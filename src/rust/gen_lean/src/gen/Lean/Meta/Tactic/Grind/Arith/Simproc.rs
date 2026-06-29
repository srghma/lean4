// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Simproc
// Imports: Init.Grind.Ring.Basic Init.Simproc Lean.Meta.Tactic.Grind.SynthInstance Init.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util Lean.Meta.LitValues Init.Grind.Ring.Field Lean.Meta.DecLevel Lean.Meta.Tactic.Grind.Arith.FieldNormNum Lean.Util.SafeExponentiation
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_zpow;
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::Grind::Ring::Field::{
    initialize_Init_Grind_Ring_Field, runtime_initialize_Init_Grind_Ring_Field,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_sort___override,
    l_Lean_Int_mkInstHAdd, l_Lean_Int_mkInstHDiv, l_Lean_Int_mkInstHMul, l_Lean_Int_mkInstHPow,
    l_Lean_Int_mkInstHSub, l_Lean_Int_mkInstMod, l_Lean_Int_mkInstNatCast, l_Lean_Int_mkInstNeg,
    l_Lean_Nat_mkInstHAdd, l_Lean_Nat_mkInstHDiv, l_Lean_Nat_mkInstHMul, l_Lean_Nat_mkInstHPow,
    l_Lean_Nat_mkInstHSub, l_Lean_Nat_mkInstMod, l_Lean_eagerReflBoolTrue, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkIntLit,
    l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkNumeral;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_checkWithKernel;
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_getDecLevel_x3f,
    runtime_initialize_Lean_Meta_DecLevel,
};
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
    l_Lean_Meta_getRatValue_x3f, runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::FieldNormNum::{
    initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum,
    l_Lean_Meta_Grind_Arith_normFieldExpr_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Util::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_Simprocs_add, l_Lean_Meta_Simp_addSEvalprocBuiltinAttr,
    l_Lean_Meta_Simp_addSimprocBuiltinAttr, l_Lean_Meta_Simp_registerBuiltinDSimproc,
    l_Lean_Meta_Simp_registerBuiltinSimproc,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprRat_mkInt;
use crate::r#gen::Lean::Util::SafeExponentiation::{
    initialize_Lean_Util_SafeExponentiation, l_Lean_checkExponent,
    runtime_initialize_Lean_Util_SafeExponentiation,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_of_nat,
};
use crate::ffi::lean_expr_eqv;
pub static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12847922472053947547 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10422657989269798688 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 111, 119, 95, 111, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        394892708320830391 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 111, 119, 95, 122, 101, 114, 111, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        6727744398392576516 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 97, 110, 100, 80, 111, 119, 48, 49, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,2706729942186767305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value) as *mut crate::leanh::LeanObject,15764114953608429200 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value) as *mut crate::leanh::LeanObject,9755723410228041222 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value) as *mut crate::leanh::LeanObject,13474504806189678690 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value) as *mut crate::leanh::LeanObject,6508593840631735363 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value) as *mut crate::leanh::LeanObject,4828225126264449809 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value) as *mut crate::leanh::LeanObject,1593258566177356093 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value) as *mut crate::leanh::LeanObject,17423969607579146442 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11858238400308895562 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6100819061652633370 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 105, 101, 108, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8615353994042975301 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        10171450186735820607 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        100, 105, 118, 95, 101, 113, 95, 109, 117, 108, 95, 105, 110, 118, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8615353994042975301 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
        9538795308046934224 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 120, 112, 97, 110, 100, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4708767832372302305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17636616155771105671 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15578568367168711682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [78, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5779414593499529281 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        7063772860359172143 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 114, 109, 70, 105, 101, 108, 100, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,8266182311865699269 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normInst___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_Arith_normInst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normInst___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_normInst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normInst___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_normInst___closed__2: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 65, 100, 100, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,15584518111807109331 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 77, 117, 108, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,13677744548222662368 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 83, 117, 98, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,11383999617417945194 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 68, 105, 118, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,5076174649581448308 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 77, 111, 100, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,13169703542747036293 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 80, 111, 119, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,15556061861495369649 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value) as *mut crate::leanh::LeanObject,6887128300681693401 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 111, 114, 109, 78, 97, 116, 79, 102, 78, 97, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,11489045652117677475 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 78, 101, 103, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,8075962225818476478 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 65, 100, 100, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,2135059512807332143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 77, 117, 108, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,4945833999404616362 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 83, 117, 98, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,8170102839800125606 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 68, 105, 118, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,7787041150290436990 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 77, 111, 100, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,11716802168203232425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 80, 111, 119, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject,13651304118362781131 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 111, 114, 109, 78, 97, 116, 67, 97, 115, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,13994695426372946926 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value) as *mut crate::leanh::LeanObject,10588691866721272861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 111, 114, 109, 73, 110, 116, 79, 102, 78, 97, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,967661541724967424 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        110, 97, 116, 67, 97, 115, 116, 95, 101, 113, 95, 111, 102, 78, 97, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10460788938683698780 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 78, 97, 116, 67, 97, 115, 116, 78, 117, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,4857848945093974811 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [73, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4977321555018234431 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        4463466624472370110 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 116, 67, 97, 115, 116, 95, 101, 113, 95, 111, 102, 78, 97, 116, 95, 111, 102, 95,
        110, 111, 110, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        14340752977193240557 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 116, 67, 97, 115, 116, 95, 101, 113, 95, 111, 102, 78, 97, 116, 95, 111, 102, 95,
        110, 111, 110, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        7756652563502799267 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 114, 109, 73, 110, 116, 67, 97, 115, 116, 78, 117, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,16019971347447751659 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [82, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3708748166848919527 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        1334142589224437282 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 115, 116, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3708748166848919527 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        16847769216878551944 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 111, 114, 109, 80, 111, 119, 82, 97, 116, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,4531007068787178776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject,8560983654376751983 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_mkSemiringThm(
    mut v_declName_2878_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2879_: *mut crate::leanh::LeanObject,
    mut v_a_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v_val_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v_val_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2923_: u8 = 0;
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_00_u03b1_2879_);
                v___x_2885_ = l_Lean_Meta_getDecLevel_x3f(
                    v_00_u03b1_2879_,
                    v_a_2880_,
                    v_a_2881_,
                    v_a_2882_,
                    v_a_2883_,
                );
                if crate::leanh::lean_obj_tag(v___x_2885_) == 0 {
                    v_a_2886_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    v_isSharedCheck_2923_ = (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                    if v_isSharedCheck_2923_ == 0 {
                        v___x_2888_ = v___x_2885_;
                        v_isShared_2889_ = v_isSharedCheck_2923_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2886_);
                        crate::leanh::lean_dec(v___x_2885_);
                        v___x_2888_ = crate::leanh::lean_box(0);
                        v_isShared_2889_ = v_isSharedCheck_2923_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03b1_2879_);
                    crate::leanh::lean_dec(v_declName_2878_);
                    v_a_2924_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    v_isSharedCheck_2931_ = (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2926_ = v___x_2885_;
                        v_isShared_2927_ = v_isSharedCheck_2931_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2924_);
                        crate::leanh::lean_dec(v___x_2885_);
                        v___x_2926_ = crate::leanh::lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2931_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2886_) == 1 {
                    crate::leanh::lean_del_object(v___x_2888_);
                    v_val_2890_ = crate::leanh::lean_ctor_get(v_a_2886_, 0);
                    crate::leanh::lean_inc(v_val_2890_);
                    crate::leanh::lean_dec_ref_known(v_a_2886_, 1);
                    v___x_2891_ = l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3;
                    v___x_2892_ = crate::leanh::lean_box(0);
                    v___x_2893_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2893_, 0, v_val_2890_);
                    crate::leanh::lean_ctor_set(v___x_2893_, 1, v___x_2892_);
                    crate::leanh::lean_inc_ref(v___x_2893_);
                    v___x_2894_ = l_Lean_mkConst(v___x_2891_, v___x_2893_);
                    crate::leanh::lean_inc_ref(v_00_u03b1_2879_);
                    v___x_2895_ = l_Lean_Expr_app___override(v___x_2894_, v_00_u03b1_2879_);
                    v___x_2896_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2895_,
                        v_a_2880_,
                        v_a_2881_,
                        v_a_2882_,
                        v_a_2883_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2896_) == 0 {
                        v_a_2897_ = crate::leanh::lean_ctor_get(v___x_2896_, 0);
                        v_isSharedCheck_2918_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2896_)) as u8;
                        if v_isSharedCheck_2918_ == 0 {
                            v___x_2899_ = v___x_2896_;
                            v_isShared_2900_ = v_isSharedCheck_2918_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2897_);
                            crate::leanh::lean_dec(v___x_2896_);
                            v___x_2899_ = crate::leanh::lean_box(0);
                            v_isShared_2900_ = v_isSharedCheck_2918_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2893_, 2);
                        crate::leanh::lean_dec_ref(v_00_u03b1_2879_);
                        crate::leanh::lean_dec(v_declName_2878_);
                        return v___x_2896_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2886_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_2879_);
                    crate::leanh::lean_dec(v_declName_2878_);
                    v___x_2919_ = crate::leanh::lean_box(0);
                    if v_isShared_2889_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2919_);
                        v___x_2921_ = v___x_2888_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
                        v___x_2921_ = v_reuseFailAlloc_2922_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2897_) == 1 {
                    v_val_2901_ = crate::leanh::lean_ctor_get(v_a_2897_, 0);
                    v_isSharedCheck_2913_ = (!crate::leanh::lean_is_exclusive(v_a_2897_)) as u8;
                    if v_isSharedCheck_2913_ == 0 {
                        v___x_2903_ = v_a_2897_;
                        v_isShared_2904_ = v_isSharedCheck_2913_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2901_);
                        crate::leanh::lean_dec(v_a_2897_);
                        v___x_2903_ = crate::leanh::lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2913_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2897_);
                    crate::leanh::lean_dec_ref_known(v___x_2893_, 2);
                    crate::leanh::lean_dec_ref(v_00_u03b1_2879_);
                    crate::leanh::lean_dec(v_declName_2878_);
                    v___x_2914_ = crate::leanh::lean_box(0);
                    if v_isShared_2900_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2899_, 0, v___x_2914_);
                        v___x_2916_ = v___x_2899_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
                        v___x_2916_ = v_reuseFailAlloc_2917_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2905_ = l_Lean_mkConst(v_declName_2878_, v___x_2893_);
                v___x_2906_ = l_Lean_mkAppB(v___x_2905_, v_00_u03b1_2879_, v_val_2901_);
                if v_isShared_2904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2906_);
                    v___x_2908_ = v___x_2903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2906_);
                    v___x_2908_ = v_reuseFailAlloc_2912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2899_, 0, v___x_2908_);
                    v___x_2910_ = v___x_2899_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2910_;
            }
            6 => {
                return v___x_2916_;
            }
            7 => {
                return v___x_2921_;
            }
            8 => {
                if v_isShared_2927_ == 0 {
                    v___x_2929_ = v___x_2926_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_mkSemiringThm___boxed(
    mut v_declName_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut crate::leanh::LeanObject,
    mut v_a_2934_: *mut crate::leanh::LeanObject,
    mut v_a_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(
        v_declName_2932_,
        v_00_u03b1_2933_,
        v_a_2934_,
        v_a_2935_,
        v_a_2936_,
        v_a_2937_,
    );
    crate::leanh::lean_dec(v_a_2937_);
    crate::leanh::lean_dec_ref(v_a_2936_);
    crate::leanh::lean_dec(v_a_2935_);
    crate::leanh::lean_dec_ref(v_a_2934_);
    return v_res_2939_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandPow01___redArg(
    mut v_e_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v_arg_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v_arg_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v_arg_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v_arg_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_arg_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v_val_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v_val_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3064_: u8 = 0;
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v_a_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3078_: u8 = 0;
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v_val_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_a_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_a_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3148_: u8 = 0;
    let mut v_a_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_a_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3161_: u8 = 0;
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2971_ = l_Lean_Expr_cleanupAnnotations(v_e_2962_);
                v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
                if v___x_2972_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2971_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2973_ = crate::leanh::lean_ctor_get(v___x_2971_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2973_);
                    v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
                    v___x_2975_ = l_Lean_Expr_isApp(v___x_2974_);
                    if v___x_2975_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2974_);
                        crate::leanh::lean_dec_ref(v_arg_2973_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2976_ = crate::leanh::lean_ctor_get(v___x_2974_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2976_);
                        v___x_2977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2974_);
                        v___x_2978_ = l_Lean_Expr_isApp(v___x_2977_);
                        if v___x_2978_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2977_);
                            crate::leanh::lean_dec_ref(v_arg_2976_);
                            crate::leanh::lean_dec_ref(v_arg_2973_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
                            v___x_2980_ = l_Lean_Expr_isApp(v___x_2979_);
                            if v___x_2980_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2979_);
                                crate::leanh::lean_dec_ref(v_arg_2976_);
                                crate::leanh::lean_dec_ref(v_arg_2973_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2981_ = crate::leanh::lean_ctor_get(v___x_2979_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2981_);
                                v___x_2982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2979_);
                                v___x_2983_ = l_Lean_Expr_isApp(v___x_2982_);
                                if v___x_2983_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2982_);
                                    crate::leanh::lean_dec_ref(v_arg_2981_);
                                    crate::leanh::lean_dec_ref(v_arg_2976_);
                                    crate::leanh::lean_dec_ref(v_arg_2973_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2984_ = crate::leanh::lean_ctor_get(v___x_2982_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2984_);
                                    v___x_2985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2982_);
                                    v___x_2986_ = l_Lean_Expr_isApp(v___x_2985_);
                                    if v___x_2986_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2985_);
                                        crate::leanh::lean_dec_ref(v_arg_2984_);
                                        crate::leanh::lean_dec_ref(v_arg_2981_);
                                        crate::leanh::lean_dec_ref(v_arg_2976_);
                                        crate::leanh::lean_dec_ref(v_arg_2973_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2987_ = crate::leanh::lean_ctor_get(v___x_2985_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_2987_);
                                        v___x_2988_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2985_);
                                        v___x_2989_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3;
                                        v___x_2990_ =
                                            l_Lean_Expr_isConstOf(v___x_2988_, v___x_2989_);
                                        crate::leanh::lean_dec_ref(v___x_2988_);
                                        if v___x_2990_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_2987_);
                                            crate::leanh::lean_dec_ref(v_arg_2984_);
                                            crate::leanh::lean_dec_ref(v_arg_2981_);
                                            crate::leanh::lean_dec_ref(v_arg_2976_);
                                            crate::leanh::lean_dec_ref(v_arg_2973_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_2991_ =
                                                l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                    v_arg_2984_,
                                                    v_a_2964_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_2991_) == 0 {
                                                v_a_2992_ =
                                                    crate::leanh::lean_ctor_get(v___x_2991_, 0);
                                                v_isSharedCheck_3157_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2991_))
                                                        as u8;
                                                if v_isSharedCheck_3157_ == 0 {
                                                    v___x_2994_ = v___x_2991_;
                                                    v_isShared_2995_ = v_isSharedCheck_3157_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2992_);
                                                    crate::leanh::lean_dec(v___x_2991_);
                                                    v___x_2994_ = crate::leanh::lean_box(0);
                                                    v_isShared_2995_ = v_isSharedCheck_3157_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_2987_);
                                                crate::leanh::lean_dec_ref(v_arg_2981_);
                                                crate::leanh::lean_dec_ref(v_arg_2976_);
                                                crate::leanh::lean_dec_ref(v_arg_2973_);
                                                v_a_3158_ =
                                                    crate::leanh::lean_ctor_get(v___x_2991_, 0);
                                                v_isSharedCheck_3165_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2991_))
                                                        as u8;
                                                if v_isSharedCheck_3165_ == 0 {
                                                    v___x_3160_ = v___x_2991_;
                                                    v_isShared_3161_ = v_isSharedCheck_3165_;
                                                    state = 37;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3158_);
                                                    crate::leanh::lean_dec(v___x_2991_);
                                                    v___x_3160_ = crate::leanh::lean_box(0);
                                                    v_isShared_3161_ = v_isSharedCheck_3165_;
                                                    state = 37;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2969_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                v___x_2970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2970_, 0, v___x_2969_);
                return v___x_2970_;
            }
            2 => {
                v___x_2996_ = l_Lean_Expr_cleanupAnnotations(v_a_2992_);
                v___x_2997_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5;
                v___x_2998_ = l_Lean_Expr_isConstOf(v___x_2996_, v___x_2997_);
                crate::leanh::lean_dec_ref(v___x_2996_);
                if v___x_2998_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2987_);
                    crate::leanh::lean_dec_ref(v_arg_2981_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    crate::leanh::lean_dec_ref(v_arg_2973_);
                    v___x_2999_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_2995_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2994_, 0, v___x_2999_);
                        v___x_3001_ = v___x_2994_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
                        v___x_3001_ = v_reuseFailAlloc_3002_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2994_);
                    v___x_3003_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_2973_,
                        v_a_2963_,
                        v_a_2964_,
                        v_a_2965_,
                        v_a_2966_,
                    );
                    crate::leanh::lean_dec_ref(v_arg_2973_);
                    if crate::leanh::lean_obj_tag(v___x_3003_) == 0 {
                        v_a_3004_ = crate::leanh::lean_ctor_get(v___x_3003_, 0);
                        v_isSharedCheck_3148_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3003_)) as u8;
                        if v_isSharedCheck_3148_ == 0 {
                            v___x_3006_ = v___x_3003_;
                            v_isShared_3007_ = v_isSharedCheck_3148_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3004_);
                            crate::leanh::lean_dec(v___x_3003_);
                            v___x_3006_ = crate::leanh::lean_box(0);
                            v_isShared_3007_ = v_isSharedCheck_3148_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2987_);
                        crate::leanh::lean_dec_ref(v_arg_2981_);
                        crate::leanh::lean_dec_ref(v_arg_2976_);
                        v_a_3149_ = crate::leanh::lean_ctor_get(v___x_3003_, 0);
                        v_isSharedCheck_3156_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3003_)) as u8;
                        if v_isSharedCheck_3156_ == 0 {
                            v___x_3151_ = v___x_3003_;
                            v_isShared_3152_ = v_isSharedCheck_3156_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3149_);
                            crate::leanh::lean_dec(v___x_3003_);
                            v___x_3151_ = crate::leanh::lean_box(0);
                            v_isShared_3152_ = v_isSharedCheck_3156_;
                            state = 35;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3001_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3004_) == 1 {
                    v_val_3008_ = crate::leanh::lean_ctor_get(v_a_3004_, 0);
                    v_isSharedCheck_3143_ = (!crate::leanh::lean_is_exclusive(v_a_3004_)) as u8;
                    if v_isSharedCheck_3143_ == 0 {
                        v___x_3010_ = v_a_3004_;
                        v_isShared_3011_ = v_isSharedCheck_3143_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3008_);
                        crate::leanh::lean_dec(v_a_3004_);
                        v___x_3010_ = crate::leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3143_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3004_);
                    crate::leanh::lean_dec_ref(v_arg_2987_);
                    crate::leanh::lean_dec_ref(v_arg_2981_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v___x_3144_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3007_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3006_, 0, v___x_3144_);
                        v___x_3146_ = v___x_3006_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_3147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
                        v___x_3146_ = v_reuseFailAlloc_3147_;
                        state = 34;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3012_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3013_ = lean_nat_dec_eq(v_val_3008_, v___x_3012_);
                if v___x_3013_ == 0 {
                    v___x_3014_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3015_ = lean_nat_dec_eq(v_val_3008_, v___x_3014_);
                    crate::leanh::lean_dec(v_val_3008_);
                    if v___x_3015_ == 0 {
                        crate::leanh::lean_del_object(v___x_3010_);
                        crate::leanh::lean_dec_ref(v_arg_2987_);
                        crate::leanh::lean_dec_ref(v_arg_2981_);
                        crate::leanh::lean_dec_ref(v_arg_2976_);
                        v___x_3016_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                        if v_isShared_3007_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3006_, 0, v___x_3016_);
                            v___x_3018_ = v___x_3006_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3019_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
                            v___x_3018_ = v_reuseFailAlloc_3019_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3006_);
                        crate::leanh::lean_inc_ref(v_arg_2987_);
                        v___x_3020_ = l_Lean_Meta_isExprDefEq(
                            v_arg_2987_,
                            v_arg_2981_,
                            v_a_2963_,
                            v_a_2964_,
                            v_a_2965_,
                            v_a_2966_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3020_) == 0 {
                            v_a_3021_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3065_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3065_ == 0 {
                                v___x_3023_ = v___x_3020_;
                                v_isShared_3024_ = v_isSharedCheck_3065_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3021_);
                                crate::leanh::lean_dec(v___x_3020_);
                                v___x_3023_ = crate::leanh::lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3065_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3010_);
                            crate::leanh::lean_dec_ref(v_arg_2987_);
                            crate::leanh::lean_dec_ref(v_arg_2976_);
                            v_a_3066_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3073_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3073_ == 0 {
                                v___x_3068_ = v___x_3020_;
                                v_isShared_3069_ = v_isSharedCheck_3073_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3066_);
                                crate::leanh::lean_dec(v___x_3020_);
                                v___x_3068_ = crate::leanh::lean_box(0);
                                v_isShared_3069_ = v_isSharedCheck_3073_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_3008_);
                    crate::leanh::lean_del_object(v___x_3006_);
                    crate::leanh::lean_inc_ref(v_arg_2987_);
                    v___x_3074_ = l_Lean_Meta_isExprDefEq(
                        v_arg_2987_,
                        v_arg_2981_,
                        v_a_2963_,
                        v_a_2964_,
                        v_a_2965_,
                        v_a_2966_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3074_) == 0 {
                        v_a_3075_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
                        v_isSharedCheck_3134_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3074_)) as u8;
                        if v_isSharedCheck_3134_ == 0 {
                            v___x_3077_ = v___x_3074_;
                            v_isShared_3078_ = v_isSharedCheck_3134_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3075_);
                            crate::leanh::lean_dec(v___x_3074_);
                            v___x_3077_ = crate::leanh::lean_box(0);
                            v_isShared_3078_ = v_isSharedCheck_3134_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3010_);
                        crate::leanh::lean_dec_ref(v_arg_2987_);
                        crate::leanh::lean_dec_ref(v_arg_2976_);
                        v_a_3135_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
                        v_isSharedCheck_3142_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3074_)) as u8;
                        if v_isSharedCheck_3142_ == 0 {
                            v___x_3137_ = v___x_3074_;
                            v_isShared_3138_ = v_isSharedCheck_3142_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3135_);
                            crate::leanh::lean_dec(v___x_3074_);
                            v___x_3137_ = crate::leanh::lean_box(0);
                            v_isShared_3138_ = v_isSharedCheck_3142_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_3018_;
            }
            7 => {
                v___x_3025_ = (crate::leanh::lean_unbox(v_a_3021_) as u8);
                crate::leanh::lean_dec(v_a_3021_);
                if v___x_3025_ == 0 {
                    crate::leanh::lean_del_object(v___x_3010_);
                    crate::leanh::lean_dec_ref(v_arg_2987_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v___x_3026_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3024_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3023_, 0, v___x_3026_);
                        v___x_3028_ = v___x_3023_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
                        v___x_3028_ = v_reuseFailAlloc_3029_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3023_);
                    v___x_3030_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7;
                    v___x_3031_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(
                        v___x_3030_,
                        v_arg_2987_,
                        v_a_2963_,
                        v_a_2964_,
                        v_a_2965_,
                        v_a_2966_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3031_) == 0 {
                        v_a_3032_ = crate::leanh::lean_ctor_get(v___x_3031_, 0);
                        v_isSharedCheck_3056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3031_)) as u8;
                        if v_isSharedCheck_3056_ == 0 {
                            v___x_3034_ = v___x_3031_;
                            v_isShared_3035_ = v_isSharedCheck_3056_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3032_);
                            crate::leanh::lean_dec(v___x_3031_);
                            v___x_3034_ = crate::leanh::lean_box(0);
                            v_isShared_3035_ = v_isSharedCheck_3056_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3010_);
                        crate::leanh::lean_dec_ref(v_arg_2976_);
                        v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3031_, 0);
                        v_isSharedCheck_3064_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3031_)) as u8;
                        if v_isSharedCheck_3064_ == 0 {
                            v___x_3059_ = v___x_3031_;
                            v_isShared_3060_ = v_isSharedCheck_3064_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3057_);
                            crate::leanh::lean_dec(v___x_3031_);
                            v___x_3059_ = crate::leanh::lean_box(0);
                            v_isShared_3060_ = v_isSharedCheck_3064_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            8 => {
                return v___x_3028_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_3032_) == 1 {
                    v_val_3036_ = crate::leanh::lean_ctor_get(v_a_3032_, 0);
                    v_isSharedCheck_3051_ = (!crate::leanh::lean_is_exclusive(v_a_3032_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v___x_3038_ = v_a_3032_;
                        v_isShared_3039_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3036_);
                        crate::leanh::lean_dec(v_a_3032_);
                        v___x_3038_ = crate::leanh::lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3032_);
                    crate::leanh::lean_del_object(v___x_3010_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v___x_3052_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3052_);
                        v___x_3054_ = v___x_3034_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
                        v___x_3054_ = v_reuseFailAlloc_3055_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                crate::leanh::lean_inc_ref(v_arg_2976_);
                v___x_3040_ = l_Lean_Expr_app___override(v_val_3036_, v_arg_2976_);
                if v_isShared_3039_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3038_, 0, v___x_3040_);
                    v___x_3042_ = v___x_3038_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3040_);
                    v___x_3042_ = v_reuseFailAlloc_3050_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3043_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3043_, 0, v_arg_2976_);
                crate::leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3043_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2998_,
                );
                if v_isShared_3011_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3010_, 0);
                    crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3043_);
                    v___x_3045_ = v___x_3010_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3043_);
                    v___x_3045_ = v_reuseFailAlloc_3049_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3045_);
                    v___x_3047_ = v___x_3034_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
                    v___x_3047_ = v_reuseFailAlloc_3048_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3047_;
            }
            14 => {
                return v___x_3054_;
            }
            15 => {
                if v_isShared_3060_ == 0 {
                    v___x_3062_ = v___x_3059_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
                    v___x_3062_ = v_reuseFailAlloc_3063_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3062_;
            }
            17 => {
                if v_isShared_3069_ == 0 {
                    v___x_3071_ = v___x_3068_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
                    v___x_3071_ = v_reuseFailAlloc_3072_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3071_;
            }
            19 => {
                v___x_3079_ = (crate::leanh::lean_unbox(v_a_3075_) as u8);
                crate::leanh::lean_dec(v_a_3075_);
                if v___x_3079_ == 0 {
                    crate::leanh::lean_del_object(v___x_3010_);
                    crate::leanh::lean_dec_ref(v_arg_2987_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v___x_3080_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3078_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3077_, 0, v___x_3080_);
                        v___x_3082_ = v___x_3077_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
                        v___x_3082_ = v_reuseFailAlloc_3083_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3077_);
                    v___x_3084_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9;
                    crate::leanh::lean_inc_ref(v_arg_2987_);
                    v___x_3085_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(
                        v___x_3084_,
                        v_arg_2987_,
                        v_a_2963_,
                        v_a_2964_,
                        v_a_2965_,
                        v_a_2966_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3085_) == 0 {
                        v_a_3086_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                        v_isSharedCheck_3125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3085_)) as u8;
                        if v_isSharedCheck_3125_ == 0 {
                            v___x_3088_ = v___x_3085_;
                            v_isShared_3089_ = v_isSharedCheck_3125_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3086_);
                            crate::leanh::lean_dec(v___x_3085_);
                            v___x_3088_ = crate::leanh::lean_box(0);
                            v_isShared_3089_ = v_isSharedCheck_3125_;
                            state = 21;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3010_);
                        crate::leanh::lean_dec_ref(v_arg_2987_);
                        crate::leanh::lean_dec_ref(v_arg_2976_);
                        v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                        v_isSharedCheck_3133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3085_)) as u8;
                        if v_isSharedCheck_3133_ == 0 {
                            v___x_3128_ = v___x_3085_;
                            v_isShared_3129_ = v_isSharedCheck_3133_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3126_);
                            crate::leanh::lean_dec(v___x_3085_);
                            v___x_3128_ = crate::leanh::lean_box(0);
                            v_isShared_3129_ = v_isSharedCheck_3133_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            20 => {
                return v___x_3082_;
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_a_3086_) == 1 {
                    crate::leanh::lean_del_object(v___x_3088_);
                    v_val_3090_ = crate::leanh::lean_ctor_get(v_a_3086_, 0);
                    v_isSharedCheck_3120_ = (!crate::leanh::lean_is_exclusive(v_a_3086_)) as u8;
                    if v_isSharedCheck_3120_ == 0 {
                        v___x_3092_ = v_a_3086_;
                        v_isShared_3093_ = v_isSharedCheck_3120_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3090_);
                        crate::leanh::lean_dec(v_a_3086_);
                        v___x_3092_ = crate::leanh::lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3120_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3086_);
                    crate::leanh::lean_del_object(v___x_3010_);
                    crate::leanh::lean_dec_ref(v_arg_2987_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v___x_3121_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3089_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3088_, 0, v___x_3121_);
                        v___x_3123_ = v___x_3088_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
                        v___x_3123_ = v_reuseFailAlloc_3124_;
                        state = 29;
                        continue;
                    }
                }
            }
            22 => {
                v___x_3094_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3095_ = l_Lean_Meta_mkNumeral(
                    v_arg_2987_,
                    v___x_3094_,
                    v_a_2963_,
                    v_a_2964_,
                    v_a_2965_,
                    v_a_2966_,
                );
                if crate::leanh::lean_obj_tag(v___x_3095_) == 0 {
                    v_a_3096_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                    v_isSharedCheck_3111_ = (!crate::leanh::lean_is_exclusive(v___x_3095_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v___x_3098_ = v___x_3095_;
                        v_isShared_3099_ = v_isSharedCheck_3111_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3096_);
                        crate::leanh::lean_dec(v___x_3095_);
                        v___x_3098_ = crate::leanh::lean_box(0);
                        v_isShared_3099_ = v_isSharedCheck_3111_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3092_);
                    crate::leanh::lean_dec(v_val_3090_);
                    crate::leanh::lean_del_object(v___x_3010_);
                    crate::leanh::lean_dec_ref(v_arg_2976_);
                    v_a_3112_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                    v_isSharedCheck_3119_ = (!crate::leanh::lean_is_exclusive(v___x_3095_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3114_ = v___x_3095_;
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3112_);
                        crate::leanh::lean_dec(v___x_3095_);
                        v___x_3114_ = crate::leanh::lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 27;
                        continue;
                    }
                }
            }
            23 => {
                v___x_3100_ = l_Lean_Expr_app___override(v_val_3090_, v_arg_2976_);
                if v_isShared_3093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3092_, 0, v___x_3100_);
                    v___x_3102_ = v___x_3092_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3100_);
                    v___x_3102_ = v_reuseFailAlloc_3110_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3103_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3103_, 0, v_a_3096_);
                crate::leanh::lean_ctor_set(v___x_3103_, 1, v___x_3102_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2998_,
                );
                if v_isShared_3011_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3010_, 0);
                    crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3103_);
                    v___x_3105_ = v___x_3010_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3103_);
                    v___x_3105_ = v_reuseFailAlloc_3109_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3098_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3098_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3107_;
            }
            27 => {
                if v_isShared_3115_ == 0 {
                    v___x_3117_ = v___x_3114_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3117_;
            }
            29 => {
                return v___x_3123_;
            }
            30 => {
                if v_isShared_3129_ == 0 {
                    v___x_3131_ = v___x_3128_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
                    v___x_3131_ = v_reuseFailAlloc_3132_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3131_;
            }
            32 => {
                if v_isShared_3138_ == 0 {
                    v___x_3140_ = v___x_3137_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3140_;
            }
            34 => {
                return v___x_3146_;
            }
            35 => {
                if v_isShared_3152_ == 0 {
                    v___x_3154_ = v___x_3151_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3155_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3154_;
            }
            37 => {
                if v_isShared_3161_ == 0 {
                    v___x_3163_ = v___x_3160_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandPow01___redArg___boxed(
    mut v_e_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3172_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg(
        v_e_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_,
    );
    crate::leanh::lean_dec(v_a_3170_);
    crate::leanh::lean_dec_ref(v_a_3169_);
    crate::leanh::lean_dec(v_a_3168_);
    crate::leanh::lean_dec_ref(v_a_3167_);
    return v_res_3172_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandPow01(
    mut v_e_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
    mut v_a_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg(
        v_e_3173_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_,
    );
    return v___x_3182_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandPow01___boxed(
    mut v_e_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
    mut v_a_3187_: *mut crate::leanh::LeanObject,
    mut v_a_3188_: *mut crate::leanh::LeanObject,
    mut v_a_3189_: *mut crate::leanh::LeanObject,
    mut v_a_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3192_ = l_Lean_Meta_Grind_Arith_expandPow01(
        v_e_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_,
    );
    crate::leanh::lean_dec(v_a_3190_);
    crate::leanh::lean_dec_ref(v_a_3189_);
    crate::leanh::lean_dec(v_a_3188_);
    crate::leanh::lean_dec_ref(v_a_3187_);
    crate::leanh::lean_dec(v_a_3186_);
    crate::leanh::lean_dec_ref(v_a_3185_);
    crate::leanh::lean_dec(v_a_3184_);
    return v_res_3192_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_;
    v___x_3218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_;
    v___x_3219_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_expandPow01___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3220_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3217_, v___x_3218_, v___x_3219_);
    return v___x_3220_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13____boxed(
    mut v_a_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_();
    return v_res_3222_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u64 = 0;
    v___x_3223_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3224_ = lean_uint64_of_nat(v___x_3223_);
    return v___x_3224_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_3225_: *mut crate::leanh::LeanObject,
    mut v_x_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: u64 = 0;
    let mut v___x_3236_: u64 = 0;
    let mut v___x_3237_: u64 = 0;
    let mut v_fold_3238_: u64 = 0;
    let mut v___x_3239_: u64 = 0;
    let mut v___x_3240_: u64 = 0;
    let mut v___x_3241_: u64 = 0;
    let mut v___x_3242_: usize = 0;
    let mut v___x_3243_: usize = 0;
    let mut v___x_3244_: usize = 0;
    let mut v___x_3245_: usize = 0;
    let mut v___x_3246_: usize = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u64 = 0;
    let mut v_hash_3254_: u64 = 0;
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3226_) == 0 {
                    return v_x_3225_;
                } else {
                    v_key_3227_ = crate::leanh::lean_ctor_get(v_x_3226_, 0);
                    v_value_3228_ = crate::leanh::lean_ctor_get(v_x_3226_, 1);
                    v_tail_3229_ = crate::leanh::lean_ctor_get(v_x_3226_, 2);
                    v_isSharedCheck_3255_ = (!crate::leanh::lean_is_exclusive(v_x_3226_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3231_ = v_x_3226_;
                        v_isShared_3232_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3229_);
                        crate::leanh::lean_inc(v_value_3228_);
                        crate::leanh::lean_inc(v_key_3227_);
                        crate::leanh::lean_dec(v_x_3226_);
                        v___x_3231_ = crate::leanh::lean_box(0);
                        v_isShared_3232_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3233_ = lean_array_get_size(v_x_3225_);
                if crate::leanh::lean_obj_tag(v_key_3227_) == 0 {
                    v___x_3253_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_3235_ = v___x_3253_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3254_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_3227_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3235_ = v_hash_3254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3236_ = 32u64;
                v___x_3237_ = lean_uint64_shift_right(v___y_3235_, v___x_3236_);
                v_fold_3238_ = lean_uint64_xor(v___y_3235_, v___x_3237_);
                v___x_3239_ = 16u64;
                v___x_3240_ = lean_uint64_shift_right(v_fold_3238_, v___x_3239_);
                v___x_3241_ = lean_uint64_xor(v_fold_3238_, v___x_3240_);
                v___x_3242_ = lean_uint64_to_usize(v___x_3241_);
                v___x_3243_ = lean_usize_of_nat(v___x_3233_);
                v___x_3244_ = 1usize;
                v___x_3245_ = lean_usize_sub(v___x_3243_, v___x_3244_);
                v___x_3246_ = lean_usize_land(v___x_3242_, v___x_3245_);
                v___x_3247_ = lean_array_uget_borrowed(v_x_3225_, v___x_3246_);
                crate::leanh::lean_inc(v___x_3247_);
                if v_isShared_3232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3231_, 2, v___x_3247_);
                    v___x_3249_ = v___x_3231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_key_3227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_value_3228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 2, v___x_3247_);
                    v___x_3249_ = v_reuseFailAlloc_3252_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3250_ = lean_array_uset(v_x_3225_, v___x_3246_, v___x_3249_);
                v_x_3225_ = v___x_3250_;
                v_x_3226_ = v_tail_3229_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(
    mut v_i_3256_: *mut crate::leanh::LeanObject,
    mut v_source_3257_: *mut crate::leanh::LeanObject,
    mut v_target_3258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v_es_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3259_ = lean_array_get_size(v_source_3257_);
                v___x_3260_ = lean_nat_dec_lt(v_i_3256_, v___x_3259_);
                if v___x_3260_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3257_);
                    crate::leanh::lean_dec(v_i_3256_);
                    return v_target_3258_;
                } else {
                    v_es_3261_ = lean_array_fget(v_source_3257_, v_i_3256_);
                    v___x_3262_ = crate::leanh::lean_box(0);
                    v_source_3263_ = lean_array_fset(v_source_3257_, v_i_3256_, v___x_3262_);
                    v_target_3264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_target_3258_, v_es_3261_);
                    v___x_3265_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3266_ = lean_nat_add(v_i_3256_, v___x_3265_);
                    crate::leanh::lean_dec(v_i_3256_);
                    v_i_3256_ = v___x_3266_;
                    v_source_3257_ = v_source_3263_;
                    v_target_3258_ = v_target_3264_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(
    mut v_data_3268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3269_ = lean_array_get_size(v_data_3268_);
    v___x_3270_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3271_ = lean_nat_mul(v___x_3269_, v___x_3270_);
    v___x_3272_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3273_ = crate::leanh::lean_box(0);
    v___x_3274_ = lean_mk_array(v_nbuckets_3271_, v___x_3273_);
    v___x_3275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v___x_3272_, v_data_3268_, v___x_3274_);
    return v___x_3275_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_x_3277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3278_: u8 = 0;
    let mut v_key_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3277_) == 0 {
                    v___x_3278_ = 0;
                    return v___x_3278_;
                } else {
                    v_key_3279_ = crate::leanh::lean_ctor_get(v_x_3277_, 0);
                    v_tail_3280_ = crate::leanh::lean_ctor_get(v_x_3277_, 2);
                    v___x_3281_ = lean_name_eq(v_key_3279_, v_a_3276_);
                    if v___x_3281_ == 0 {
                        v_x_3277_ = v_tail_3280_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3281_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg___boxed(
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_x_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3285_: u8 = 0;
    let mut v_r_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_3283_, v_x_3284_);
    crate::leanh::lean_dec(v_x_3284_);
    crate::leanh::lean_dec(v_a_3283_);
    v_r_3286_ = crate::leanh::lean_box((v_res_3285_) as usize);
    return v_r_3286_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(
    mut v_m_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_b_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3294_: u64 = 0;
    let mut v___x_3295_: u64 = 0;
    let mut v___x_3296_: u64 = 0;
    let mut v_fold_3297_: u64 = 0;
    let mut v___x_3298_: u64 = 0;
    let mut v___x_3299_: u64 = 0;
    let mut v___x_3300_: u64 = 0;
    let mut v___x_3301_: usize = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: usize = 0;
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: usize = 0;
    let mut v_bkt_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v_val_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: u64 = 0;
    let mut v_hash_3332_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3290_ = crate::leanh::lean_ctor_get(v_m_3287_, 0);
                v_buckets_3291_ = crate::leanh::lean_ctor_get(v_m_3287_, 1);
                v___x_3292_ = lean_array_get_size(v_buckets_3291_);
                if crate::leanh::lean_obj_tag(v_a_3288_) == 0 {
                    v___x_3331_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_3294_ = v___x_3331_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3332_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3288_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3294_ = v_hash_3332_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3295_ = 32u64;
                v___x_3296_ = lean_uint64_shift_right(v___y_3294_, v___x_3295_);
                v_fold_3297_ = lean_uint64_xor(v___y_3294_, v___x_3296_);
                v___x_3298_ = 16u64;
                v___x_3299_ = lean_uint64_shift_right(v_fold_3297_, v___x_3298_);
                v___x_3300_ = lean_uint64_xor(v_fold_3297_, v___x_3299_);
                v___x_3301_ = lean_uint64_to_usize(v___x_3300_);
                v___x_3302_ = lean_usize_of_nat(v___x_3292_);
                v___x_3303_ = 1usize;
                v___x_3304_ = lean_usize_sub(v___x_3302_, v___x_3303_);
                v___x_3305_ = lean_usize_land(v___x_3301_, v___x_3304_);
                v_bkt_3306_ = lean_array_uget_borrowed(v_buckets_3291_, v___x_3305_);
                v___x_3307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_3288_, v_bkt_3306_);
                if v___x_3307_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3291_);
                    crate::leanh::lean_inc(v_size_3290_);
                    v_isSharedCheck_3328_ = (!crate::leanh::lean_is_exclusive(v_m_3287_)) as u8;
                    if v_isSharedCheck_3328_ == 0 {
                        v_unused_3329_ = crate::leanh::lean_ctor_get(v_m_3287_, 1);
                        crate::leanh::lean_dec(v_unused_3329_);
                        v_unused_3330_ = crate::leanh::lean_ctor_get(v_m_3287_, 0);
                        crate::leanh::lean_dec(v_unused_3330_);
                        v___x_3309_ = v_m_3287_;
                        v_isShared_3310_ = v_isSharedCheck_3328_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3287_);
                        v___x_3309_ = crate::leanh::lean_box(0);
                        v_isShared_3310_ = v_isSharedCheck_3328_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3289_);
                    crate::leanh::lean_dec(v_a_3288_);
                    return v_m_3287_;
                }
            }
            2 => {
                v___x_3311_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3312_ = lean_nat_add(v_size_3290_, v___x_3311_);
                crate::leanh::lean_dec(v_size_3290_);
                crate::leanh::lean_inc(v_bkt_3306_);
                v___x_3313_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3313_, 0, v_a_3288_);
                crate::leanh::lean_ctor_set(v___x_3313_, 1, v_b_3289_);
                crate::leanh::lean_ctor_set(v___x_3313_, 2, v_bkt_3306_);
                v_buckets_x27_3314_ = lean_array_uset(v_buckets_3291_, v___x_3305_, v___x_3313_);
                v___x_3315_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3316_ = lean_nat_mul(v_size_x27_3312_, v___x_3315_);
                v___x_3317_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3318_ = lean_nat_div(v___x_3316_, v___x_3317_);
                crate::leanh::lean_dec(v___x_3316_);
                v___x_3319_ = lean_array_get_size(v_buckets_x27_3314_);
                v___x_3320_ = lean_nat_dec_le(v___x_3318_, v___x_3319_);
                crate::leanh::lean_dec(v___x_3318_);
                if v___x_3320_ == 0 {
                    v_val_3321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_buckets_x27_3314_);
                    if v_isShared_3310_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3309_, 1, v_val_3321_);
                        crate::leanh::lean_ctor_set(v___x_3309_, 0, v_size_x27_3312_);
                        v___x_3323_ = v___x_3309_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_size_x27_3312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_val_3321_);
                        v___x_3323_ = v_reuseFailAlloc_3324_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3310_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3309_, 1, v_buckets_x27_3314_);
                        crate::leanh::lean_ctor_set(v___x_3309_, 0, v_size_x27_3312_);
                        v___x_3326_ = v___x_3309_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_size_x27_3312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_buckets_x27_3314_);
                        v___x_3326_ = v_reuseFailAlloc_3327_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3323_;
            }
            4 => {
                return v___x_3326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(
    mut v_x_3333_: *mut crate::leanh::LeanObject,
    mut v_x_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3334_) == 0 {
                    return v_x_3333_;
                } else {
                    v_head_3335_ = crate::leanh::lean_ctor_get(v_x_3334_, 0);
                    crate::leanh::lean_inc(v_head_3335_);
                    v_tail_3336_ = crate::leanh::lean_ctor_get(v_x_3334_, 1);
                    crate::leanh::lean_inc(v_tail_3336_);
                    crate::leanh::lean_dec_ref_known(v_x_3334_, 2);
                    v___x_3337_ = crate::leanh::lean_box(0);
                    v___x_3338_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_x_3333_, v_head_3335_, v___x_3337_);
                    v_x_3333_ = v___x_3338_;
                    v_x_3334_ = v_tail_3336_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3340_ = crate::leanh::lean_box(0);
    v___x_3341_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3342_ = lean_mk_array(v___x_3341_, v___x_3340_);
    return v___x_3342_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3343_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0);
    v___x_3344_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3345_, 0, v___x_3344_);
    crate::leanh::lean_ctor_set(v___x_3345_, 1, v___x_3343_);
    return v___x_3345_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3406_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30;
    v___x_3407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1);
    v___x_3408_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(v___x_3407_, v___x_3406_);
    return v___x_3408_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31);
    return v___x_3409_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0(
    mut v_00_u03b2_3410_: *mut crate::leanh::LeanObject,
    mut v_m_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_b_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_m_3411_, v_a_3412_, v_b_3413_);
    return v___x_3414_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(
    mut v_00_u03b2_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_x_3417_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3418_: u8 = 0;
    v___x_3418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_3416_, v_x_3417_);
    return v___x_3418_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___boxed(
    mut v_00_u03b2_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_x_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: u8 = 0;
    let mut v_r_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(v_00_u03b2_3419_, v_a_3420_, v_x_3421_);
    crate::leanh::lean_dec(v_x_3421_);
    crate::leanh::lean_dec(v_a_3420_);
    v_r_3423_ = crate::leanh::lean_box((v_res_3422_) as usize);
    return v_r_3423_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1(
    mut v_00_u03b2_3424_: *mut crate::leanh::LeanObject,
    mut v_data_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_data_3425_);
    return v___x_3426_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3427_: *mut crate::leanh::LeanObject,
    mut v_i_3428_: *mut crate::leanh::LeanObject,
    mut v_source_3429_: *mut crate::leanh::LeanObject,
    mut v_target_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v_i_3428_, v_source_3429_, v_target_3430_);
    return v___x_3431_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3432_: *mut crate::leanh::LeanObject,
    mut v_x_3433_: *mut crate::leanh::LeanObject,
    mut v_x_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_x_3433_, v_x_3434_);
    return v___x_3435_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(
    mut v_m_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: u64 = 0;
    let mut v___x_3442_: u64 = 0;
    let mut v___x_3443_: u64 = 0;
    let mut v_fold_3444_: u64 = 0;
    let mut v___x_3445_: u64 = 0;
    let mut v___x_3446_: u64 = 0;
    let mut v___x_3447_: u64 = 0;
    let mut v___x_3448_: usize = 0;
    let mut v___x_3449_: usize = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: usize = 0;
    let mut v___x_3452_: usize = 0;
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: u64 = 0;
    let mut v_hash_3456_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3438_ = crate::leanh::lean_ctor_get(v_m_3436_, 1);
                v___x_3439_ = lean_array_get_size(v_buckets_3438_);
                if crate::leanh::lean_obj_tag(v_a_3437_) == 0 {
                    v___x_3455_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_3441_ = v___x_3455_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3456_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3437_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3441_ = v_hash_3456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3442_ = 32u64;
                v___x_3443_ = lean_uint64_shift_right(v___y_3441_, v___x_3442_);
                v_fold_3444_ = lean_uint64_xor(v___y_3441_, v___x_3443_);
                v___x_3445_ = 16u64;
                v___x_3446_ = lean_uint64_shift_right(v_fold_3444_, v___x_3445_);
                v___x_3447_ = lean_uint64_xor(v_fold_3444_, v___x_3446_);
                v___x_3448_ = lean_uint64_to_usize(v___x_3447_);
                v___x_3449_ = lean_usize_of_nat(v___x_3439_);
                v___x_3450_ = 1usize;
                v___x_3451_ = lean_usize_sub(v___x_3449_, v___x_3450_);
                v___x_3452_ = lean_usize_land(v___x_3448_, v___x_3451_);
                v___x_3453_ = lean_array_uget_borrowed(v_buckets_3438_, v___x_3452_);
                v___x_3454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_3437_, v___x_3453_);
                return v___x_3454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg___boxed(
    mut v_m_3457_: *mut crate::leanh::LeanObject,
    mut v_a_3458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3459_: u8 = 0;
    let mut v_r_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3459_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_3457_, v_a_3458_);
    crate::leanh::lean_dec(v_a_3458_);
    crate::leanh::lean_dec_ref(v_m_3457_);
    v_r_3460_ = crate::leanh::lean_box((v_res_3459_) as usize);
    return v_r_3460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(
    mut v_type_3461_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ = l_Lean_Expr_getAppFn(v_type_3461_);
    if crate::leanh::lean_obj_tag(v___x_3462_) == 4 {
        let mut v_declName_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3465_: u8 = 0;
        v_declName_3463_ = crate::leanh::lean_ctor_get(v___x_3462_, 0);
        crate::leanh::lean_inc(v_declName_3463_);
        crate::leanh::lean_dec_ref_known(v___x_3462_, 2);
        v___x_3464_ =
            l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField;
        v___x_3465_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v___x_3464_, v_declName_3463_);
        crate::leanh::lean_dec(v_declName_3463_);
        return v___x_3465_;
    } else {
        let mut v___x_3466_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_3462_);
        v___x_3466_ = 0;
        return v___x_3466_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick___boxed(
    mut v_type_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3468_: u8 = 0;
    let mut v_r_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(
            v_type_3467_,
        );
    crate::leanh::lean_dec_ref(v_type_3467_);
    v_r_3469_ = crate::leanh::lean_box((v_res_3468_) as usize);
    return v_r_3469_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(
    mut v_00_u03b2_3470_: *mut crate::leanh::LeanObject,
    mut v_m_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3473_: u8 = 0;
    v___x_3473_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_3471_, v_a_3472_);
    return v___x_3473_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___boxed(
    mut v_00_u03b2_3474_: *mut crate::leanh::LeanObject,
    mut v_m_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3477_: u8 = 0;
    let mut v_r_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(v_00_u03b2_3474_, v_m_3475_, v_a_3476_);
    crate::leanh::lean_dec(v_a_3476_);
    crate::leanh::lean_dec_ref(v_m_3475_);
    v_r_3478_ = crate::leanh::lean_box((v_res_3477_) as usize);
    return v_r_3478_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandDiv___redArg(
    mut v_e_3509_: *mut crate::leanh::LeanObject,
    mut v_a_3510_: *mut crate::leanh::LeanObject,
    mut v_a_3511_: *mut crate::leanh::LeanObject,
    mut v_a_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v_arg_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    let mut v_arg_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v_arg_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u8 = 0;
    let mut v_arg_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v_arg_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: u8 = 0;
    let mut v___y_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v_head_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v_val_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v_val_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v_val_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_a_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut v___x_3674_: u8 = 0;
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut v_a_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3685_: u8 = 0;
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3518_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3509_, v_a_3511_);
                if crate::leanh::lean_obj_tag(v___x_3518_) == 0 {
                    v_a_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                    v_isSharedCheck_3681_ = (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3521_ = v___x_3518_;
                        v_isShared_3522_ = v_isSharedCheck_3681_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3519_);
                        crate::leanh::lean_dec(v___x_3518_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3681_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3682_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                    v_isSharedCheck_3689_ = (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v___x_3684_ = v___x_3518_;
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3682_);
                        crate::leanh::lean_dec(v___x_3518_);
                        v___x_3684_ = crate::leanh::lean_box(0);
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 29;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3516_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3516_);
                return v___x_3517_;
            }
            2 => {
                v___x_3528_ = l_Lean_Expr_cleanupAnnotations(v_a_3519_);
                v___x_3529_ = l_Lean_Expr_isApp(v___x_3528_);
                if v___x_3529_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3528_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3530_ = crate::leanh::lean_ctor_get(v___x_3528_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3530_);
                    v___x_3531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3528_);
                    v___x_3532_ = l_Lean_Expr_isApp(v___x_3531_);
                    if v___x_3532_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3531_);
                        crate::leanh::lean_dec_ref(v_arg_3530_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_3533_ = crate::leanh::lean_ctor_get(v___x_3531_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3533_);
                        v___x_3534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3531_);
                        v___x_3535_ = l_Lean_Expr_isApp(v___x_3534_);
                        if v___x_3535_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3534_);
                            crate::leanh::lean_dec_ref(v_arg_3533_);
                            crate::leanh::lean_dec_ref(v_arg_3530_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3536_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
                            v___x_3537_ = l_Lean_Expr_isApp(v___x_3536_);
                            if v___x_3537_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3536_);
                                crate::leanh::lean_dec_ref(v_arg_3533_);
                                crate::leanh::lean_dec_ref(v_arg_3530_);
                                state = 3;
                                continue;
                            } else {
                                v_arg_3538_ = crate::leanh::lean_ctor_get(v___x_3536_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3538_);
                                v___x_3539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3536_);
                                v___x_3540_ = l_Lean_Expr_isApp(v___x_3539_);
                                if v___x_3540_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3539_);
                                    crate::leanh::lean_dec_ref(v_arg_3538_);
                                    crate::leanh::lean_dec_ref(v_arg_3533_);
                                    crate::leanh::lean_dec_ref(v_arg_3530_);
                                    state = 3;
                                    continue;
                                } else {
                                    v_arg_3541_ = crate::leanh::lean_ctor_get(v___x_3539_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_3541_);
                                    v___x_3542_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3539_);
                                    v___x_3543_ = l_Lean_Expr_isApp(v___x_3542_);
                                    if v___x_3543_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3542_);
                                        crate::leanh::lean_dec_ref(v_arg_3541_);
                                        crate::leanh::lean_dec_ref(v_arg_3538_);
                                        crate::leanh::lean_dec_ref(v_arg_3533_);
                                        crate::leanh::lean_dec_ref(v_arg_3530_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_3544_ = crate::leanh::lean_ctor_get(v___x_3542_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_3544_);
                                        v___x_3545_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3542_);
                                        v___x_3546_ =
                                            l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2;
                                        v___x_3547_ =
                                            l_Lean_Expr_isConstOf(v___x_3545_, v___x_3546_);
                                        if v___x_3547_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3545_);
                                            crate::leanh::lean_dec_ref(v_arg_3544_);
                                            crate::leanh::lean_dec_ref(v_arg_3541_);
                                            crate::leanh::lean_dec_ref(v_arg_3538_);
                                            crate::leanh::lean_dec_ref(v_arg_3533_);
                                            crate::leanh::lean_dec_ref(v_arg_3530_);
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_del_object(v___x_3521_);
                                            v___x_3674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_3544_);
                                            if v___x_3674_ == 0 {
                                                crate::leanh::lean_inc_ref(v_arg_3544_);
                                                v___x_3675_ = l_Lean_Meta_isExprDefEq(
                                                    v_arg_3544_,
                                                    v_arg_3541_,
                                                    v_a_3510_,
                                                    v_a_3511_,
                                                    v_a_3512_,
                                                    v_a_3513_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3675_) == 0 {
                                                    v_a_3676_ =
                                                        crate::leanh::lean_ctor_get(v___x_3675_, 0);
                                                    crate::leanh::lean_inc(v_a_3676_);
                                                    v___x_3677_ =
                                                        (crate::leanh::lean_unbox(v_a_3676_) as u8);
                                                    crate::leanh::lean_dec(v_a_3676_);
                                                    if v___x_3677_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_3538_);
                                                        v___y_3549_ = v___x_3675_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3675_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_arg_3544_);
                                                        v___x_3678_ = l_Lean_Meta_isExprDefEq(
                                                            v_arg_3544_,
                                                            v_arg_3538_,
                                                            v_a_3510_,
                                                            v_a_3511_,
                                                            v_a_3512_,
                                                            v_a_3513_,
                                                        );
                                                        v___y_3549_ = v___x_3678_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_3538_);
                                                    v___y_3549_ = v___x_3675_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3545_);
                                                crate::leanh::lean_dec_ref(v_arg_3544_);
                                                crate::leanh::lean_dec_ref(v_arg_3541_);
                                                crate::leanh::lean_dec_ref(v_arg_3538_);
                                                crate::leanh::lean_dec_ref(v_arg_3533_);
                                                crate::leanh::lean_dec_ref(v_arg_3530_);
                                                v___x_3679_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                                                v___x_3680_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3680_,
                                                    0,
                                                    v___x_3679_,
                                                );
                                                return v___x_3680_;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3524_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                if v_isShared_3522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3526_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_3549_) == 0 {
                    v_a_3550_ = crate::leanh::lean_ctor_get(v___y_3549_, 0);
                    v_isSharedCheck_3665_ = (!crate::leanh::lean_is_exclusive(v___y_3549_)) as u8;
                    if v_isSharedCheck_3665_ == 0 {
                        v___x_3552_ = v___y_3549_;
                        v_isShared_3553_ = v_isSharedCheck_3665_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3550_);
                        crate::leanh::lean_dec(v___y_3549_);
                        v___x_3552_ = crate::leanh::lean_box(0);
                        v_isShared_3553_ = v_isSharedCheck_3665_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3545_);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v_a_3666_ = crate::leanh::lean_ctor_get(v___y_3549_, 0);
                    v_isSharedCheck_3673_ = (!crate::leanh::lean_is_exclusive(v___y_3549_)) as u8;
                    if v_isSharedCheck_3673_ == 0 {
                        v___x_3668_ = v___y_3549_;
                        v_isShared_3669_ = v_isSharedCheck_3673_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3666_);
                        crate::leanh::lean_dec(v___y_3549_);
                        v___x_3668_ = crate::leanh::lean_box(0);
                        v_isShared_3669_ = v_isSharedCheck_3673_;
                        state = 27;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3554_ = (crate::leanh::lean_unbox(v_a_3550_) as u8);
                crate::leanh::lean_dec(v_a_3550_);
                if v___x_3554_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3545_);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v___x_3555_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3553_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3555_);
                        v___x_3557_ = v___x_3552_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
                        v___x_3557_ = v_reuseFailAlloc_3558_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3552_);
                    v___x_3559_ = l_Lean_Expr_constLevels_x21(v___x_3545_);
                    crate::leanh::lean_dec_ref(v___x_3545_);
                    if crate::leanh::lean_obj_tag(v___x_3559_) == 1 {
                        v_tail_3560_ = crate::leanh::lean_ctor_get(v___x_3559_, 1);
                        crate::leanh::lean_inc(v_tail_3560_);
                        if crate::leanh::lean_obj_tag(v_tail_3560_) == 1 {
                            v_tail_3561_ = crate::leanh::lean_ctor_get(v_tail_3560_, 1);
                            crate::leanh::lean_inc(v_tail_3561_);
                            crate::leanh::lean_dec_ref_known(v_tail_3560_, 2);
                            if crate::leanh::lean_obj_tag(v_tail_3561_) == 1 {
                                v_tail_3562_ = crate::leanh::lean_ctor_get(v_tail_3561_, 1);
                                v_isSharedCheck_3663_ =
                                    (!crate::leanh::lean_is_exclusive(v_tail_3561_)) as u8;
                                if v_isSharedCheck_3663_ == 0 {
                                    v_unused_3664_ = crate::leanh::lean_ctor_get(v_tail_3561_, 0);
                                    crate::leanh::lean_dec(v_unused_3664_);
                                    v___x_3564_ = v_tail_3561_;
                                    v_isShared_3565_ = v_isSharedCheck_3663_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_tail_3562_);
                                    crate::leanh::lean_dec(v_tail_3561_);
                                    v___x_3564_ = crate::leanh::lean_box(0);
                                    v_isShared_3565_ = v_isSharedCheck_3663_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_tail_3561_);
                                crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                                crate::leanh::lean_dec_ref(v_arg_3544_);
                                crate::leanh::lean_dec_ref(v_arg_3533_);
                                crate::leanh::lean_dec_ref(v_arg_3530_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_3560_);
                            crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                            crate::leanh::lean_dec_ref(v_arg_3544_);
                            crate::leanh::lean_dec_ref(v_arg_3533_);
                            crate::leanh::lean_dec_ref(v_arg_3530_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3559_);
                        crate::leanh::lean_dec_ref(v_arg_3544_);
                        crate::leanh::lean_dec_ref(v_arg_3533_);
                        crate::leanh::lean_dec_ref(v_arg_3530_);
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3557_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_tail_3562_) == 0 {
                    v_head_3566_ = crate::leanh::lean_ctor_get(v___x_3559_, 0);
                    crate::leanh::lean_inc(v_head_3566_);
                    v___x_3567_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4;
                    if v_isShared_3565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3564_, 0, v_head_3566_);
                        v___x_3569_ = v___x_3564_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_head_3566_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_tail_3562_);
                        v___x_3569_ = v_reuseFailAlloc_3662_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3564_);
                    crate::leanh::lean_dec(v_tail_3562_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    state = 1;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v___x_3569_);
                v___x_3570_ = l_Lean_mkConst(v___x_3567_, v___x_3569_);
                crate::leanh::lean_inc_ref(v_arg_3544_);
                v___x_3571_ = l_Lean_Expr_app___override(v___x_3570_, v_arg_3544_);
                v___x_3572_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_3571_,
                    v_a_3510_,
                    v_a_3511_,
                    v_a_3512_,
                    v_a_3513_,
                );
                if crate::leanh::lean_obj_tag(v___x_3572_) == 0 {
                    v_a_3573_ = crate::leanh::lean_ctor_get(v___x_3572_, 0);
                    v_isSharedCheck_3653_ = (!crate::leanh::lean_is_exclusive(v___x_3572_)) as u8;
                    if v_isSharedCheck_3653_ == 0 {
                        v___x_3575_ = v___x_3572_;
                        v_isShared_3576_ = v_isSharedCheck_3653_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3573_);
                        crate::leanh::lean_dec(v___x_3572_);
                        v___x_3575_ = crate::leanh::lean_box(0);
                        v_isShared_3576_ = v_isSharedCheck_3653_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3572_, 0);
                    v_isSharedCheck_3661_ = (!crate::leanh::lean_is_exclusive(v___x_3572_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3656_ = v___x_3572_;
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3654_);
                        crate::leanh::lean_dec(v___x_3572_);
                        v___x_3656_ = crate::leanh::lean_box(0);
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 25;
                        continue;
                    }
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_3573_) == 1 {
                    crate::leanh::lean_del_object(v___x_3575_);
                    v_val_3577_ = crate::leanh::lean_ctor_get(v_a_3573_, 0);
                    crate::leanh::lean_inc(v_val_3577_);
                    crate::leanh::lean_dec_ref_known(v_a_3573_, 1);
                    v___x_3578_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6;
                    crate::leanh::lean_inc_ref(v___x_3559_);
                    v___x_3579_ = l_Lean_mkConst(v___x_3578_, v___x_3559_);
                    crate::leanh::lean_inc_ref_n(v_arg_3544_, 3);
                    v___x_3580_ = l_Lean_mkApp3(v___x_3579_, v_arg_3544_, v_arg_3544_, v_arg_3544_);
                    v___x_3581_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3580_,
                        v_a_3510_,
                        v_a_3511_,
                        v_a_3512_,
                        v_a_3513_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3581_) == 0 {
                        v_a_3582_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                        v_isSharedCheck_3640_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3581_)) as u8;
                        if v_isSharedCheck_3640_ == 0 {
                            v___x_3584_ = v___x_3581_;
                            v_isShared_3585_ = v_isSharedCheck_3640_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3582_);
                            crate::leanh::lean_dec(v___x_3581_);
                            v___x_3584_ = crate::leanh::lean_box(0);
                            v_isShared_3585_ = v_isSharedCheck_3640_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3577_);
                        crate::leanh::lean_dec_ref(v___x_3569_);
                        crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                        crate::leanh::lean_dec_ref(v_arg_3544_);
                        crate::leanh::lean_dec_ref(v_arg_3533_);
                        crate::leanh::lean_dec_ref(v_arg_3530_);
                        v_a_3641_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                        v_isSharedCheck_3648_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3581_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v___x_3643_ = v___x_3581_;
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3641_);
                            crate::leanh::lean_dec(v___x_3581_);
                            v___x_3643_ = crate::leanh::lean_box(0);
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3573_);
                    crate::leanh::lean_dec_ref(v___x_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v___x_3649_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3576_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3649_);
                        v___x_3651_ = v___x_3575_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3652_;
                        state = 24;
                        continue;
                    }
                }
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_3582_) == 1 {
                    crate::leanh::lean_del_object(v___x_3584_);
                    v_val_3586_ = crate::leanh::lean_ctor_get(v_a_3582_, 0);
                    v_isSharedCheck_3635_ = (!crate::leanh::lean_is_exclusive(v_a_3582_)) as u8;
                    if v_isSharedCheck_3635_ == 0 {
                        v___x_3588_ = v_a_3582_;
                        v_isShared_3589_ = v_isSharedCheck_3635_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3586_);
                        crate::leanh::lean_dec(v_a_3582_);
                        v___x_3588_ = crate::leanh::lean_box(0);
                        v_isShared_3589_ = v_isSharedCheck_3635_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3582_);
                    crate::leanh::lean_dec(v_val_3577_);
                    crate::leanh::lean_dec_ref(v___x_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v___x_3636_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3585_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3584_, 0, v___x_3636_);
                        v___x_3638_ = v___x_3584_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 21;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3590_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8;
                crate::leanh::lean_inc_ref(v___x_3569_);
                v___x_3591_ = l_Lean_mkConst(v___x_3590_, v___x_3569_);
                crate::leanh::lean_inc_ref(v_arg_3544_);
                v___x_3592_ = l_Lean_Expr_app___override(v___x_3591_, v_arg_3544_);
                v___x_3593_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_3592_,
                    v_a_3510_,
                    v_a_3511_,
                    v_a_3512_,
                    v_a_3513_,
                );
                if crate::leanh::lean_obj_tag(v___x_3593_) == 0 {
                    v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                    v_isSharedCheck_3626_ = (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                    if v_isSharedCheck_3626_ == 0 {
                        v___x_3596_ = v___x_3593_;
                        v_isShared_3597_ = v_isSharedCheck_3626_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3594_);
                        crate::leanh::lean_dec(v___x_3593_);
                        v___x_3596_ = crate::leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3626_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3588_);
                    crate::leanh::lean_dec(v_val_3586_);
                    crate::leanh::lean_dec(v_val_3577_);
                    crate::leanh::lean_dec_ref(v___x_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v_a_3627_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                    v_isSharedCheck_3634_ = (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3629_ = v___x_3593_;
                        v_isShared_3630_ = v_isSharedCheck_3634_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3627_);
                        crate::leanh::lean_dec(v___x_3593_);
                        v___x_3629_ = crate::leanh::lean_box(0);
                        v_isShared_3630_ = v_isSharedCheck_3634_;
                        state = 19;
                        continue;
                    }
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_3594_) == 1 {
                    v_val_3598_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                    v_isSharedCheck_3621_ = (!crate::leanh::lean_is_exclusive(v_a_3594_)) as u8;
                    if v_isSharedCheck_3621_ == 0 {
                        v___x_3600_ = v_a_3594_;
                        v_isShared_3601_ = v_isSharedCheck_3621_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3598_);
                        crate::leanh::lean_dec(v_a_3594_);
                        v___x_3600_ = crate::leanh::lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3621_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3594_);
                    crate::leanh::lean_del_object(v___x_3588_);
                    crate::leanh::lean_dec(v_val_3586_);
                    crate::leanh::lean_dec(v_val_3577_);
                    crate::leanh::lean_dec_ref(v___x_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 2);
                    crate::leanh::lean_dec_ref(v_arg_3544_);
                    crate::leanh::lean_dec_ref(v_arg_3533_);
                    crate::leanh::lean_dec_ref(v_arg_3530_);
                    v___x_3622_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3597_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3596_, 0, v___x_3622_);
                        v___x_3624_ = v___x_3596_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
                        v___x_3624_ = v_reuseFailAlloc_3625_;
                        state = 18;
                        continue;
                    }
                }
            }
            14 => {
                v___x_3602_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10;
                v___x_3603_ = l_Lean_mkConst(v___x_3602_, v___x_3559_);
                v___x_3604_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12;
                crate::leanh::lean_inc_ref(v___x_3569_);
                v___x_3605_ = l_Lean_mkConst(v___x_3604_, v___x_3569_);
                crate::leanh::lean_inc_ref(v_arg_3530_);
                crate::leanh::lean_inc_ref_n(v_arg_3544_, 4);
                v___x_3606_ = l_Lean_mkApp3(v___x_3605_, v_arg_3544_, v_val_3598_, v_arg_3530_);
                crate::leanh::lean_inc_ref(v_arg_3533_);
                v___x_3607_ = l_Lean_mkApp6(
                    v___x_3603_,
                    v_arg_3544_,
                    v_arg_3544_,
                    v_arg_3544_,
                    v_val_3586_,
                    v_arg_3533_,
                    v___x_3606_,
                );
                v___x_3608_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14;
                v___x_3609_ = l_Lean_mkConst(v___x_3608_, v___x_3569_);
                v___x_3610_ = l_Lean_mkApp4(
                    v___x_3609_,
                    v_arg_3544_,
                    v_val_3577_,
                    v_arg_3533_,
                    v_arg_3530_,
                );
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3610_);
                    v___x_3612_ = v___x_3600_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3610_);
                    v___x_3612_ = v_reuseFailAlloc_3620_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3613_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3613_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3547_,
                );
                if v_isShared_3589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3588_, 0, v___x_3613_);
                    v___x_3615_ = v___x_3588_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3613_);
                    v___x_3615_ = v_reuseFailAlloc_3619_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3596_, 0, v___x_3615_);
                    v___x_3617_ = v___x_3596_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
                    v___x_3617_ = v_reuseFailAlloc_3618_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3617_;
            }
            18 => {
                return v___x_3624_;
            }
            19 => {
                if v_isShared_3630_ == 0 {
                    v___x_3632_ = v___x_3629_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
                    v___x_3632_ = v_reuseFailAlloc_3633_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3632_;
            }
            21 => {
                return v___x_3638_;
            }
            22 => {
                if v_isShared_3644_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3646_;
            }
            24 => {
                return v___x_3651_;
            }
            25 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3659_;
            }
            27 => {
                if v_isShared_3669_ == 0 {
                    v___x_3671_ = v___x_3668_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
                    v___x_3671_ = v_reuseFailAlloc_3672_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3671_;
            }
            29 => {
                if v_isShared_3685_ == 0 {
                    v___x_3687_ = v___x_3684_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
                    v___x_3687_ = v_reuseFailAlloc_3688_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandDiv___redArg___boxed(
    mut v_e_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3696_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg(
        v_e_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_,
    );
    crate::leanh::lean_dec(v_a_3694_);
    crate::leanh::lean_dec_ref(v_a_3693_);
    crate::leanh::lean_dec(v_a_3692_);
    crate::leanh::lean_dec_ref(v_a_3691_);
    return v_res_3696_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandDiv(
    mut v_e_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_a_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_a_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg(
        v_e_3697_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_,
    );
    return v___x_3706_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_expandDiv___boxed(
    mut v_e_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3716_ = l_Lean_Meta_Grind_Arith_expandDiv(
        v_e_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_,
    );
    crate::leanh::lean_dec(v_a_3714_);
    crate::leanh::lean_dec_ref(v_a_3713_);
    crate::leanh::lean_dec(v_a_3712_);
    crate::leanh::lean_dec_ref(v_a_3711_);
    crate::leanh::lean_dec(v_a_3710_);
    crate::leanh::lean_dec_ref(v_a_3709_);
    crate::leanh::lean_dec(v_a_3708_);
    return v_res_3716_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_;
    v___x_3740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_;
    v___x_3741_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_expandDiv___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3742_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3739_, v___x_3740_, v___x_3741_);
    return v___x_3742_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13____boxed(
    mut v_a_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_();
    return v_res_3744_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldInv___redArg(
    mut v_e_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
    mut v_a_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v_arg_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: u8 = 0;
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    let mut v_arg_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v_val_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v_fst_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_unused_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_isSharedCheck_3826_: u8 = 0;
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: u8 = 0;
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: u8 = 0;
    let mut v_a_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_a_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3865_: u8 = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3755_);
                v___x_3764_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3755_, v_a_3757_);
                if crate::leanh::lean_obj_tag(v___x_3764_) == 0 {
                    v_a_3765_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3861_ = (!crate::leanh::lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3861_ == 0 {
                        v___x_3767_ = v___x_3764_;
                        v_isShared_3768_ = v_isSharedCheck_3861_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3765_);
                        crate::leanh::lean_dec(v___x_3764_);
                        v___x_3767_ = crate::leanh::lean_box(0);
                        v_isShared_3768_ = v_isSharedCheck_3861_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3755_);
                    v_a_3862_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3869_ = (!crate::leanh::lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3869_ == 0 {
                        v___x_3864_ = v___x_3764_;
                        v_isShared_3865_ = v_isSharedCheck_3869_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3862_);
                        crate::leanh::lean_dec(v___x_3764_);
                        v___x_3864_ = crate::leanh::lean_box(0);
                        v_isShared_3865_ = v_isSharedCheck_3869_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3762_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                v___x_3763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3762_);
                return v___x_3763_;
            }
            2 => {
                v___x_3774_ = l_Lean_Expr_cleanupAnnotations(v_a_3765_);
                v___x_3775_ = l_Lean_Expr_isApp(v___x_3774_);
                if v___x_3775_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3774_);
                    crate::leanh::lean_dec_ref(v_e_3755_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3776_ = crate::leanh::lean_ctor_get(v___x_3774_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3776_);
                    v___x_3777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3774_);
                    v___x_3778_ = l_Lean_Expr_isApp(v___x_3777_);
                    if v___x_3778_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3777_);
                        crate::leanh::lean_dec_ref(v_arg_3776_);
                        crate::leanh::lean_dec_ref(v_e_3755_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3777_);
                        v___x_3780_ = l_Lean_Expr_isApp(v___x_3779_);
                        if v___x_3780_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3779_);
                            crate::leanh::lean_dec_ref(v_arg_3776_);
                            crate::leanh::lean_dec_ref(v_e_3755_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_3781_ = crate::leanh::lean_ctor_get(v___x_3779_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3781_);
                            v___x_3782_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3779_);
                            v___x_3783_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12;
                            v___x_3784_ = l_Lean_Expr_isConstOf(v___x_3782_, v___x_3783_);
                            crate::leanh::lean_dec_ref(v___x_3782_);
                            if v___x_3784_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_3781_);
                                crate::leanh::lean_dec_ref(v_arg_3776_);
                                crate::leanh::lean_dec_ref(v_e_3755_);
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_3767_);
                                v___x_3785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_3781_);
                                if v___x_3785_ == 0 {
                                    v___x_3786_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                        v_arg_3776_,
                                        v_a_3757_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3786_) == 0 {
                                        v_a_3787_ = crate::leanh::lean_ctor_get(v___x_3786_, 0);
                                        crate::leanh::lean_inc(v_a_3787_);
                                        crate::leanh::lean_dec_ref_known(v___x_3786_, 1);
                                        v___x_3840_ = l_Lean_Expr_cleanupAnnotations(v_a_3787_);
                                        v___x_3841_ = l_Lean_Expr_isApp(v___x_3840_);
                                        if v___x_3841_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3840_);
                                            v___y_3789_ = v_a_3756_;
                                            v___y_3790_ = v_a_3757_;
                                            v___y_3791_ = v_a_3758_;
                                            v___y_3792_ = v_a_3759_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_3842_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3840_);
                                            v___x_3843_ = l_Lean_Expr_isApp(v___x_3842_);
                                            if v___x_3843_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_3842_);
                                                v___y_3789_ = v_a_3756_;
                                                v___y_3790_ = v_a_3757_;
                                                v___y_3791_ = v_a_3758_;
                                                v___y_3792_ = v_a_3759_;
                                                state = 5;
                                                continue;
                                            } else {
                                                v___x_3844_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_3842_);
                                                v___x_3845_ = l_Lean_Expr_isApp(v___x_3844_);
                                                if v___x_3845_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_3844_);
                                                    v___y_3789_ = v_a_3756_;
                                                    v___y_3790_ = v_a_3757_;
                                                    v___y_3791_ = v_a_3758_;
                                                    v___y_3792_ = v_a_3759_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v___x_3846_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3844_,
                                                    );
                                                    v___x_3847_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2;
                                                    v___x_3848_ = l_Lean_Expr_isConstOf(
                                                        v___x_3846_,
                                                        v___x_3847_,
                                                    );
                                                    if v___x_3848_ == 0 {
                                                        v___x_3849_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5;
                                                        v___x_3850_ = l_Lean_Expr_isConstOf(
                                                            v___x_3846_,
                                                            v___x_3849_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v___x_3846_);
                                                        if v___x_3850_ == 0 {
                                                            v___y_3789_ = v_a_3756_;
                                                            v___y_3790_ = v_a_3757_;
                                                            v___y_3791_ = v_a_3758_;
                                                            v___y_3792_ = v_a_3759_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_3781_);
                                                            crate::leanh::lean_dec_ref(v_e_3755_);
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_3846_);
                                                        crate::leanh::lean_dec_ref(v_arg_3781_);
                                                        crate::leanh::lean_dec_ref(v_e_3755_);
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_3781_);
                                        crate::leanh::lean_dec_ref(v_e_3755_);
                                        v_a_3851_ = crate::leanh::lean_ctor_get(v___x_3786_, 0);
                                        v_isSharedCheck_3858_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3786_)) as u8;
                                        if v_isSharedCheck_3858_ == 0 {
                                            v___x_3853_ = v___x_3786_;
                                            v_isShared_3854_ = v_isSharedCheck_3858_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3851_);
                                            crate::leanh::lean_dec(v___x_3786_);
                                            v___x_3853_ = crate::leanh::lean_box(0);
                                            v_isShared_3854_ = v_isSharedCheck_3858_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_3781_);
                                    crate::leanh::lean_dec_ref(v_arg_3776_);
                                    crate::leanh::lean_dec_ref(v_e_3755_);
                                    v___x_3859_ =
                                        l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                                    v___x_3860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3860_, 0, v___x_3859_);
                                    return v___x_3860_;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3770_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                if v_isShared_3768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3767_, 0, v___x_3770_);
                    v___x_3772_ = v___x_3767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
                    v___x_3772_ = v_reuseFailAlloc_3773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3772_;
            }
            5 => {
                v___x_3793_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(
                    v_e_3755_,
                    v_arg_3781_,
                    v___y_3789_,
                    v___y_3790_,
                    v___y_3791_,
                    v___y_3792_,
                );
                if crate::leanh::lean_obj_tag(v___x_3793_) == 0 {
                    v_a_3794_ = crate::leanh::lean_ctor_get(v___x_3793_, 0);
                    v_isSharedCheck_3831_ = (!crate::leanh::lean_is_exclusive(v___x_3793_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3796_ = v___x_3793_;
                        v_isShared_3797_ = v_isSharedCheck_3831_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3794_);
                        crate::leanh::lean_dec(v___x_3793_);
                        v___x_3796_ = crate::leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3831_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3793_, 0);
                    v_isSharedCheck_3839_ = (!crate::leanh::lean_is_exclusive(v___x_3793_)) as u8;
                    if v_isSharedCheck_3839_ == 0 {
                        v___x_3834_ = v___x_3793_;
                        v_isShared_3835_ = v_isSharedCheck_3839_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3832_);
                        crate::leanh::lean_dec(v___x_3793_);
                        v___x_3834_ = crate::leanh::lean_box(0);
                        v_isShared_3835_ = v_isSharedCheck_3839_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3794_) == 1 {
                    crate::leanh::lean_del_object(v___x_3796_);
                    v_val_3798_ = crate::leanh::lean_ctor_get(v_a_3794_, 0);
                    v_isSharedCheck_3826_ = (!crate::leanh::lean_is_exclusive(v_a_3794_)) as u8;
                    if v_isSharedCheck_3826_ == 0 {
                        v___x_3800_ = v_a_3794_;
                        v_isShared_3801_ = v_isSharedCheck_3826_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3798_);
                        crate::leanh::lean_dec(v_a_3794_);
                        v___x_3800_ = crate::leanh::lean_box(0);
                        v_isShared_3801_ = v_isSharedCheck_3826_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3794_);
                    v___x_3827_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_3797_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3827_);
                        v___x_3829_ = v___x_3796_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
                        v___x_3829_ = v_reuseFailAlloc_3830_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v_fst_3802_ = crate::leanh::lean_ctor_get(v_val_3798_, 0);
                crate::leanh::lean_inc(v_fst_3802_);
                v_snd_3803_ = crate::leanh::lean_ctor_get(v_val_3798_, 1);
                crate::leanh::lean_inc_n(v_snd_3803_, 2);
                crate::leanh::lean_dec(v_val_3798_);
                v___x_3804_ = l_Lean_Meta_checkWithKernel(
                    v_snd_3803_,
                    v___y_3789_,
                    v___y_3790_,
                    v___y_3791_,
                    v___y_3792_,
                );
                if crate::leanh::lean_obj_tag(v___x_3804_) == 0 {
                    v_isSharedCheck_3816_ = (!crate::leanh::lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3816_ == 0 {
                        v_unused_3817_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                        crate::leanh::lean_dec(v_unused_3817_);
                        v___x_3806_ = v___x_3804_;
                        v_isShared_3807_ = v_isSharedCheck_3816_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3804_);
                        v___x_3806_ = crate::leanh::lean_box(0);
                        v_isShared_3807_ = v_isSharedCheck_3816_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3803_);
                    crate::leanh::lean_dec(v_fst_3802_);
                    crate::leanh::lean_del_object(v___x_3800_);
                    v_a_3818_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3825_ = (!crate::leanh::lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3825_ == 0 {
                        v___x_3820_ = v___x_3804_;
                        v_isShared_3821_ = v_isSharedCheck_3825_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3818_);
                        crate::leanh::lean_dec(v___x_3804_);
                        v___x_3820_ = crate::leanh::lean_box(0);
                        v_isShared_3821_ = v_isSharedCheck_3825_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3800_, 0, v_snd_3803_);
                    v___x_3809_ = v___x_3800_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_snd_3803_);
                    v___x_3809_ = v_reuseFailAlloc_3815_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3810_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3810_, 0, v_fst_3802_);
                crate::leanh::lean_ctor_set(v___x_3810_, 1, v___x_3809_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3810_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3784_,
                );
                v___x_3811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3811_, 0, v___x_3810_);
                if v_isShared_3807_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3806_, 0, v___x_3811_);
                    v___x_3813_ = v___x_3806_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
                    v___x_3813_ = v_reuseFailAlloc_3814_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3813_;
            }
            11 => {
                if v_isShared_3821_ == 0 {
                    v___x_3823_ = v___x_3820_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
                    v___x_3823_ = v_reuseFailAlloc_3824_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3823_;
            }
            13 => {
                return v___x_3829_;
            }
            14 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3837_;
            }
            16 => {
                if v_isShared_3854_ == 0 {
                    v___x_3856_ = v___x_3853_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
                    v___x_3856_ = v_reuseFailAlloc_3857_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3856_;
            }
            18 => {
                if v_isShared_3865_ == 0 {
                    v___x_3867_ = v___x_3864_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
                    v___x_3867_ = v_reuseFailAlloc_3868_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldInv___redArg___boxed(
    mut v_e_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg(
        v_e_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_,
    );
    crate::leanh::lean_dec(v_a_3874_);
    crate::leanh::lean_dec_ref(v_a_3873_);
    crate::leanh::lean_dec(v_a_3872_);
    crate::leanh::lean_dec_ref(v_a_3871_);
    return v_res_3876_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldInv(
    mut v_e_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_a_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
    mut v_a_3881_: *mut crate::leanh::LeanObject,
    mut v_a_3882_: *mut crate::leanh::LeanObject,
    mut v_a_3883_: *mut crate::leanh::LeanObject,
    mut v_a_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg(
        v_e_3877_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_,
    );
    return v___x_3886_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldInv___boxed(
    mut v_e_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_Lean_Meta_Grind_Arith_normFieldInv(
        v_e_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
    );
    crate::leanh::lean_dec(v_a_3894_);
    crate::leanh::lean_dec_ref(v_a_3893_);
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    crate::leanh::lean_dec(v_a_3890_);
    crate::leanh::lean_dec_ref(v_a_3889_);
    crate::leanh::lean_dec(v_a_3888_);
    return v_res_3896_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_;
    v___x_3917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_;
    v___x_3918_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normFieldInv___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3919_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3916_, v___x_3917_, v___x_3918_);
    return v___x_3919_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12____boxed(
    mut v_a_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_();
    return v_res_3921_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(
    mut v_instPos_3922_: *mut crate::leanh::LeanObject,
    mut v_inst_3923_: *mut crate::leanh::LeanObject,
    mut v_x_3924_: *mut crate::leanh::LeanObject,
    mut v_x_3925_: *mut crate::leanh::LeanObject,
    mut v_x_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3924_) == 5 {
                    v_fn_3928_ = crate::leanh::lean_ctor_get(v_x_3924_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3928_);
                    v_arg_3929_ = crate::leanh::lean_ctor_get(v_x_3924_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3929_);
                    crate::leanh::lean_dec_ref_known(v_x_3924_, 2);
                    v___x_3930_ = lean_array_set(v_x_3925_, v_x_3926_, v_arg_3929_);
                    v___x_3931_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3932_ = lean_nat_sub(v_x_3926_, v___x_3931_);
                    crate::leanh::lean_dec(v_x_3926_);
                    v_x_3924_ = v_fn_3928_;
                    v_x_3925_ = v___x_3930_;
                    v_x_3926_ = v___x_3932_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_3926_);
                    v___x_3934_ = lean_array_set(v_x_3925_, v_instPos_3922_, v_inst_3923_);
                    v___x_3935_ = l_Lean_mkAppN(v_x_3924_, v___x_3934_);
                    crate::leanh::lean_dec_ref(v___x_3934_);
                    v___x_3936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3936_, 0, v___x_3935_);
                    v___x_3937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3936_);
                    return v___x_3937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg___boxed(
    mut v_instPos_3938_: *mut crate::leanh::LeanObject,
    mut v_inst_3939_: *mut crate::leanh::LeanObject,
    mut v_x_3940_: *mut crate::leanh::LeanObject,
    mut v_x_3941_: *mut crate::leanh::LeanObject,
    mut v_x_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(
        v_instPos_3938_,
        v_inst_3939_,
        v_x_3940_,
        v_x_3941_,
        v_x_3942_,
    );
    crate::leanh::lean_dec(v_instPos_3938_);
    return v_res_3944_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normInst___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = crate::leanh::lean_box(0);
    v_dummy_3948_ = l_Lean_Expr_sort___override(v___x_3947_);
    return v_dummy_3948_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normInst___closed__2() -> u64 {
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: u64 = 0;
    v___x_3949_ = 3;
    v___x_3950_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3949_);
    return v___x_3950_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normInst(
    mut v_instPos_3951_: *mut crate::leanh::LeanObject,
    mut v_inst_3952_: *mut crate::leanh::LeanObject,
    mut v_e_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3963_: u8 = 0;
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCurr_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3982_: u8 = 0;
    let mut v_ctxApprox_3983_: u8 = 0;
    let mut v_quasiPatternApprox_3984_: u8 = 0;
    let mut v_constApprox_3985_: u8 = 0;
    let mut v_isDefEqStuckEx_3986_: u8 = 0;
    let mut v_unificationHints_3987_: u8 = 0;
    let mut v_proofIrrelevance_3988_: u8 = 0;
    let mut v_assignSyntheticOpaque_3989_: u8 = 0;
    let mut v_offsetCnstrs_3990_: u8 = 0;
    let mut v_etaStruct_3991_: u8 = 0;
    let mut v_univApprox_3992_: u8 = 0;
    let mut v_iota_3993_: u8 = 0;
    let mut v_beta_3994_: u8 = 0;
    let mut v_proj_3995_: u8 = 0;
    let mut v_zeta_3996_: u8 = 0;
    let mut v_zetaDelta_3997_: u8 = 0;
    let mut v_zetaUnused_3998_: u8 = 0;
    let mut v_zetaHave_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4002_: u8 = 0;
    let mut v_trackZetaDelta_4003_: u8 = 0;
    let mut v_zetaDeltaSet_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4010_: u8 = 0;
    let mut v_inTypeClassResolution_4011_: u8 = 0;
    let mut v_cacheInferType_4012_: u8 = 0;
    let mut v___x_4013_: u8 = 0;
    let mut v_config_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: u64 = 0;
    let mut v___x_4017_: u64 = 0;
    let mut v___x_4018_: u64 = 0;
    let mut v___x_4019_: u64 = 0;
    let mut v___x_4020_: u64 = 0;
    let mut v_key_4021_: u64 = 0;
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: u8 = 0;
    let mut v_a_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v_a_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3972_ = l_Lean_Expr_getAppNumArgs(v_e_3953_);
                v___x_3973_ = lean_nat_dec_lt(v_instPos_3951_, v___x_3972_);
                if v___x_3973_ == 0 {
                    crate::leanh::lean_dec(v___x_3972_);
                    crate::leanh::lean_dec_ref(v_e_3953_);
                    crate::leanh::lean_dec_ref(v_inst_3952_);
                    v___x_3974_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    v___x_3975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3975_, 0, v___x_3974_);
                    return v___x_3975_;
                } else {
                    v___x_3976_ = lean_nat_sub(v___x_3972_, v_instPos_3951_);
                    crate::leanh::lean_dec(v___x_3972_);
                    v___x_3977_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3978_ = lean_nat_sub(v___x_3976_, v___x_3977_);
                    crate::leanh::lean_dec(v___x_3976_);
                    v_instCurr_3979_ = l_Lean_Expr_getRevArg_x21(v_e_3953_, v___x_3978_);
                    v___x_3980_ = lean_expr_eqv(v_inst_3952_, v_instCurr_3979_);
                    if v___x_3980_ == 0 {
                        v___x_3981_ = l_Lean_Meta_Context_config(v_a_3957_);
                        v_foApprox_3982_ = crate::leanh::lean_ctor_get_uint8(v___x_3981_, 0 as u32);
                        v_ctxApprox_3983_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 1 as u32);
                        v_quasiPatternApprox_3984_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 2 as u32);
                        v_constApprox_3985_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 3 as u32);
                        v_isDefEqStuckEx_3986_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 4 as u32);
                        v_unificationHints_3987_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 5 as u32);
                        v_proofIrrelevance_3988_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 6 as u32);
                        v_assignSyntheticOpaque_3989_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 7 as u32);
                        v_offsetCnstrs_3990_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 8 as u32);
                        v_etaStruct_3991_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 10 as u32);
                        v_univApprox_3992_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 11 as u32);
                        v_iota_3993_ = crate::leanh::lean_ctor_get_uint8(v___x_3981_, 12 as u32);
                        v_beta_3994_ = crate::leanh::lean_ctor_get_uint8(v___x_3981_, 13 as u32);
                        v_proj_3995_ = crate::leanh::lean_ctor_get_uint8(v___x_3981_, 14 as u32);
                        v_zeta_3996_ = crate::leanh::lean_ctor_get_uint8(v___x_3981_, 15 as u32);
                        v_zetaDelta_3997_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 16 as u32);
                        v_zetaUnused_3998_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 17 as u32);
                        v_zetaHave_3999_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3981_, 18 as u32);
                        v_isSharedCheck_4038_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3981_)) as u8;
                        if v_isSharedCheck_4038_ == 0 {
                            v___x_4001_ = v___x_3981_;
                            v_isShared_4002_ = v_isSharedCheck_4038_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3981_);
                            v___x_4001_ = crate::leanh::lean_box(0);
                            v_isShared_4002_ = v_isSharedCheck_4038_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_instCurr_3979_);
                        crate::leanh::lean_dec_ref(v_e_3953_);
                        crate::leanh::lean_dec_ref(v_inst_3952_);
                        v___x_4039_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                        v___x_4040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4039_);
                        return v___x_4040_;
                    }
                }
            }
            1 => {
                if v_a_3963_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3953_);
                    crate::leanh::lean_dec_ref(v_inst_3952_);
                    v___x_3964_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    v___x_3965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3964_);
                    return v___x_3965_;
                } else {
                    v_dummy_3966_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normInst___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normInst___closed__1_once),
                        _init_l_Lean_Meta_Grind_Arith_normInst___closed__1,
                    );
                    v_nargs_3967_ = l_Lean_Expr_getAppNumArgs(v_e_3953_);
                    crate::leanh::lean_inc(v_nargs_3967_);
                    v___x_3968_ = lean_mk_array(v_nargs_3967_, v_dummy_3966_);
                    v___x_3969_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3970_ = lean_nat_sub(v_nargs_3967_, v___x_3969_);
                    crate::leanh::lean_dec(v_nargs_3967_);
                    v___x_3971_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_3951_, v_inst_3952_, v_e_3953_, v___x_3968_, v___x_3970_);
                    return v___x_3971_;
                }
            }
            2 => {
                v_trackZetaDelta_4003_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4004_ = crate::leanh::lean_ctor_get(v_a_3957_, 1);
                v_lctx_4005_ = crate::leanh::lean_ctor_get(v_a_3957_, 2);
                v_localInstances_4006_ = crate::leanh::lean_ctor_get(v_a_3957_, 3);
                v_defEqCtx_x3f_4007_ = crate::leanh::lean_ctor_get(v_a_3957_, 4);
                v_synthPendingDepth_4008_ = crate::leanh::lean_ctor_get(v_a_3957_, 5);
                v_canUnfold_x3f_4009_ = crate::leanh::lean_ctor_get(v_a_3957_, 6);
                v_univApprox_4010_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4011_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4012_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_4013_ = 3;
                if v_isShared_4002_ == 0 {
                    v_config_4015_ = v___x_4001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        0 as u32,
                        v_foApprox_3982_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        1 as u32,
                        v_ctxApprox_3983_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        2 as u32,
                        v_quasiPatternApprox_3984_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        3 as u32,
                        v_constApprox_3985_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        4 as u32,
                        v_isDefEqStuckEx_3986_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        5 as u32,
                        v_unificationHints_3987_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        6 as u32,
                        v_proofIrrelevance_3988_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        7 as u32,
                        v_assignSyntheticOpaque_3989_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        8 as u32,
                        v_offsetCnstrs_3990_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        10 as u32,
                        v_etaStruct_3991_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        11 as u32,
                        v_univApprox_3992_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        12 as u32,
                        v_iota_3993_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        13 as u32,
                        v_beta_3994_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        14 as u32,
                        v_proj_3995_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        15 as u32,
                        v_zeta_3996_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        16 as u32,
                        v_zetaDelta_3997_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        17 as u32,
                        v_zetaUnused_3998_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4037_,
                        18 as u32,
                        v_zetaHave_3999_,
                    );
                    v_config_4015_ = v_reuseFailAlloc_4037_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_4015_, 9 as u32, v___x_4013_);
                v___x_4016_ = l_Lean_Meta_Context_configKey(v_a_3957_);
                v___x_4017_ = 3u64;
                v___x_4018_ = lean_uint64_shift_right(v___x_4016_, v___x_4017_);
                v___x_4019_ = lean_uint64_shift_left(v___x_4018_, v___x_4017_);
                v___x_4020_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normInst___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normInst___closed__2_once),
                    _init_l_Lean_Meta_Grind_Arith_normInst___closed__2,
                );
                v_key_4021_ = lean_uint64_lor(v___x_4019_, v___x_4020_);
                v___x_4022_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4022_, 0, v_config_4015_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_4021_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_4009_);
                crate::leanh::lean_inc(v_synthPendingDepth_4008_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_4007_);
                crate::leanh::lean_inc_ref(v_localInstances_4006_);
                crate::leanh::lean_inc_ref(v_lctx_4005_);
                crate::leanh::lean_inc(v_zetaDeltaSet_4004_);
                v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4022_);
                crate::leanh::lean_ctor_set(v___x_4023_, 1, v_zetaDeltaSet_4004_);
                crate::leanh::lean_ctor_set(v___x_4023_, 2, v_lctx_4005_);
                crate::leanh::lean_ctor_set(v___x_4023_, 3, v_localInstances_4006_);
                crate::leanh::lean_ctor_set(v___x_4023_, 4, v_defEqCtx_x3f_4007_);
                crate::leanh::lean_ctor_set(v___x_4023_, 5, v_synthPendingDepth_4008_);
                crate::leanh::lean_ctor_set(v___x_4023_, 6, v_canUnfold_x3f_4009_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4003_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4010_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4011_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4012_,
                );
                crate::leanh::lean_inc_ref(v_inst_3952_);
                v___x_4024_ = l_Lean_Meta_isExprDefEq(
                    v_inst_3952_,
                    v_instCurr_3979_,
                    v___x_4023_,
                    v_a_3958_,
                    v_a_3959_,
                    v_a_3960_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4023_, 7);
                if crate::leanh::lean_obj_tag(v___x_4024_) == 0 {
                    v_a_4025_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                    crate::leanh::lean_inc(v_a_4025_);
                    crate::leanh::lean_dec_ref_known(v___x_4024_, 1);
                    v___x_4026_ = (crate::leanh::lean_unbox(v_a_4025_) as u8);
                    crate::leanh::lean_dec(v_a_4025_);
                    v_a_3963_ = v___x_4026_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4024_) == 0 {
                        v_a_4027_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                        crate::leanh::lean_inc(v_a_4027_);
                        crate::leanh::lean_dec_ref_known(v___x_4024_, 1);
                        v___x_4028_ = (crate::leanh::lean_unbox(v_a_4027_) as u8);
                        crate::leanh::lean_dec(v_a_4027_);
                        v_a_3963_ = v___x_4028_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3953_);
                        crate::leanh::lean_dec_ref(v_inst_3952_);
                        v_a_4029_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                        v_isSharedCheck_4036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4024_)) as u8;
                        if v_isSharedCheck_4036_ == 0 {
                            v___x_4031_ = v___x_4024_;
                            v_isShared_4032_ = v_isSharedCheck_4036_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4029_);
                            crate::leanh::lean_dec(v___x_4024_);
                            v___x_4031_ = crate::leanh::lean_box(0);
                            v_isShared_4032_ = v_isSharedCheck_4036_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_4032_ == 0 {
                    v___x_4034_ = v___x_4031_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normInst___boxed(
    mut v_instPos_4041_: *mut crate::leanh::LeanObject,
    mut v_inst_4042_: *mut crate::leanh::LeanObject,
    mut v_e_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
    mut v_a_4049_: *mut crate::leanh::LeanObject,
    mut v_a_4050_: *mut crate::leanh::LeanObject,
    mut v_a_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4052_ = l_Lean_Meta_Grind_Arith_normInst(
        v_instPos_4041_,
        v_inst_4042_,
        v_e_4043_,
        v_a_4044_,
        v_a_4045_,
        v_a_4046_,
        v_a_4047_,
        v_a_4048_,
        v_a_4049_,
        v_a_4050_,
    );
    crate::leanh::lean_dec(v_a_4050_);
    crate::leanh::lean_dec_ref(v_a_4049_);
    crate::leanh::lean_dec(v_a_4048_);
    crate::leanh::lean_dec_ref(v_a_4047_);
    crate::leanh::lean_dec(v_a_4046_);
    crate::leanh::lean_dec_ref(v_a_4045_);
    crate::leanh::lean_dec(v_a_4044_);
    crate::leanh::lean_dec(v_instPos_4041_);
    return v_res_4052_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(
    mut v_instPos_4053_: *mut crate::leanh::LeanObject,
    mut v_inst_4054_: *mut crate::leanh::LeanObject,
    mut v_x_4055_: *mut crate::leanh::LeanObject,
    mut v_x_4056_: *mut crate::leanh::LeanObject,
    mut v_x_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(
        v_instPos_4053_,
        v_inst_4054_,
        v_x_4055_,
        v_x_4056_,
        v_x_4057_,
    );
    return v___x_4066_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___boxed(
    mut v_instPos_4067_: *mut crate::leanh::LeanObject,
    mut v_inst_4068_: *mut crate::leanh::LeanObject,
    mut v_x_4069_: *mut crate::leanh::LeanObject,
    mut v_x_4070_: *mut crate::leanh::LeanObject,
    mut v_x_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(
        v_instPos_4067_,
        v_inst_4068_,
        v_x_4069_,
        v_x_4070_,
        v_x_4071_,
        v___y_4072_,
        v___y_4073_,
        v___y_4074_,
        v___y_4075_,
        v___y_4076_,
        v___y_4077_,
        v___y_4078_,
    );
    crate::leanh::lean_dec(v___y_4078_);
    crate::leanh::lean_dec_ref(v___y_4077_);
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    crate::leanh::lean_dec(v___y_4074_);
    crate::leanh::lean_dec_ref(v___y_4073_);
    crate::leanh::lean_dec(v___y_4072_);
    crate::leanh::lean_dec(v_instPos_4067_);
    return v_res_4080_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatAddInst(
    mut v_e_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4091_ = l_Lean_Nat_mkInstHAdd;
    v___x_4092_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4090_,
        v___x_4091_,
        v_e_4081_,
        v_a_4082_,
        v_a_4083_,
        v_a_4084_,
        v_a_4085_,
        v_a_4086_,
        v_a_4087_,
        v_a_4088_,
    );
    return v___x_4092_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatAddInst___boxed(
    mut v_e_4093_: *mut crate::leanh::LeanObject,
    mut v_a_4094_: *mut crate::leanh::LeanObject,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
    mut v_a_4097_: *mut crate::leanh::LeanObject,
    mut v_a_4098_: *mut crate::leanh::LeanObject,
    mut v_a_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_Lean_Meta_Grind_Arith_normNatAddInst(
        v_e_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_,
    );
    crate::leanh::lean_dec(v_a_4100_);
    crate::leanh::lean_dec_ref(v_a_4099_);
    crate::leanh::lean_dec(v_a_4098_);
    crate::leanh::lean_dec_ref(v_a_4097_);
    crate::leanh::lean_dec(v_a_4096_);
    crate::leanh::lean_dec_ref(v_a_4095_);
    crate::leanh::lean_dec(v_a_4094_);
    return v_res_4102_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_;
    v___x_4135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_;
    v___x_4136_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatAddInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4137_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4134_, v___x_4135_, v___x_4136_);
    return v___x_4137_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16____boxed(
    mut v_a_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_();
    return v_res_4139_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatMulInst(
    mut v_e_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v_a_4145_: *mut crate::leanh::LeanObject,
    mut v_a_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4150_ = l_Lean_Nat_mkInstHMul;
    v___x_4151_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4149_,
        v___x_4150_,
        v_e_4140_,
        v_a_4141_,
        v_a_4142_,
        v_a_4143_,
        v_a_4144_,
        v_a_4145_,
        v_a_4146_,
        v_a_4147_,
    );
    return v___x_4151_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatMulInst___boxed(
    mut v_e_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
    mut v_a_4156_: *mut crate::leanh::LeanObject,
    mut v_a_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_Lean_Meta_Grind_Arith_normNatMulInst(
        v_e_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_,
    );
    crate::leanh::lean_dec(v_a_4159_);
    crate::leanh::lean_dec_ref(v_a_4158_);
    crate::leanh::lean_dec(v_a_4157_);
    crate::leanh::lean_dec_ref(v_a_4156_);
    crate::leanh::lean_dec(v_a_4155_);
    crate::leanh::lean_dec_ref(v_a_4154_);
    crate::leanh::lean_dec(v_a_4153_);
    return v_res_4161_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_;
    v___x_4186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_;
    v___x_4187_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatMulInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4188_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4185_, v___x_4186_, v___x_4187_);
    return v___x_4188_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16____boxed(
    mut v_a_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_();
    return v_res_4190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatSubInst(
    mut v_e_4191_: *mut crate::leanh::LeanObject,
    mut v_a_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4201_ = l_Lean_Nat_mkInstHSub;
    v___x_4202_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4200_,
        v___x_4201_,
        v_e_4191_,
        v_a_4192_,
        v_a_4193_,
        v_a_4194_,
        v_a_4195_,
        v_a_4196_,
        v_a_4197_,
        v_a_4198_,
    );
    return v___x_4202_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatSubInst___boxed(
    mut v_e_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4212_ = l_Lean_Meta_Grind_Arith_normNatSubInst(
        v_e_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_,
    );
    crate::leanh::lean_dec(v_a_4210_);
    crate::leanh::lean_dec_ref(v_a_4209_);
    crate::leanh::lean_dec(v_a_4208_);
    crate::leanh::lean_dec_ref(v_a_4207_);
    crate::leanh::lean_dec(v_a_4206_);
    crate::leanh::lean_dec_ref(v_a_4205_);
    crate::leanh::lean_dec(v_a_4204_);
    return v_res_4212_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_;
    v___x_4242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_;
    v___x_4243_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatSubInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4244_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4241_, v___x_4242_, v___x_4243_);
    return v___x_4244_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16____boxed(
    mut v_a_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4246_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_();
    return v_res_4246_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatDivInst(
    mut v_e_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4257_ = l_Lean_Nat_mkInstHDiv;
    v___x_4258_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4256_,
        v___x_4257_,
        v_e_4247_,
        v_a_4248_,
        v_a_4249_,
        v_a_4250_,
        v_a_4251_,
        v_a_4252_,
        v_a_4253_,
        v_a_4254_,
    );
    return v___x_4258_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatDivInst___boxed(
    mut v_e_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ = l_Lean_Meta_Grind_Arith_normNatDivInst(
        v_e_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_,
    );
    crate::leanh::lean_dec(v_a_4266_);
    crate::leanh::lean_dec_ref(v_a_4265_);
    crate::leanh::lean_dec(v_a_4264_);
    crate::leanh::lean_dec_ref(v_a_4263_);
    crate::leanh::lean_dec(v_a_4262_);
    crate::leanh::lean_dec_ref(v_a_4261_);
    crate::leanh::lean_dec(v_a_4260_);
    return v_res_4268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_;
    v___x_4290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_;
    v___x_4291_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatDivInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4292_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4289_, v___x_4290_, v___x_4291_);
    return v___x_4292_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16____boxed(
    mut v_a_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_();
    return v_res_4294_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatModInst(
    mut v_e_4295_: *mut crate::leanh::LeanObject,
    mut v_a_4296_: *mut crate::leanh::LeanObject,
    mut v_a_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4304_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4305_ = l_Lean_Nat_mkInstMod;
    v___x_4306_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4304_,
        v___x_4305_,
        v_e_4295_,
        v_a_4296_,
        v_a_4297_,
        v_a_4298_,
        v_a_4299_,
        v_a_4300_,
        v_a_4301_,
        v_a_4302_,
    );
    return v___x_4306_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatModInst___boxed(
    mut v_e_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4316_ = l_Lean_Meta_Grind_Arith_normNatModInst(
        v_e_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_,
    );
    crate::leanh::lean_dec(v_a_4314_);
    crate::leanh::lean_dec_ref(v_a_4313_);
    crate::leanh::lean_dec(v_a_4312_);
    crate::leanh::lean_dec_ref(v_a_4311_);
    crate::leanh::lean_dec(v_a_4310_);
    crate::leanh::lean_dec_ref(v_a_4309_);
    crate::leanh::lean_dec(v_a_4308_);
    return v_res_4316_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_;
    v___x_4346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_;
    v___x_4347_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatModInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4348_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4345_, v___x_4346_, v___x_4347_);
    return v___x_4348_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16____boxed(
    mut v_a_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_();
    return v_res_4350_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatPowInst(
    mut v_e_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4361_ = l_Lean_Nat_mkInstHPow;
    v___x_4362_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4360_,
        v___x_4361_,
        v_e_4351_,
        v_a_4352_,
        v_a_4353_,
        v_a_4354_,
        v_a_4355_,
        v_a_4356_,
        v_a_4357_,
        v_a_4358_,
    );
    return v___x_4362_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatPowInst___boxed(
    mut v_e_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
    mut v_a_4366_: *mut crate::leanh::LeanObject,
    mut v_a_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4372_ = l_Lean_Meta_Grind_Arith_normNatPowInst(
        v_e_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_,
    );
    crate::leanh::lean_dec(v_a_4370_);
    crate::leanh::lean_dec_ref(v_a_4369_);
    crate::leanh::lean_dec(v_a_4368_);
    crate::leanh::lean_dec_ref(v_a_4367_);
    crate::leanh::lean_dec(v_a_4366_);
    crate::leanh::lean_dec_ref(v_a_4365_);
    crate::leanh::lean_dec(v_a_4364_);
    return v_res_4372_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_;
    v___x_4394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_;
    v___x_4395_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatPowInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4396_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4393_, v___x_4394_, v___x_4395_);
    return v___x_4396_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16____boxed(
    mut v_a_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_();
    return v_res_4398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(
    mut v_00_u03b1_4402_: *mut crate::leanh::LeanObject,
    mut v_n_4403_: *mut crate::leanh::LeanObject,
    mut v_inst_4404_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    v___x_4405_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5;
    v___x_4406_ = l_Lean_Expr_isConstOf(v_00_u03b1_4402_, v___x_4405_);
    if v___x_4406_ == 0 {
        return v___x_4406_;
    } else {
        if crate::leanh::lean_obj_tag(v_n_4403_) == 9 {
            let mut v_a_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_4407_ = crate::leanh::lean_ctor_get(v_n_4403_, 0);
            if crate::leanh::lean_obj_tag(v_a_4407_) == 0 {
                let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4410_: u8 = 0;
                v___x_4408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1;
                v___x_4409_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4410_ = l_Lean_Expr_isAppOfArity(v_inst_4404_, v___x_4408_, v___x_4409_);
                if v___x_4410_ == 0 {
                    return v___x_4410_;
                } else {
                    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4412_: u8 = 0;
                    v___x_4411_ = l_Lean_Expr_appArg_x21(v_inst_4404_);
                    v___x_4412_ = lean_expr_eqv(v___x_4411_, v_n_4403_);
                    crate::leanh::lean_dec_ref(v___x_4411_);
                    return v___x_4412_;
                }
            } else {
                let mut v___x_4413_: u8 = 0;
                v___x_4413_ = 0;
                return v___x_4413_;
            }
        } else {
            let mut v___x_4414_: u8 = 0;
            v___x_4414_ = 0;
            return v___x_4414_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___boxed(
    mut v_00_u03b1_4415_: *mut crate::leanh::LeanObject,
    mut v_n_4416_: *mut crate::leanh::LeanObject,
    mut v_inst_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4418_: u8 = 0;
    let mut v_r_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(
            v_00_u03b1_4415_,
            v_n_4416_,
            v_inst_4417_,
        );
    crate::leanh::lean_dec_ref(v_inst_4417_);
    crate::leanh::lean_dec_ref(v_n_4416_);
    crate::leanh::lean_dec_ref(v_00_u03b1_4415_);
    v_r_4419_ = crate::leanh::lean_box((v_res_4418_) as usize);
    return v_r_4419_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(
    mut v_e_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v_arg_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v_arg_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v_arg_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v_val_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4463_: u8 = 0;
    let mut v_a_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4420_);
                v___x_4429_ = l_Lean_Expr_cleanupAnnotations(v_e_4420_);
                v___x_4430_ = l_Lean_Expr_isApp(v___x_4429_);
                if v___x_4430_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4429_);
                    crate::leanh::lean_dec_ref(v_e_4420_);
                    state = 1;
                    continue;
                } else {
                    v_arg_4431_ = crate::leanh::lean_ctor_get(v___x_4429_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4431_);
                    v___x_4432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4429_);
                    v___x_4433_ = l_Lean_Expr_isApp(v___x_4432_);
                    if v___x_4433_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4432_);
                        crate::leanh::lean_dec_ref(v_arg_4431_);
                        crate::leanh::lean_dec_ref(v_e_4420_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_4434_ = crate::leanh::lean_ctor_get(v___x_4432_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4434_);
                        v___x_4435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4432_);
                        v___x_4436_ = l_Lean_Expr_isApp(v___x_4435_);
                        if v___x_4436_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4435_);
                            crate::leanh::lean_dec_ref(v_arg_4434_);
                            crate::leanh::lean_dec_ref(v_arg_4431_);
                            crate::leanh::lean_dec_ref(v_e_4420_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_4437_ = crate::leanh::lean_ctor_get(v___x_4435_, 1);
                            crate::leanh::lean_inc_ref(v_arg_4437_);
                            v___x_4438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4435_);
                            v___x_4439_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2;
                            v___x_4440_ = l_Lean_Expr_isConstOf(v___x_4438_, v___x_4439_);
                            crate::leanh::lean_dec_ref(v___x_4438_);
                            if v___x_4440_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_4437_);
                                crate::leanh::lean_dec_ref(v_arg_4434_);
                                crate::leanh::lean_dec_ref(v_arg_4431_);
                                crate::leanh::lean_dec_ref(v_e_4420_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(v_arg_4437_, v_arg_4434_, v_arg_4431_);
                                crate::leanh::lean_dec_ref(v_arg_4431_);
                                crate::leanh::lean_dec_ref(v_arg_4434_);
                                crate::leanh::lean_dec_ref(v_arg_4437_);
                                if v___x_4441_ == 0 {
                                    v___x_4442_ = l_Lean_Meta_getNatValue_x3f(
                                        v_e_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_,
                                    );
                                    crate::leanh::lean_dec_ref(v_e_4420_);
                                    if crate::leanh::lean_obj_tag(v___x_4442_) == 0 {
                                        v_a_4443_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                                        v_isSharedCheck_4463_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4442_)) as u8;
                                        if v_isSharedCheck_4463_ == 0 {
                                            v___x_4445_ = v___x_4442_;
                                            v_isShared_4446_ = v_isSharedCheck_4463_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4443_);
                                            crate::leanh::lean_dec(v___x_4442_);
                                            v___x_4445_ = crate::leanh::lean_box(0);
                                            v_isShared_4446_ = v_isSharedCheck_4463_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v_a_4464_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                                        v_isSharedCheck_4471_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4442_)) as u8;
                                        if v_isSharedCheck_4471_ == 0 {
                                            v___x_4466_ = v___x_4442_;
                                            v_isShared_4467_ = v_isSharedCheck_4471_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4464_);
                                            crate::leanh::lean_dec(v___x_4442_);
                                            v___x_4466_ = crate::leanh::lean_box(0);
                                            v_isShared_4467_ = v_isSharedCheck_4471_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_4472_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4472_, 0, v_e_4420_);
                                    v___x_4473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4472_);
                                    return v___x_4473_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4427_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                v___x_4428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4428_, 0, v___x_4427_);
                return v___x_4428_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4443_) == 1 {
                    v_val_4447_ = crate::leanh::lean_ctor_get(v_a_4443_, 0);
                    v_isSharedCheck_4458_ = (!crate::leanh::lean_is_exclusive(v_a_4443_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4449_ = v_a_4443_;
                        v_isShared_4450_ = v_isSharedCheck_4458_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4447_);
                        crate::leanh::lean_dec(v_a_4443_);
                        v___x_4449_ = crate::leanh::lean_box(0);
                        v_isShared_4450_ = v_isSharedCheck_4458_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4443_);
                    v___x_4459_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    if v_isShared_4446_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4445_, 0, v___x_4459_);
                        v___x_4461_ = v___x_4445_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
                        v___x_4461_ = v_reuseFailAlloc_4462_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4451_ = l_Lean_mkNatLit(v_val_4447_);
                if v_isShared_4450_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4449_, 0);
                    crate::leanh::lean_ctor_set(v___x_4449_, 0, v___x_4451_);
                    v___x_4453_ = v___x_4449_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4451_);
                    v___x_4453_ = v_reuseFailAlloc_4457_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4445_, 0, v___x_4453_);
                    v___x_4455_ = v___x_4445_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
                    v___x_4455_ = v_reuseFailAlloc_4456_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4455_;
            }
            6 => {
                return v___x_4461_;
            }
            7 => {
                if v_isShared_4467_ == 0 {
                    v___x_4469_ = v___x_4466_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
                    v___x_4469_ = v_reuseFailAlloc_4470_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg___boxed(
    mut v_e_4474_: *mut crate::leanh::LeanObject,
    mut v_a_4475_: *mut crate::leanh::LeanObject,
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4480_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(
        v_e_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_,
    );
    crate::leanh::lean_dec(v_a_4478_);
    crate::leanh::lean_dec_ref(v_a_4477_);
    crate::leanh::lean_dec(v_a_4476_);
    crate::leanh::lean_dec_ref(v_a_4475_);
    return v_res_4480_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatOfNatInst(
    mut v_e_4481_: *mut crate::leanh::LeanObject,
    mut v_a_4482_: *mut crate::leanh::LeanObject,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
    mut v_a_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_a_4486_: *mut crate::leanh::LeanObject,
    mut v_a_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(
        v_e_4481_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_,
    );
    return v___x_4490_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed(
    mut v_e_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
    mut v_a_4495_: *mut crate::leanh::LeanObject,
    mut v_a_4496_: *mut crate::leanh::LeanObject,
    mut v_a_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4500_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst(
        v_e_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_,
    );
    crate::leanh::lean_dec(v_a_4498_);
    crate::leanh::lean_dec_ref(v_a_4497_);
    crate::leanh::lean_dec(v_a_4496_);
    crate::leanh::lean_dec_ref(v_a_4495_);
    crate::leanh::lean_dec(v_a_4494_);
    crate::leanh::lean_dec_ref(v_a_4493_);
    crate::leanh::lean_dec(v_a_4492_);
    return v_res_4500_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_;
    v___x_4522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_;
    v___x_4523_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4524_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4521_, v___x_4522_, v___x_4523_);
    return v___x_4524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13____boxed(
    mut v_a_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_();
    return v_res_4526_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntNegInst(
    mut v_e_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4536_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4537_ = l_Lean_Int_mkInstNeg;
    v___x_4538_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4536_,
        v___x_4537_,
        v_e_4527_,
        v_a_4528_,
        v_a_4529_,
        v_a_4530_,
        v_a_4531_,
        v_a_4532_,
        v_a_4533_,
        v_a_4534_,
    );
    return v___x_4538_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntNegInst___boxed(
    mut v_e_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
    mut v_a_4546_: *mut crate::leanh::LeanObject,
    mut v_a_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_Meta_Grind_Arith_normIntNegInst(
        v_e_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_,
    );
    crate::leanh::lean_dec(v_a_4546_);
    crate::leanh::lean_dec_ref(v_a_4545_);
    crate::leanh::lean_dec(v_a_4544_);
    crate::leanh::lean_dec_ref(v_a_4543_);
    crate::leanh::lean_dec(v_a_4542_);
    crate::leanh::lean_dec_ref(v_a_4541_);
    crate::leanh::lean_dec(v_a_4540_);
    return v_res_4548_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4577_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_;
    v___x_4578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_;
    v___x_4579_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntNegInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4580_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4577_, v___x_4578_, v___x_4579_);
    return v___x_4580_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15____boxed(
    mut v_a_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_();
    return v_res_4582_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntAddInst(
    mut v_e_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4593_ = l_Lean_Int_mkInstHAdd;
    v___x_4594_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4592_,
        v___x_4593_,
        v_e_4583_,
        v_a_4584_,
        v_a_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
        v_a_4590_,
    );
    return v___x_4594_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntAddInst___boxed(
    mut v_e_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
    mut v_a_4600_: *mut crate::leanh::LeanObject,
    mut v_a_4601_: *mut crate::leanh::LeanObject,
    mut v_a_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4604_ = l_Lean_Meta_Grind_Arith_normIntAddInst(
        v_e_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_,
    );
    crate::leanh::lean_dec(v_a_4602_);
    crate::leanh::lean_dec_ref(v_a_4601_);
    crate::leanh::lean_dec(v_a_4600_);
    crate::leanh::lean_dec_ref(v_a_4599_);
    crate::leanh::lean_dec(v_a_4598_);
    crate::leanh::lean_dec_ref(v_a_4597_);
    crate::leanh::lean_dec(v_a_4596_);
    return v_res_4604_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_;
    v___x_4626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_;
    v___x_4627_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntAddInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4628_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4625_, v___x_4626_, v___x_4627_);
    return v___x_4628_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16____boxed(
    mut v_a_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_();
    return v_res_4630_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntMulInst(
    mut v_e_4631_: *mut crate::leanh::LeanObject,
    mut v_a_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_a_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4640_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4641_ = l_Lean_Int_mkInstHMul;
    v___x_4642_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4640_,
        v___x_4641_,
        v_e_4631_,
        v_a_4632_,
        v_a_4633_,
        v_a_4634_,
        v_a_4635_,
        v_a_4636_,
        v_a_4637_,
        v_a_4638_,
    );
    return v___x_4642_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntMulInst___boxed(
    mut v_e_4643_: *mut crate::leanh::LeanObject,
    mut v_a_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_a_4647_: *mut crate::leanh::LeanObject,
    mut v_a_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Lean_Meta_Grind_Arith_normIntMulInst(
        v_e_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_,
    );
    crate::leanh::lean_dec(v_a_4650_);
    crate::leanh::lean_dec_ref(v_a_4649_);
    crate::leanh::lean_dec(v_a_4648_);
    crate::leanh::lean_dec_ref(v_a_4647_);
    crate::leanh::lean_dec(v_a_4646_);
    crate::leanh::lean_dec_ref(v_a_4645_);
    crate::leanh::lean_dec(v_a_4644_);
    return v_res_4652_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_;
    v___x_4674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_;
    v___x_4675_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntMulInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4676_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4673_, v___x_4674_, v___x_4675_);
    return v___x_4676_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16____boxed(
    mut v_a_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_();
    return v_res_4678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntSubInst(
    mut v_e_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_a_4682_: *mut crate::leanh::LeanObject,
    mut v_a_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
    mut v_a_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4689_ = l_Lean_Int_mkInstHSub;
    v___x_4690_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4688_,
        v___x_4689_,
        v_e_4679_,
        v_a_4680_,
        v_a_4681_,
        v_a_4682_,
        v_a_4683_,
        v_a_4684_,
        v_a_4685_,
        v_a_4686_,
    );
    return v___x_4690_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntSubInst___boxed(
    mut v_e_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
    mut v_a_4693_: *mut crate::leanh::LeanObject,
    mut v_a_4694_: *mut crate::leanh::LeanObject,
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_a_4697_: *mut crate::leanh::LeanObject,
    mut v_a_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4700_ = l_Lean_Meta_Grind_Arith_normIntSubInst(
        v_e_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_,
    );
    crate::leanh::lean_dec(v_a_4698_);
    crate::leanh::lean_dec_ref(v_a_4697_);
    crate::leanh::lean_dec(v_a_4696_);
    crate::leanh::lean_dec_ref(v_a_4695_);
    crate::leanh::lean_dec(v_a_4694_);
    crate::leanh::lean_dec_ref(v_a_4693_);
    crate::leanh::lean_dec(v_a_4692_);
    return v_res_4700_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_;
    v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_;
    v___x_4723_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntSubInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4724_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4721_, v___x_4722_, v___x_4723_);
    return v___x_4724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16____boxed(
    mut v_a_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_();
    return v_res_4726_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntDivInst(
    mut v_e_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
    mut v_a_4730_: *mut crate::leanh::LeanObject,
    mut v_a_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4736_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4737_ = l_Lean_Int_mkInstHDiv;
    v___x_4738_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4736_,
        v___x_4737_,
        v_e_4727_,
        v_a_4728_,
        v_a_4729_,
        v_a_4730_,
        v_a_4731_,
        v_a_4732_,
        v_a_4733_,
        v_a_4734_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntDivInst___boxed(
    mut v_e_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
    mut v_a_4741_: *mut crate::leanh::LeanObject,
    mut v_a_4742_: *mut crate::leanh::LeanObject,
    mut v_a_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4748_ = l_Lean_Meta_Grind_Arith_normIntDivInst(
        v_e_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_,
    );
    crate::leanh::lean_dec(v_a_4746_);
    crate::leanh::lean_dec_ref(v_a_4745_);
    crate::leanh::lean_dec(v_a_4744_);
    crate::leanh::lean_dec_ref(v_a_4743_);
    crate::leanh::lean_dec(v_a_4742_);
    crate::leanh::lean_dec_ref(v_a_4741_);
    crate::leanh::lean_dec(v_a_4740_);
    return v_res_4748_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_;
    v___x_4770_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_;
    v___x_4771_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntDivInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4772_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4769_, v___x_4770_, v___x_4771_);
    return v___x_4772_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16____boxed(
    mut v_a_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_();
    return v_res_4774_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntModInst(
    mut v_e_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4784_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4785_ = l_Lean_Int_mkInstMod;
    v___x_4786_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4784_,
        v___x_4785_,
        v_e_4775_,
        v_a_4776_,
        v_a_4777_,
        v_a_4778_,
        v_a_4779_,
        v_a_4780_,
        v_a_4781_,
        v_a_4782_,
    );
    return v___x_4786_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntModInst___boxed(
    mut v_e_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Lean_Meta_Grind_Arith_normIntModInst(
        v_e_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_,
    );
    crate::leanh::lean_dec(v_a_4794_);
    crate::leanh::lean_dec_ref(v_a_4793_);
    crate::leanh::lean_dec(v_a_4792_);
    crate::leanh::lean_dec_ref(v_a_4791_);
    crate::leanh::lean_dec(v_a_4790_);
    crate::leanh::lean_dec_ref(v_a_4789_);
    crate::leanh::lean_dec(v_a_4788_);
    return v_res_4796_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_;
    v___x_4818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_;
    v___x_4819_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntModInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4820_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4817_, v___x_4818_, v___x_4819_);
    return v___x_4820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16____boxed(
    mut v_a_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_();
    return v_res_4822_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntPowInst(
    mut v_e_4823_: *mut crate::leanh::LeanObject,
    mut v_a_4824_: *mut crate::leanh::LeanObject,
    mut v_a_4825_: *mut crate::leanh::LeanObject,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_a_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_4833_ = l_Lean_Int_mkInstHPow;
    v___x_4834_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4832_,
        v___x_4833_,
        v_e_4823_,
        v_a_4824_,
        v_a_4825_,
        v_a_4826_,
        v_a_4827_,
        v_a_4828_,
        v_a_4829_,
        v_a_4830_,
    );
    return v___x_4834_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntPowInst___boxed(
    mut v_e_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
    mut v_a_4837_: *mut crate::leanh::LeanObject,
    mut v_a_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4844_ = l_Lean_Meta_Grind_Arith_normIntPowInst(
        v_e_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_,
    );
    crate::leanh::lean_dec(v_a_4842_);
    crate::leanh::lean_dec_ref(v_a_4841_);
    crate::leanh::lean_dec(v_a_4840_);
    crate::leanh::lean_dec_ref(v_a_4839_);
    crate::leanh::lean_dec(v_a_4838_);
    crate::leanh::lean_dec_ref(v_a_4837_);
    crate::leanh::lean_dec(v_a_4836_);
    return v_res_4844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_;
    v___x_4866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_;
    v___x_4867_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntPowInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4868_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4865_, v___x_4866_, v___x_4867_);
    return v___x_4868_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16____boxed(
    mut v_a_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_();
    return v_res_4870_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastInst(
    mut v_e_4871_: *mut crate::leanh::LeanObject,
    mut v_a_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
    mut v_a_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4881_ = l_Lean_Int_mkInstNatCast;
    v___x_4882_ = l_Lean_Meta_Grind_Arith_normInst(
        v___x_4880_,
        v___x_4881_,
        v_e_4871_,
        v_a_4872_,
        v_a_4873_,
        v_a_4874_,
        v_a_4875_,
        v_a_4876_,
        v_a_4877_,
        v_a_4878_,
    );
    return v___x_4882_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastInst___boxed(
    mut v_e_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
    mut v_a_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_Meta_Grind_Arith_normNatCastInst(
        v_e_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_,
    );
    crate::leanh::lean_dec(v_a_4890_);
    crate::leanh::lean_dec_ref(v_a_4889_);
    crate::leanh::lean_dec(v_a_4888_);
    crate::leanh::lean_dec_ref(v_a_4887_);
    crate::leanh::lean_dec(v_a_4886_);
    crate::leanh::lean_dec_ref(v_a_4885_);
    crate::leanh::lean_dec(v_a_4884_);
    return v_res_4892_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_;
    v___x_4914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_;
    v___x_4915_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatCastInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4916_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4913_, v___x_4914_, v___x_4915_);
    return v___x_4916_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13____boxed(
    mut v_a_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_();
    return v_res_4918_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(
    mut v_00_u03b1_4922_: *mut crate::leanh::LeanObject,
    mut v_n_4923_: *mut crate::leanh::LeanObject,
    mut v_inst_4924_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    v___x_4925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3;
    v___x_4926_ = l_Lean_Expr_isConstOf(v_00_u03b1_4922_, v___x_4925_);
    if v___x_4926_ == 0 {
        return v___x_4926_;
    } else {
        if crate::leanh::lean_obj_tag(v_n_4923_) == 9 {
            let mut v_a_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_4927_ = crate::leanh::lean_ctor_get(v_n_4923_, 0);
            if crate::leanh::lean_obj_tag(v_a_4927_) == 0 {
                let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4930_: u8 = 0;
                v___x_4928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1;
                v___x_4929_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4930_ = l_Lean_Expr_isAppOfArity(v_inst_4924_, v___x_4928_, v___x_4929_);
                if v___x_4930_ == 0 {
                    return v___x_4930_;
                } else {
                    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4932_: u8 = 0;
                    v___x_4931_ = l_Lean_Expr_appArg_x21(v_inst_4924_);
                    v___x_4932_ = lean_expr_eqv(v___x_4931_, v_n_4923_);
                    crate::leanh::lean_dec_ref(v___x_4931_);
                    return v___x_4932_;
                }
            } else {
                let mut v___x_4933_: u8 = 0;
                v___x_4933_ = 0;
                return v___x_4933_;
            }
        } else {
            let mut v___x_4934_: u8 = 0;
            v___x_4934_ = 0;
            return v___x_4934_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___boxed(
    mut v_00_u03b1_4935_: *mut crate::leanh::LeanObject,
    mut v_n_4936_: *mut crate::leanh::LeanObject,
    mut v_inst_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4938_: u8 = 0;
    let mut v_r_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4938_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(
            v_00_u03b1_4935_,
            v_n_4936_,
            v_inst_4937_,
        );
    crate::leanh::lean_dec_ref(v_inst_4937_);
    crate::leanh::lean_dec_ref(v_n_4936_);
    crate::leanh::lean_dec_ref(v_00_u03b1_4935_);
    v_r_4939_ = crate::leanh::lean_box((v_res_4938_) as usize);
    return v_r_4939_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(
    mut v_e_4940_: *mut crate::leanh::LeanObject,
    mut v_a_4941_: *mut crate::leanh::LeanObject,
    mut v_a_4942_: *mut crate::leanh::LeanObject,
    mut v_a_4943_: *mut crate::leanh::LeanObject,
    mut v_a_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: u8 = 0;
    let mut v_arg_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v_arg_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v_arg_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: u8 = 0;
    let mut v___x_4961_: u8 = 0;
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4966_: u8 = 0;
    let mut v_val_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4970_: u8 = 0;
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4978_: u8 = 0;
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_a_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4987_: u8 = 0;
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4940_);
                v___x_4949_ = l_Lean_Expr_cleanupAnnotations(v_e_4940_);
                v___x_4950_ = l_Lean_Expr_isApp(v___x_4949_);
                if v___x_4950_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4949_);
                    crate::leanh::lean_dec_ref(v_e_4940_);
                    state = 1;
                    continue;
                } else {
                    v_arg_4951_ = crate::leanh::lean_ctor_get(v___x_4949_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4951_);
                    v___x_4952_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4949_);
                    v___x_4953_ = l_Lean_Expr_isApp(v___x_4952_);
                    if v___x_4953_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4952_);
                        crate::leanh::lean_dec_ref(v_arg_4951_);
                        crate::leanh::lean_dec_ref(v_e_4940_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_4954_ = crate::leanh::lean_ctor_get(v___x_4952_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4954_);
                        v___x_4955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4952_);
                        v___x_4956_ = l_Lean_Expr_isApp(v___x_4955_);
                        if v___x_4956_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4955_);
                            crate::leanh::lean_dec_ref(v_arg_4954_);
                            crate::leanh::lean_dec_ref(v_arg_4951_);
                            crate::leanh::lean_dec_ref(v_e_4940_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_4957_ = crate::leanh::lean_ctor_get(v___x_4955_, 1);
                            crate::leanh::lean_inc_ref(v_arg_4957_);
                            v___x_4958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4955_);
                            v___x_4959_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2;
                            v___x_4960_ = l_Lean_Expr_isConstOf(v___x_4958_, v___x_4959_);
                            crate::leanh::lean_dec_ref(v___x_4958_);
                            if v___x_4960_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_4957_);
                                crate::leanh::lean_dec_ref(v_arg_4954_);
                                crate::leanh::lean_dec_ref(v_arg_4951_);
                                crate::leanh::lean_dec_ref(v_e_4940_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(v_arg_4957_, v_arg_4954_, v_arg_4951_);
                                crate::leanh::lean_dec_ref(v_arg_4951_);
                                crate::leanh::lean_dec_ref(v_arg_4954_);
                                crate::leanh::lean_dec_ref(v_arg_4957_);
                                if v___x_4961_ == 0 {
                                    v___x_4962_ = l_Lean_Meta_getIntValue_x3f(
                                        v_e_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4962_) == 0 {
                                        v_a_4963_ = crate::leanh::lean_ctor_get(v___x_4962_, 0);
                                        v_isSharedCheck_4983_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4962_)) as u8;
                                        if v_isSharedCheck_4983_ == 0 {
                                            v___x_4965_ = v___x_4962_;
                                            v_isShared_4966_ = v_isSharedCheck_4983_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4963_);
                                            crate::leanh::lean_dec(v___x_4962_);
                                            v___x_4965_ = crate::leanh::lean_box(0);
                                            v_isShared_4966_ = v_isSharedCheck_4983_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v_a_4984_ = crate::leanh::lean_ctor_get(v___x_4962_, 0);
                                        v_isSharedCheck_4991_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4962_)) as u8;
                                        if v_isSharedCheck_4991_ == 0 {
                                            v___x_4986_ = v___x_4962_;
                                            v_isShared_4987_ = v_isSharedCheck_4991_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4984_);
                                            crate::leanh::lean_dec(v___x_4962_);
                                            v___x_4986_ = crate::leanh::lean_box(0);
                                            v_isShared_4987_ = v_isSharedCheck_4991_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_4992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4992_, 0, v_e_4940_);
                                    v___x_4993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4993_, 0, v___x_4992_);
                                    return v___x_4993_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4947_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                v___x_4948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4948_, 0, v___x_4947_);
                return v___x_4948_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4963_) == 1 {
                    v_val_4967_ = crate::leanh::lean_ctor_get(v_a_4963_, 0);
                    v_isSharedCheck_4978_ = (!crate::leanh::lean_is_exclusive(v_a_4963_)) as u8;
                    if v_isSharedCheck_4978_ == 0 {
                        v___x_4969_ = v_a_4963_;
                        v_isShared_4970_ = v_isSharedCheck_4978_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4967_);
                        crate::leanh::lean_dec(v_a_4963_);
                        v___x_4969_ = crate::leanh::lean_box(0);
                        v_isShared_4970_ = v_isSharedCheck_4978_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4963_);
                    v___x_4979_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    if v_isShared_4966_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4979_);
                        v___x_4981_ = v___x_4965_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
                        v___x_4981_ = v_reuseFailAlloc_4982_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4971_ = l_Lean_mkIntLit(v_val_4967_);
                crate::leanh::lean_dec(v_val_4967_);
                if v_isShared_4970_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4969_, 0);
                    crate::leanh::lean_ctor_set(v___x_4969_, 0, v___x_4971_);
                    v___x_4973_ = v___x_4969_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4971_);
                    v___x_4973_ = v_reuseFailAlloc_4977_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4973_);
                    v___x_4975_ = v___x_4965_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4973_);
                    v___x_4975_ = v_reuseFailAlloc_4976_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4975_;
            }
            6 => {
                return v___x_4981_;
            }
            7 => {
                if v_isShared_4987_ == 0 {
                    v___x_4989_ = v___x_4986_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
                    v___x_4989_ = v_reuseFailAlloc_4990_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg___boxed(
    mut v_e_4994_: *mut crate::leanh::LeanObject,
    mut v_a_4995_: *mut crate::leanh::LeanObject,
    mut v_a_4996_: *mut crate::leanh::LeanObject,
    mut v_a_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5000_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(
        v_e_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_,
    );
    crate::leanh::lean_dec(v_a_4998_);
    crate::leanh::lean_dec_ref(v_a_4997_);
    crate::leanh::lean_dec(v_a_4996_);
    crate::leanh::lean_dec_ref(v_a_4995_);
    return v_res_5000_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntOfNatInst(
    mut v_e_5001_: *mut crate::leanh::LeanObject,
    mut v_a_5002_: *mut crate::leanh::LeanObject,
    mut v_a_5003_: *mut crate::leanh::LeanObject,
    mut v_a_5004_: *mut crate::leanh::LeanObject,
    mut v_a_5005_: *mut crate::leanh::LeanObject,
    mut v_a_5006_: *mut crate::leanh::LeanObject,
    mut v_a_5007_: *mut crate::leanh::LeanObject,
    mut v_a_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5010_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(
        v_e_5001_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_,
    );
    return v___x_5010_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed(
    mut v_e_5011_: *mut crate::leanh::LeanObject,
    mut v_a_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
    mut v_a_5015_: *mut crate::leanh::LeanObject,
    mut v_a_5016_: *mut crate::leanh::LeanObject,
    mut v_a_5017_: *mut crate::leanh::LeanObject,
    mut v_a_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst(
        v_e_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_,
    );
    crate::leanh::lean_dec(v_a_5018_);
    crate::leanh::lean_dec_ref(v_a_5017_);
    crate::leanh::lean_dec(v_a_5016_);
    crate::leanh::lean_dec_ref(v_a_5015_);
    crate::leanh::lean_dec(v_a_5014_);
    crate::leanh::lean_dec_ref(v_a_5013_);
    crate::leanh::lean_dec(v_a_5012_);
    return v_res_5020_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_;
    v___x_5039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_;
    v___x_5040_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5041_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5038_, v___x_5039_, v___x_5040_);
    return v___x_5041_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13____boxed(
    mut v_a_5042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_();
    return v_res_5043_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(
    mut v_e_5050_: *mut crate::leanh::LeanObject,
    mut v_a_5051_: *mut crate::leanh::LeanObject,
    mut v_a_5052_: *mut crate::leanh::LeanObject,
    mut v_a_5053_: *mut crate::leanh::LeanObject,
    mut v_a_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: u8 = 0;
    let mut v_arg_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: u8 = 0;
    let mut v_arg_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v_val_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v_val_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5091_: u8 = 0;
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5096_: u8 = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5110_: u8 = 0;
    let mut v_a_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5114_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5118_: u8 = 0;
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut v_a_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5128_: u8 = 0;
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5132_: u8 = 0;
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5059_ = l_Lean_Expr_cleanupAnnotations(v_e_5050_);
                v___x_5060_ = l_Lean_Expr_isApp(v___x_5059_);
                if v___x_5060_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5059_);
                    state = 1;
                    continue;
                } else {
                    v_arg_5061_ = crate::leanh::lean_ctor_get(v___x_5059_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5061_);
                    v___x_5062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5059_);
                    v___x_5063_ = l_Lean_Expr_isApp(v___x_5062_);
                    if v___x_5063_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5062_);
                        crate::leanh::lean_dec_ref(v_arg_5061_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5062_);
                        v___x_5065_ = l_Lean_Expr_isApp(v___x_5064_);
                        if v___x_5065_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5064_);
                            crate::leanh::lean_dec_ref(v_arg_5061_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_5066_ = crate::leanh::lean_ctor_get(v___x_5064_, 1);
                            crate::leanh::lean_inc_ref(v_arg_5066_);
                            v___x_5067_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5064_);
                            v___x_5068_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5;
                            v___x_5069_ = l_Lean_Expr_isConstOf(v___x_5067_, v___x_5068_);
                            if v___x_5069_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5067_);
                                crate::leanh::lean_dec_ref(v_arg_5066_);
                                crate::leanh::lean_dec_ref(v_arg_5061_);
                                state = 1;
                                continue;
                            } else {
                                v___x_5070_ = l_Lean_Meta_getNatValue_x3f(
                                    v_arg_5061_,
                                    v_a_5051_,
                                    v_a_5052_,
                                    v_a_5053_,
                                    v_a_5054_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5070_) == 0 {
                                    v_a_5071_ = crate::leanh::lean_ctor_get(v___x_5070_, 0);
                                    v_isSharedCheck_5138_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5070_)) as u8;
                                    if v_isSharedCheck_5138_ == 0 {
                                        v___x_5073_ = v___x_5070_;
                                        v_isShared_5074_ = v_isSharedCheck_5138_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5071_);
                                        crate::leanh::lean_dec(v___x_5070_);
                                        v___x_5073_ = crate::leanh::lean_box(0);
                                        v_isShared_5074_ = v_isSharedCheck_5138_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5067_);
                                    crate::leanh::lean_dec_ref(v_arg_5066_);
                                    crate::leanh::lean_dec_ref(v_arg_5061_);
                                    v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5070_, 0);
                                    v_isSharedCheck_5146_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5070_)) as u8;
                                    if v_isSharedCheck_5146_ == 0 {
                                        v___x_5141_ = v___x_5070_;
                                        v_isShared_5142_ = v_isSharedCheck_5146_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5139_);
                                        crate::leanh::lean_dec(v___x_5070_);
                                        v___x_5141_ = crate::leanh::lean_box(0);
                                        v_isShared_5142_ = v_isSharedCheck_5146_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5057_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5058_, 0, v___x_5057_);
                return v___x_5058_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5071_) == 1 {
                    crate::leanh::lean_del_object(v___x_5073_);
                    v_val_5075_ = crate::leanh::lean_ctor_get(v_a_5071_, 0);
                    v_isSharedCheck_5133_ = (!crate::leanh::lean_is_exclusive(v_a_5071_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v___x_5077_ = v_a_5071_;
                        v_isShared_5078_ = v_isSharedCheck_5133_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5075_);
                        crate::leanh::lean_dec(v_a_5071_);
                        v___x_5077_ = crate::leanh::lean_box(0);
                        v_isShared_5078_ = v_isSharedCheck_5133_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5071_);
                    crate::leanh::lean_dec_ref(v___x_5067_);
                    crate::leanh::lean_dec_ref(v_arg_5066_);
                    crate::leanh::lean_dec_ref(v_arg_5061_);
                    v___x_5134_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_5074_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5073_, 0, v___x_5134_);
                        v___x_5136_ = v___x_5073_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5134_);
                        v___x_5136_ = v_reuseFailAlloc_5137_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5079_ = l_Lean_Expr_constLevels_x21(v___x_5067_);
                crate::leanh::lean_dec_ref(v___x_5067_);
                v___x_5080_ = l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3;
                crate::leanh::lean_inc(v___x_5079_);
                v___x_5081_ = l_Lean_mkConst(v___x_5080_, v___x_5079_);
                crate::leanh::lean_inc_ref(v_arg_5066_);
                v___x_5082_ = l_Lean_Expr_app___override(v___x_5081_, v_arg_5066_);
                v___x_5083_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_5082_,
                    v_a_5051_,
                    v_a_5052_,
                    v_a_5053_,
                    v_a_5054_,
                );
                if crate::leanh::lean_obj_tag(v___x_5083_) == 0 {
                    v_a_5084_ = crate::leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5124_ = (!crate::leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5124_ == 0 {
                        v___x_5086_ = v___x_5083_;
                        v_isShared_5087_ = v_isSharedCheck_5124_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5084_);
                        crate::leanh::lean_dec(v___x_5083_);
                        v___x_5086_ = crate::leanh::lean_box(0);
                        v_isShared_5087_ = v_isSharedCheck_5124_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5079_);
                    crate::leanh::lean_del_object(v___x_5077_);
                    crate::leanh::lean_dec(v_val_5075_);
                    crate::leanh::lean_dec_ref(v_arg_5066_);
                    crate::leanh::lean_dec_ref(v_arg_5061_);
                    v_a_5125_ = crate::leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5132_ = (!crate::leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5132_ == 0 {
                        v___x_5127_ = v___x_5083_;
                        v_isShared_5128_ = v_isSharedCheck_5132_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5125_);
                        crate::leanh::lean_dec(v___x_5083_);
                        v___x_5127_ = crate::leanh::lean_box(0);
                        v_isShared_5128_ = v_isSharedCheck_5132_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_5084_) == 1 {
                    crate::leanh::lean_del_object(v___x_5086_);
                    v_val_5088_ = crate::leanh::lean_ctor_get(v_a_5084_, 0);
                    v_isSharedCheck_5119_ = (!crate::leanh::lean_is_exclusive(v_a_5084_)) as u8;
                    if v_isSharedCheck_5119_ == 0 {
                        v___x_5090_ = v_a_5084_;
                        v_isShared_5091_ = v_isSharedCheck_5119_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5088_);
                        crate::leanh::lean_dec(v_a_5084_);
                        v___x_5090_ = crate::leanh::lean_box(0);
                        v_isShared_5091_ = v_isSharedCheck_5119_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5084_);
                    crate::leanh::lean_dec(v___x_5079_);
                    crate::leanh::lean_del_object(v___x_5077_);
                    crate::leanh::lean_dec(v_val_5075_);
                    crate::leanh::lean_dec_ref(v_arg_5066_);
                    crate::leanh::lean_dec_ref(v_arg_5061_);
                    v___x_5120_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_5087_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5086_, 0, v___x_5120_);
                        v___x_5122_ = v___x_5086_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5120_);
                        v___x_5122_ = v_reuseFailAlloc_5123_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_arg_5066_);
                v___x_5092_ = l_Lean_Meta_mkNumeral(
                    v_arg_5066_,
                    v_val_5075_,
                    v_a_5051_,
                    v_a_5052_,
                    v_a_5053_,
                    v_a_5054_,
                );
                if crate::leanh::lean_obj_tag(v___x_5092_) == 0 {
                    v_a_5093_ = crate::leanh::lean_ctor_get(v___x_5092_, 0);
                    v_isSharedCheck_5110_ = (!crate::leanh::lean_is_exclusive(v___x_5092_)) as u8;
                    if v_isSharedCheck_5110_ == 0 {
                        v___x_5095_ = v___x_5092_;
                        v_isShared_5096_ = v_isSharedCheck_5110_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5093_);
                        crate::leanh::lean_dec(v___x_5092_);
                        v___x_5095_ = crate::leanh::lean_box(0);
                        v_isShared_5096_ = v_isSharedCheck_5110_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5090_);
                    crate::leanh::lean_dec(v_val_5088_);
                    crate::leanh::lean_dec(v___x_5079_);
                    crate::leanh::lean_del_object(v___x_5077_);
                    crate::leanh::lean_dec_ref(v_arg_5066_);
                    crate::leanh::lean_dec_ref(v_arg_5061_);
                    v_a_5111_ = crate::leanh::lean_ctor_get(v___x_5092_, 0);
                    v_isSharedCheck_5118_ = (!crate::leanh::lean_is_exclusive(v___x_5092_)) as u8;
                    if v_isSharedCheck_5118_ == 0 {
                        v___x_5113_ = v___x_5092_;
                        v_isShared_5114_ = v_isSharedCheck_5118_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5111_);
                        crate::leanh::lean_dec(v___x_5092_);
                        v___x_5113_ = crate::leanh::lean_box(0);
                        v_isShared_5114_ = v_isSharedCheck_5118_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5097_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1;
                v___x_5098_ = l_Lean_mkConst(v___x_5097_, v___x_5079_);
                v___x_5099_ = l_Lean_mkApp3(v___x_5098_, v_arg_5066_, v_val_5088_, v_arg_5061_);
                if v_isShared_5091_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5090_, 0, v___x_5099_);
                    v___x_5101_ = v___x_5090_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5099_);
                    v___x_5101_ = v_reuseFailAlloc_5109_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5102_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5102_, 0, v_a_5093_);
                crate::leanh::lean_ctor_set(v___x_5102_, 1, v___x_5101_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5102_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5069_,
                );
                if v_isShared_5078_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5077_, 0);
                    crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5102_);
                    v___x_5104_ = v___x_5077_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5102_);
                    v___x_5104_ = v_reuseFailAlloc_5108_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5095_, 0, v___x_5104_);
                    v___x_5106_ = v___x_5095_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5104_);
                    v___x_5106_ = v_reuseFailAlloc_5107_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5106_;
            }
            10 => {
                if v_isShared_5114_ == 0 {
                    v___x_5116_ = v___x_5113_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
                    v___x_5116_ = v_reuseFailAlloc_5117_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5116_;
            }
            12 => {
                return v___x_5122_;
            }
            13 => {
                if v_isShared_5128_ == 0 {
                    v___x_5130_ = v___x_5127_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
                    v___x_5130_ = v_reuseFailAlloc_5131_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5130_;
            }
            15 => {
                return v___x_5136_;
            }
            16 => {
                if v_isShared_5142_ == 0 {
                    v___x_5144_ = v___x_5141_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
                    v___x_5144_ = v_reuseFailAlloc_5145_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___boxed(
    mut v_e_5147_: *mut crate::leanh::LeanObject,
    mut v_a_5148_: *mut crate::leanh::LeanObject,
    mut v_a_5149_: *mut crate::leanh::LeanObject,
    mut v_a_5150_: *mut crate::leanh::LeanObject,
    mut v_a_5151_: *mut crate::leanh::LeanObject,
    mut v_a_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5153_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(
        v_e_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_,
    );
    crate::leanh::lean_dec(v_a_5151_);
    crate::leanh::lean_dec_ref(v_a_5150_);
    crate::leanh::lean_dec(v_a_5149_);
    crate::leanh::lean_dec_ref(v_a_5148_);
    return v_res_5153_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastNum(
    mut v_e_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
    mut v_a_5156_: *mut crate::leanh::LeanObject,
    mut v_a_5157_: *mut crate::leanh::LeanObject,
    mut v_a_5158_: *mut crate::leanh::LeanObject,
    mut v_a_5159_: *mut crate::leanh::LeanObject,
    mut v_a_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(
        v_e_5154_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_,
    );
    return v___x_5163_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normNatCastNum___boxed(
    mut v_e_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
    mut v_a_5166_: *mut crate::leanh::LeanObject,
    mut v_a_5167_: *mut crate::leanh::LeanObject,
    mut v_a_5168_: *mut crate::leanh::LeanObject,
    mut v_a_5169_: *mut crate::leanh::LeanObject,
    mut v_a_5170_: *mut crate::leanh::LeanObject,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
    mut v_a_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5173_ = l_Lean_Meta_Grind_Arith_normNatCastNum(
        v_e_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_,
    );
    crate::leanh::lean_dec(v_a_5171_);
    crate::leanh::lean_dec_ref(v_a_5170_);
    crate::leanh::lean_dec(v_a_5169_);
    crate::leanh::lean_dec_ref(v_a_5168_);
    crate::leanh::lean_dec(v_a_5167_);
    crate::leanh::lean_dec_ref(v_a_5166_);
    crate::leanh::lean_dec(v_a_5165_);
    return v_res_5173_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_;
    v___x_5191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_;
    v___x_5192_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normNatCastNum___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5193_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5190_, v___x_5191_, v___x_5192_);
    return v___x_5193_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10____boxed(
    mut v_a_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_();
    return v_res_5195_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5207_ = lean_nat_to_int(v___x_5206_);
    return v___x_5207_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(
    mut v_e_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v_arg_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: u8 = 0;
    let mut v_arg_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v_val_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5250_: u8 = 0;
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v_val_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v_val_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5320_: u8 = 0;
    let mut v_a_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5324_: u8 = 0;
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_isSharedCheck_5329_: u8 = 0;
    let mut v_a_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut v_a_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5231_ = l_Lean_Expr_cleanupAnnotations(v_e_5222_);
                v___x_5232_ = l_Lean_Expr_isApp(v___x_5231_);
                if v___x_5232_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5231_);
                    state = 1;
                    continue;
                } else {
                    v_arg_5233_ = crate::leanh::lean_ctor_get(v___x_5231_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5233_);
                    v___x_5234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5231_);
                    v___x_5235_ = l_Lean_Expr_isApp(v___x_5234_);
                    if v___x_5235_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5234_);
                        crate::leanh::lean_dec_ref(v_arg_5233_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5234_);
                        v___x_5237_ = l_Lean_Expr_isApp(v___x_5236_);
                        if v___x_5237_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5236_);
                            crate::leanh::lean_dec_ref(v_arg_5233_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_5238_ = crate::leanh::lean_ctor_get(v___x_5236_, 1);
                            crate::leanh::lean_inc_ref(v_arg_5238_);
                            v___x_5239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5236_);
                            v___x_5240_ =
                                l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2;
                            v___x_5241_ = l_Lean_Expr_isConstOf(v___x_5239_, v___x_5240_);
                            if v___x_5241_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5239_);
                                crate::leanh::lean_dec_ref(v_arg_5238_);
                                crate::leanh::lean_dec_ref(v_arg_5233_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_arg_5233_);
                                v___x_5242_ = l_Lean_Meta_getIntValue_x3f(
                                    v_arg_5233_,
                                    v_a_5223_,
                                    v_a_5224_,
                                    v_a_5225_,
                                    v_a_5226_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5242_) == 0 {
                                    v_a_5243_ = crate::leanh::lean_ctor_get(v___x_5242_, 0);
                                    v_isSharedCheck_5357_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5242_)) as u8;
                                    if v_isSharedCheck_5357_ == 0 {
                                        v___x_5245_ = v___x_5242_;
                                        v_isShared_5246_ = v_isSharedCheck_5357_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5243_);
                                        crate::leanh::lean_dec(v___x_5242_);
                                        v___x_5245_ = crate::leanh::lean_box(0);
                                        v_isShared_5246_ = v_isSharedCheck_5357_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5239_);
                                    crate::leanh::lean_dec_ref(v_arg_5238_);
                                    crate::leanh::lean_dec_ref(v_arg_5233_);
                                    v_a_5358_ = crate::leanh::lean_ctor_get(v___x_5242_, 0);
                                    v_isSharedCheck_5365_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5242_)) as u8;
                                    if v_isSharedCheck_5365_ == 0 {
                                        v___x_5360_ = v___x_5242_;
                                        v_isShared_5361_ = v_isSharedCheck_5365_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5358_);
                                        crate::leanh::lean_dec(v___x_5242_);
                                        v___x_5360_ = crate::leanh::lean_box(0);
                                        v_isShared_5361_ = v_isSharedCheck_5365_;
                                        state = 24;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5229_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                v___x_5230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5230_, 0, v___x_5229_);
                return v___x_5230_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5243_) == 1 {
                    crate::leanh::lean_del_object(v___x_5245_);
                    v_val_5247_ = crate::leanh::lean_ctor_get(v_a_5243_, 0);
                    v_isSharedCheck_5352_ = (!crate::leanh::lean_is_exclusive(v_a_5243_)) as u8;
                    if v_isSharedCheck_5352_ == 0 {
                        v___x_5249_ = v_a_5243_;
                        v_isShared_5250_ = v_isSharedCheck_5352_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5247_);
                        crate::leanh::lean_dec(v_a_5243_);
                        v___x_5249_ = crate::leanh::lean_box(0);
                        v_isShared_5250_ = v_isSharedCheck_5352_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5243_);
                    crate::leanh::lean_dec_ref(v___x_5239_);
                    crate::leanh::lean_dec_ref(v_arg_5238_);
                    crate::leanh::lean_dec_ref(v_arg_5233_);
                    v___x_5353_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_5246_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5245_, 0, v___x_5353_);
                        v___x_5355_ = v___x_5245_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_5356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
                        v___x_5355_ = v_reuseFailAlloc_5356_;
                        state = 23;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5251_ = l_Lean_Expr_constLevels_x21(v___x_5239_);
                crate::leanh::lean_dec_ref(v___x_5239_);
                v___x_5252_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4;
                crate::leanh::lean_inc(v___x_5251_);
                v___x_5253_ = l_Lean_mkConst(v___x_5252_, v___x_5251_);
                crate::leanh::lean_inc_ref(v_arg_5238_);
                v___x_5254_ = l_Lean_Expr_app___override(v___x_5253_, v_arg_5238_);
                v___x_5255_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_5254_,
                    v_a_5223_,
                    v_a_5224_,
                    v_a_5225_,
                    v_a_5226_,
                );
                if crate::leanh::lean_obj_tag(v___x_5255_) == 0 {
                    v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                    v_isSharedCheck_5343_ = (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                    if v_isSharedCheck_5343_ == 0 {
                        v___x_5258_ = v___x_5255_;
                        v_isShared_5259_ = v_isSharedCheck_5343_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5256_);
                        crate::leanh::lean_dec(v___x_5255_);
                        v___x_5258_ = crate::leanh::lean_box(0);
                        v_isShared_5259_ = v_isSharedCheck_5343_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5251_);
                    crate::leanh::lean_del_object(v___x_5249_);
                    crate::leanh::lean_dec(v_val_5247_);
                    crate::leanh::lean_dec_ref(v_arg_5238_);
                    crate::leanh::lean_dec_ref(v_arg_5233_);
                    v_a_5344_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                    v_isSharedCheck_5351_ = (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                    if v_isSharedCheck_5351_ == 0 {
                        v___x_5346_ = v___x_5255_;
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5344_);
                        crate::leanh::lean_dec(v___x_5255_);
                        v___x_5346_ = crate::leanh::lean_box(0);
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 21;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_5256_) == 1 {
                    crate::leanh::lean_del_object(v___x_5258_);
                    v_val_5260_ = crate::leanh::lean_ctor_get(v_a_5256_, 0);
                    v_isSharedCheck_5338_ = (!crate::leanh::lean_is_exclusive(v_a_5256_)) as u8;
                    if v_isSharedCheck_5338_ == 0 {
                        v___x_5262_ = v_a_5256_;
                        v_isShared_5263_ = v_isSharedCheck_5338_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5260_);
                        crate::leanh::lean_dec(v_a_5256_);
                        v___x_5262_ = crate::leanh::lean_box(0);
                        v_isShared_5263_ = v_isSharedCheck_5338_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5256_);
                    crate::leanh::lean_dec(v___x_5251_);
                    crate::leanh::lean_del_object(v___x_5249_);
                    crate::leanh::lean_dec(v_val_5247_);
                    crate::leanh::lean_dec_ref(v_arg_5238_);
                    crate::leanh::lean_dec_ref(v_arg_5233_);
                    v___x_5339_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_5259_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5258_, 0, v___x_5339_);
                        v___x_5341_ = v___x_5258_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5339_);
                        v___x_5341_ = v_reuseFailAlloc_5342_;
                        state = 20;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5264_ = lean_nat_abs(v_val_5247_);
                crate::leanh::lean_inc_ref(v_arg_5238_);
                v___x_5265_ = l_Lean_Meta_mkNumeral(
                    v_arg_5238_,
                    v___x_5264_,
                    v_a_5223_,
                    v_a_5224_,
                    v_a_5225_,
                    v_a_5226_,
                );
                if crate::leanh::lean_obj_tag(v___x_5265_) == 0 {
                    v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5329_ = (!crate::leanh::lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5329_ == 0 {
                        v___x_5268_ = v___x_5265_;
                        v_isShared_5269_ = v_isSharedCheck_5329_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5266_);
                        crate::leanh::lean_dec(v___x_5265_);
                        v___x_5268_ = crate::leanh::lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5329_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5262_);
                    crate::leanh::lean_dec(v_val_5260_);
                    crate::leanh::lean_dec(v___x_5251_);
                    crate::leanh::lean_del_object(v___x_5249_);
                    crate::leanh::lean_dec(v_val_5247_);
                    crate::leanh::lean_dec_ref(v_arg_5238_);
                    crate::leanh::lean_dec_ref(v_arg_5233_);
                    v_a_5330_ = crate::leanh::lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5337_ = (!crate::leanh::lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5337_ == 0 {
                        v___x_5332_ = v___x_5265_;
                        v_isShared_5333_ = v_isSharedCheck_5337_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5330_);
                        crate::leanh::lean_dec(v___x_5265_);
                        v___x_5332_ = crate::leanh::lean_box(0);
                        v_isShared_5333_ = v_isSharedCheck_5337_;
                        state = 18;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5270_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5,
                );
                v___x_5271_ = lean_int_dec_lt(v_val_5247_, v___x_5270_);
                crate::leanh::lean_dec(v_val_5247_);
                if v___x_5271_ == 0 {
                    v___x_5272_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7;
                    v___x_5273_ = l_Lean_mkConst(v___x_5272_, v___x_5251_);
                    v___x_5274_ = l_Lean_eagerReflBoolTrue;
                    v___x_5275_ = l_Lean_mkApp4(
                        v___x_5273_,
                        v_arg_5238_,
                        v_val_5260_,
                        v_arg_5233_,
                        v___x_5274_,
                    );
                    if v_isShared_5263_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5262_, 0, v___x_5275_);
                        v___x_5277_ = v___x_5262_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5275_);
                        v___x_5277_ = v_reuseFailAlloc_5285_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5268_);
                    crate::leanh::lean_del_object(v___x_5262_);
                    v___x_5286_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8;
                    crate::leanh::lean_inc(v___x_5251_);
                    v___x_5287_ = l_Lean_mkConst(v___x_5286_, v___x_5251_);
                    crate::leanh::lean_inc_ref(v_arg_5238_);
                    v___x_5288_ = l_Lean_Expr_app___override(v___x_5287_, v_arg_5238_);
                    v___x_5289_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_5288_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5289_) == 0 {
                        v_a_5290_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                        v_isSharedCheck_5320_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                        if v_isSharedCheck_5320_ == 0 {
                            v___x_5292_ = v___x_5289_;
                            v_isShared_5293_ = v_isSharedCheck_5320_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5290_);
                            crate::leanh::lean_dec(v___x_5289_);
                            v___x_5292_ = crate::leanh::lean_box(0);
                            v_isShared_5293_ = v_isSharedCheck_5320_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5266_);
                        crate::leanh::lean_dec(v_val_5260_);
                        crate::leanh::lean_dec(v___x_5251_);
                        crate::leanh::lean_del_object(v___x_5249_);
                        crate::leanh::lean_dec_ref(v_arg_5238_);
                        crate::leanh::lean_dec_ref(v_arg_5233_);
                        v_a_5321_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                        v_isSharedCheck_5328_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                        if v_isSharedCheck_5328_ == 0 {
                            v___x_5323_ = v___x_5289_;
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5321_);
                            crate::leanh::lean_dec(v___x_5289_);
                            v___x_5323_ = crate::leanh::lean_box(0);
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_5278_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5278_, 0, v_a_5266_);
                crate::leanh::lean_ctor_set(v___x_5278_, 1, v___x_5277_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5278_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5241_,
                );
                if v_isShared_5250_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5249_, 0);
                    crate::leanh::lean_ctor_set(v___x_5249_, 0, v___x_5278_);
                    v___x_5280_ = v___x_5249_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5278_);
                    v___x_5280_ = v_reuseFailAlloc_5284_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5280_);
                    v___x_5282_ = v___x_5268_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5282_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_5290_) == 1 {
                    v_val_5294_ = crate::leanh::lean_ctor_get(v_a_5290_, 0);
                    v_isSharedCheck_5315_ = (!crate::leanh::lean_is_exclusive(v_a_5290_)) as u8;
                    if v_isSharedCheck_5315_ == 0 {
                        v___x_5296_ = v_a_5290_;
                        v_isShared_5297_ = v_isSharedCheck_5315_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5294_);
                        crate::leanh::lean_dec(v_a_5290_);
                        v___x_5296_ = crate::leanh::lean_box(0);
                        v_isShared_5297_ = v_isSharedCheck_5315_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5290_);
                    crate::leanh::lean_dec(v_a_5266_);
                    crate::leanh::lean_dec(v_val_5260_);
                    crate::leanh::lean_dec(v___x_5251_);
                    crate::leanh::lean_del_object(v___x_5249_);
                    crate::leanh::lean_dec_ref(v_arg_5238_);
                    crate::leanh::lean_dec_ref(v_arg_5233_);
                    v___x_5316_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0;
                    if v_isShared_5293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5292_, 0, v___x_5316_);
                        v___x_5318_ = v___x_5292_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5316_);
                        v___x_5318_ = v_reuseFailAlloc_5319_;
                        state = 15;
                        continue;
                    }
                }
            }
            11 => {
                v___x_5298_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_;
                crate::leanh::lean_inc(v___x_5251_);
                v___x_5299_ = l_Lean_mkConst(v___x_5298_, v___x_5251_);
                crate::leanh::lean_inc_ref(v_arg_5238_);
                v___x_5300_ = l_Lean_mkApp3(v___x_5299_, v_arg_5238_, v_val_5294_, v_a_5266_);
                v___x_5301_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10;
                v___x_5302_ = l_Lean_mkConst(v___x_5301_, v___x_5251_);
                v___x_5303_ = l_Lean_eagerReflBoolTrue;
                v___x_5304_ = l_Lean_mkApp4(
                    v___x_5302_,
                    v_arg_5238_,
                    v_val_5260_,
                    v_arg_5233_,
                    v___x_5303_,
                );
                if v_isShared_5297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5296_, 0, v___x_5304_);
                    v___x_5306_ = v___x_5296_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5304_);
                    v___x_5306_ = v_reuseFailAlloc_5314_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5307_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5307_, 0, v___x_5300_);
                crate::leanh::lean_ctor_set(v___x_5307_, 1, v___x_5306_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5307_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5241_,
                );
                if v_isShared_5250_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5249_, 0);
                    crate::leanh::lean_ctor_set(v___x_5249_, 0, v___x_5307_);
                    v___x_5309_ = v___x_5249_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5307_);
                    v___x_5309_ = v_reuseFailAlloc_5313_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5292_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5292_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
                    v___x_5311_ = v_reuseFailAlloc_5312_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5311_;
            }
            15 => {
                return v___x_5318_;
            }
            16 => {
                if v_isShared_5324_ == 0 {
                    v___x_5326_ = v___x_5323_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
                    v___x_5326_ = v_reuseFailAlloc_5327_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5326_;
            }
            18 => {
                if v_isShared_5333_ == 0 {
                    v___x_5335_ = v___x_5332_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
                    v___x_5335_ = v_reuseFailAlloc_5336_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5335_;
            }
            20 => {
                return v___x_5341_;
            }
            21 => {
                if v_isShared_5347_ == 0 {
                    v___x_5349_ = v___x_5346_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5349_;
            }
            23 => {
                return v___x_5355_;
            }
            24 => {
                if v_isShared_5361_ == 0 {
                    v___x_5363_ = v___x_5360_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___boxed(
    mut v_e_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5372_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(
        v_e_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_,
    );
    crate::leanh::lean_dec(v_a_5370_);
    crate::leanh::lean_dec_ref(v_a_5369_);
    crate::leanh::lean_dec(v_a_5368_);
    crate::leanh::lean_dec_ref(v_a_5367_);
    return v_res_5372_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntCastNum(
    mut v_e_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
    mut v_a_5376_: *mut crate::leanh::LeanObject,
    mut v_a_5377_: *mut crate::leanh::LeanObject,
    mut v_a_5378_: *mut crate::leanh::LeanObject,
    mut v_a_5379_: *mut crate::leanh::LeanObject,
    mut v_a_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5382_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(
        v_e_5373_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_,
    );
    return v___x_5382_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normIntCastNum___boxed(
    mut v_e_5383_: *mut crate::leanh::LeanObject,
    mut v_a_5384_: *mut crate::leanh::LeanObject,
    mut v_a_5385_: *mut crate::leanh::LeanObject,
    mut v_a_5386_: *mut crate::leanh::LeanObject,
    mut v_a_5387_: *mut crate::leanh::LeanObject,
    mut v_a_5388_: *mut crate::leanh::LeanObject,
    mut v_a_5389_: *mut crate::leanh::LeanObject,
    mut v_a_5390_: *mut crate::leanh::LeanObject,
    mut v_a_5391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5392_ = l_Lean_Meta_Grind_Arith_normIntCastNum(
        v_e_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_,
    );
    crate::leanh::lean_dec(v_a_5390_);
    crate::leanh::lean_dec_ref(v_a_5389_);
    crate::leanh::lean_dec(v_a_5388_);
    crate::leanh::lean_dec_ref(v_a_5387_);
    crate::leanh::lean_dec(v_a_5386_);
    crate::leanh::lean_dec_ref(v_a_5385_);
    crate::leanh::lean_dec(v_a_5384_);
    return v_res_5392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_;
    v___x_5413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_;
    v___x_5414_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normIntCastNum___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5415_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5412_, v___x_5413_, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10____boxed(
    mut v_a_5416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_();
    return v_res_5417_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_normPowRatInt_spec__0(
    mut v_a_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5419_ = lean_nat_to_int(v_a_5418_);
    return v___x_5419_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5420_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5421_ = l_Lean_Level_ofNat(v___x_5420_);
    return v___x_5421_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5422_ = crate::leanh::lean_box(0);
    v___x_5423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0,
    );
    v___x_5424_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5424_, 0, v___x_5423_);
    crate::leanh::lean_ctor_set(v___x_5424_, 1, v___x_5422_);
    return v___x_5424_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1,
    );
    v___x_5426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0,
    );
    v___x_5427_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5427_, 0, v___x_5426_);
    crate::leanh::lean_ctor_set(v___x_5427_, 1, v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5428_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2,
    );
    v___x_5429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0,
    );
    v___x_5430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5430_, 0, v___x_5429_);
    crate::leanh::lean_ctor_set(v___x_5430_, 1, v___x_5428_);
    return v___x_5430_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3,
    );
    v___x_5432_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2;
    v___x_5433_ = l_Lean_Expr_const___override(v___x_5432_, v___x_5431_);
    return v___x_5433_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5437_ = crate::leanh::lean_box(0);
    v___x_5438_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6;
    v___x_5439_ = l_Lean_Expr_const___override(v___x_5438_, v___x_5437_);
    return v___x_5439_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1,
    );
    v___x_5444_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9;
    v___x_5445_ = l_Lean_Expr_const___override(v___x_5444_, v___x_5443_);
    return v___x_5445_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5450_ = crate::leanh::lean_box(0);
    v___x_5451_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12;
    v___x_5452_ = l_Lean_Expr_const___override(v___x_5451_, v___x_5450_);
    return v___x_5452_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13,
    );
    v___x_5454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7,
    );
    v___x_5455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10_once),
        _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10,
    );
    v___x_5456_ = l_Lean_mkAppB(v___x_5455_, v___x_5454_, v___x_5453_);
    return v___x_5456_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(
    mut v_e_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v_a_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
    mut v_a_5462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5468_: u8 = 0;
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u8 = 0;
    let mut v_arg_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: u8 = 0;
    let mut v_arg_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: u8 = 0;
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: u8 = 0;
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: u8 = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v_val_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5501_: u8 = 0;
    let mut v_config_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v_warnExponents_5507_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___y_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: u8 = 0;
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5546_: u8 = 0;
    let mut v_a_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5573_: u8 = 0;
    let mut v_a_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_a_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5464_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5457_, v_a_5460_);
                if crate::leanh::lean_obj_tag(v___x_5464_) == 0 {
                    v_a_5465_ = crate::leanh::lean_ctor_get(v___x_5464_, 0);
                    v_isSharedCheck_5582_ = (!crate::leanh::lean_is_exclusive(v___x_5464_)) as u8;
                    if v_isSharedCheck_5582_ == 0 {
                        v___x_5467_ = v___x_5464_;
                        v_isShared_5468_ = v_isSharedCheck_5582_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5465_);
                        crate::leanh::lean_dec(v___x_5464_);
                        v___x_5467_ = crate::leanh::lean_box(0);
                        v_isShared_5468_ = v_isSharedCheck_5582_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5583_ = crate::leanh::lean_ctor_get(v___x_5464_, 0);
                    v_isSharedCheck_5590_ = (!crate::leanh::lean_is_exclusive(v___x_5464_)) as u8;
                    if v_isSharedCheck_5590_ == 0 {
                        v___x_5585_ = v___x_5464_;
                        v_isShared_5586_ = v_isSharedCheck_5590_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5583_);
                        crate::leanh::lean_dec(v___x_5464_);
                        v___x_5585_ = crate::leanh::lean_box(0);
                        v_isShared_5586_ = v_isSharedCheck_5590_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5474_ = l_Lean_Expr_cleanupAnnotations(v_a_5465_);
                v___x_5475_ = l_Lean_Expr_isApp(v___x_5474_);
                if v___x_5475_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5474_);
                    state = 2;
                    continue;
                } else {
                    v_arg_5476_ = crate::leanh::lean_ctor_get(v___x_5474_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5476_);
                    v___x_5477_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5474_);
                    v___x_5478_ = l_Lean_Expr_isApp(v___x_5477_);
                    if v___x_5478_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5477_);
                        crate::leanh::lean_dec_ref(v_arg_5476_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_5479_ = crate::leanh::lean_ctor_get(v___x_5477_, 1);
                        crate::leanh::lean_inc_ref(v_arg_5479_);
                        v___x_5480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5477_);
                        v___x_5481_ = l_Lean_Expr_isApp(v___x_5480_);
                        if v___x_5481_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5480_);
                            crate::leanh::lean_dec_ref(v_arg_5479_);
                            crate::leanh::lean_dec_ref(v_arg_5476_);
                            state = 2;
                            continue;
                        } else {
                            v___x_5482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5480_);
                            v___x_5483_ = l_Lean_Expr_isApp(v___x_5482_);
                            if v___x_5483_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5482_);
                                crate::leanh::lean_dec_ref(v_arg_5479_);
                                crate::leanh::lean_dec_ref(v_arg_5476_);
                                state = 2;
                                continue;
                            } else {
                                v___x_5484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5482_);
                                v___x_5485_ = l_Lean_Expr_isApp(v___x_5484_);
                                if v___x_5485_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_5484_);
                                    crate::leanh::lean_dec_ref(v_arg_5479_);
                                    crate::leanh::lean_dec_ref(v_arg_5476_);
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_5486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5484_);
                                    v___x_5487_ = l_Lean_Expr_isApp(v___x_5486_);
                                    if v___x_5487_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_5486_);
                                        crate::leanh::lean_dec_ref(v_arg_5479_);
                                        crate::leanh::lean_dec_ref(v_arg_5476_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_5488_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_5486_);
                                        v___x_5489_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3;
                                        v___x_5490_ =
                                            l_Lean_Expr_isConstOf(v___x_5488_, v___x_5489_);
                                        crate::leanh::lean_dec_ref(v___x_5488_);
                                        if v___x_5490_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_5479_);
                                            crate::leanh::lean_dec_ref(v_arg_5476_);
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_del_object(v___x_5467_);
                                            v___x_5491_ = l_Lean_Meta_getRatValue_x3f(
                                                v_arg_5479_,
                                                v_a_5459_,
                                                v_a_5460_,
                                                v_a_5461_,
                                                v_a_5462_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_5491_) == 0 {
                                                v_a_5492_ =
                                                    crate::leanh::lean_ctor_get(v___x_5491_, 0);
                                                v_isSharedCheck_5573_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5491_))
                                                        as u8;
                                                if v_isSharedCheck_5573_ == 0 {
                                                    v___x_5494_ = v___x_5491_;
                                                    v_isShared_5495_ = v_isSharedCheck_5573_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5492_);
                                                    crate::leanh::lean_dec(v___x_5491_);
                                                    v___x_5494_ = crate::leanh::lean_box(0);
                                                    v_isShared_5495_ = v_isSharedCheck_5573_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_5476_);
                                                v_a_5574_ =
                                                    crate::leanh::lean_ctor_get(v___x_5491_, 0);
                                                v_isSharedCheck_5581_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5491_))
                                                        as u8;
                                                if v_isSharedCheck_5581_ == 0 {
                                                    v___x_5576_ = v___x_5491_;
                                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5574_);
                                                    crate::leanh::lean_dec(v___x_5491_);
                                                    v___x_5576_ = crate::leanh::lean_box(0);
                                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                                    state = 19;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_5470_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                if v_isShared_5468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5467_, 0, v___x_5470_);
                    v___x_5472_ = v___x_5467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5470_);
                    v___x_5472_ = v_reuseFailAlloc_5473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5472_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_5492_) == 1 {
                    crate::leanh::lean_del_object(v___x_5494_);
                    v_val_5496_ = crate::leanh::lean_ctor_get(v_a_5492_, 0);
                    crate::leanh::lean_inc(v_val_5496_);
                    crate::leanh::lean_dec_ref_known(v_a_5492_, 1);
                    v___x_5497_ = l_Lean_Meta_getIntValue_x3f(
                        v_arg_5476_,
                        v_a_5459_,
                        v_a_5460_,
                        v_a_5461_,
                        v_a_5462_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5497_) == 0 {
                        v_a_5498_ = crate::leanh::lean_ctor_get(v___x_5497_, 0);
                        v_isSharedCheck_5560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5497_)) as u8;
                        if v_isSharedCheck_5560_ == 0 {
                            v___x_5500_ = v___x_5497_;
                            v_isShared_5501_ = v_isSharedCheck_5560_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5498_);
                            crate::leanh::lean_dec(v___x_5497_);
                            v___x_5500_ = crate::leanh::lean_box(0);
                            v_isShared_5501_ = v_isSharedCheck_5560_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5496_);
                        v_a_5561_ = crate::leanh::lean_ctor_get(v___x_5497_, 0);
                        v_isSharedCheck_5568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5497_)) as u8;
                        if v_isSharedCheck_5568_ == 0 {
                            v___x_5563_ = v___x_5497_;
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5561_);
                            crate::leanh::lean_dec(v___x_5497_);
                            v___x_5563_ = crate::leanh::lean_box(0);
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5492_);
                    crate::leanh::lean_dec_ref(v_arg_5476_);
                    v___x_5569_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    if v_isShared_5495_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5494_, 0, v___x_5569_);
                        v___x_5571_ = v___x_5494_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5569_);
                        v___x_5571_ = v_reuseFailAlloc_5572_;
                        state = 18;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_5498_) == 1 {
                    v_config_5502_ = crate::leanh::lean_ctor_get(v_a_5458_, 0);
                    v_val_5503_ = crate::leanh::lean_ctor_get(v_a_5498_, 0);
                    v_isSharedCheck_5555_ = (!crate::leanh::lean_is_exclusive(v_a_5498_)) as u8;
                    if v_isSharedCheck_5555_ == 0 {
                        v___x_5505_ = v_a_5498_;
                        v_isShared_5506_ = v_isSharedCheck_5555_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5503_);
                        crate::leanh::lean_dec(v_a_5498_);
                        v___x_5505_ = crate::leanh::lean_box(0);
                        v_isShared_5506_ = v_isSharedCheck_5555_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5498_);
                    crate::leanh::lean_dec(v_val_5496_);
                    v___x_5556_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    if v_isShared_5501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5500_, 0, v___x_5556_);
                        v___x_5558_ = v___x_5500_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
                        v___x_5558_ = v_reuseFailAlloc_5559_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_warnExponents_5507_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_5502_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                );
                v___x_5508_ = lean_nat_abs(v_val_5503_);
                v___x_5509_ =
                    l_Lean_checkExponent(v___x_5508_, v_warnExponents_5507_, v_a_5461_, v_a_5462_);
                if crate::leanh::lean_obj_tag(v___x_5509_) == 0 {
                    v_a_5510_ = crate::leanh::lean_ctor_get(v___x_5509_, 0);
                    v_isSharedCheck_5546_ = (!crate::leanh::lean_is_exclusive(v___x_5509_)) as u8;
                    if v_isSharedCheck_5546_ == 0 {
                        v___x_5512_ = v___x_5509_;
                        v_isShared_5513_ = v_isSharedCheck_5546_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5510_);
                        crate::leanh::lean_dec(v___x_5509_);
                        v___x_5512_ = crate::leanh::lean_box(0);
                        v_isShared_5513_ = v_isSharedCheck_5546_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5505_);
                    crate::leanh::lean_dec(v_val_5503_);
                    crate::leanh::lean_del_object(v___x_5500_);
                    crate::leanh::lean_dec(v_val_5496_);
                    v_a_5547_ = crate::leanh::lean_ctor_get(v___x_5509_, 0);
                    v_isSharedCheck_5554_ = (!crate::leanh::lean_is_exclusive(v___x_5509_)) as u8;
                    if v_isSharedCheck_5554_ == 0 {
                        v___x_5549_ = v___x_5509_;
                        v_isShared_5550_ = v_isSharedCheck_5554_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5547_);
                        crate::leanh::lean_dec(v___x_5509_);
                        v___x_5549_ = crate::leanh::lean_box(0);
                        v_isShared_5550_ = v_isSharedCheck_5554_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_5522_ = (crate::leanh::lean_unbox(v_a_5510_) as u8);
                crate::leanh::lean_dec(v_a_5510_);
                if v___x_5522_ == 0 {
                    crate::leanh::lean_del_object(v___x_5512_);
                    crate::leanh::lean_del_object(v___x_5505_);
                    crate::leanh::lean_dec(v_val_5503_);
                    crate::leanh::lean_dec(v_val_5496_);
                    v___x_5523_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                    if v_isShared_5501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5500_, 0, v___x_5523_);
                        v___x_5525_ = v___x_5500_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5523_);
                        v___x_5525_ = v_reuseFailAlloc_5526_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_5527_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5,
                    );
                    v___x_5528_ = lean_int_dec_lt(v_val_5503_, v___x_5527_);
                    if v___x_5528_ == 0 {
                        crate::leanh::lean_del_object(v___x_5500_);
                        v___x_5529_ = l_Rat_zpow(v_val_5496_, v_val_5503_);
                        crate::leanh::lean_dec(v_val_5503_);
                        v_num_5530_ = crate::leanh::lean_ctor_get(v___x_5529_, 0);
                        crate::leanh::lean_inc(v_num_5530_);
                        v_den_5531_ = crate::leanh::lean_ctor_get(v___x_5529_, 1);
                        crate::leanh::lean_inc(v_den_5531_);
                        crate::leanh::lean_dec_ref(v___x_5529_);
                        v___x_5532_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5533_ = lean_nat_dec_eq(v_den_5531_, v___x_5532_);
                        if v___x_5533_ == 0 {
                            v___x_5534_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4_once
                                ),
                                _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4,
                            );
                            v___x_5535_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once
                                ),
                                _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7,
                            );
                            v___x_5536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14_once), _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14);
                            v___x_5537_ = l_Lean_instToExprRat_mkInt(v_num_5530_);
                            crate::leanh::lean_dec(v_num_5530_);
                            v___x_5538_ = lean_nat_to_int(v_den_5531_);
                            v___x_5539_ = l_Lean_instToExprRat_mkInt(v___x_5538_);
                            crate::leanh::lean_dec(v___x_5538_);
                            v___x_5540_ = l_Lean_mkApp6(
                                v___x_5534_,
                                v___x_5535_,
                                v___x_5535_,
                                v___x_5535_,
                                v___x_5536_,
                                v___x_5537_,
                                v___x_5539_,
                            );
                            v___y_5515_ = v___x_5540_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_den_5531_);
                            v___x_5541_ = l_Lean_instToExprRat_mkInt(v_num_5530_);
                            crate::leanh::lean_dec(v_num_5530_);
                            v___y_5515_ = v___x_5541_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5512_);
                        crate::leanh::lean_del_object(v___x_5505_);
                        crate::leanh::lean_dec(v_val_5503_);
                        crate::leanh::lean_dec(v_val_5496_);
                        v___x_5542_ = l_Lean_Meta_Grind_Arith_normInst___closed__0;
                        if v_isShared_5501_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5500_, 0, v___x_5542_);
                            v___x_5544_ = v___x_5500_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_5545_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5542_);
                            v___x_5544_ = v_reuseFailAlloc_5545_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_5506_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5505_, 0);
                    crate::leanh::lean_ctor_set(v___x_5505_, 0, v___y_5515_);
                    v___x_5517_ = v___x_5505_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___y_5515_);
                    v___x_5517_ = v_reuseFailAlloc_5521_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5512_, 0, v___x_5517_);
                    v___x_5519_ = v___x_5512_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5517_);
                    v___x_5519_ = v_reuseFailAlloc_5520_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5519_;
            }
            11 => {
                return v___x_5525_;
            }
            12 => {
                return v___x_5544_;
            }
            13 => {
                if v_isShared_5550_ == 0 {
                    v___x_5552_ = v___x_5549_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
                    v___x_5552_ = v_reuseFailAlloc_5553_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5552_;
            }
            15 => {
                return v___x_5558_;
            }
            16 => {
                if v_isShared_5564_ == 0 {
                    v___x_5566_ = v___x_5563_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
                    v___x_5566_ = v_reuseFailAlloc_5567_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5566_;
            }
            18 => {
                return v___x_5571_;
            }
            19 => {
                if v_isShared_5577_ == 0 {
                    v___x_5579_ = v___x_5576_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5579_;
            }
            21 => {
                if v_isShared_5586_ == 0 {
                    v___x_5588_ = v___x_5585_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
                    v___x_5588_ = v_reuseFailAlloc_5589_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___boxed(
    mut v_e_5591_: *mut crate::leanh::LeanObject,
    mut v_a_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
    mut v_a_5594_: *mut crate::leanh::LeanObject,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5598_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(
        v_e_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_,
    );
    crate::leanh::lean_dec(v_a_5596_);
    crate::leanh::lean_dec_ref(v_a_5595_);
    crate::leanh::lean_dec(v_a_5594_);
    crate::leanh::lean_dec_ref(v_a_5593_);
    crate::leanh::lean_dec_ref(v_a_5592_);
    return v_res_5598_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normPowRatInt(
    mut v_e_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
    mut v_a_5601_: *mut crate::leanh::LeanObject,
    mut v_a_5602_: *mut crate::leanh::LeanObject,
    mut v_a_5603_: *mut crate::leanh::LeanObject,
    mut v_a_5604_: *mut crate::leanh::LeanObject,
    mut v_a_5605_: *mut crate::leanh::LeanObject,
    mut v_a_5606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5608_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(
        v_e_5599_, v_a_5601_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_,
    );
    return v___x_5608_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normPowRatInt___boxed(
    mut v_e_5609_: *mut crate::leanh::LeanObject,
    mut v_a_5610_: *mut crate::leanh::LeanObject,
    mut v_a_5611_: *mut crate::leanh::LeanObject,
    mut v_a_5612_: *mut crate::leanh::LeanObject,
    mut v_a_5613_: *mut crate::leanh::LeanObject,
    mut v_a_5614_: *mut crate::leanh::LeanObject,
    mut v_a_5615_: *mut crate::leanh::LeanObject,
    mut v_a_5616_: *mut crate::leanh::LeanObject,
    mut v_a_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Lean_Meta_Grind_Arith_normPowRatInt(
        v_e_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_,
    );
    crate::leanh::lean_dec(v_a_5616_);
    crate::leanh::lean_dec_ref(v_a_5615_);
    crate::leanh::lean_dec(v_a_5614_);
    crate::leanh::lean_dec_ref(v_a_5613_);
    crate::leanh::lean_dec(v_a_5612_);
    crate::leanh::lean_dec_ref(v_a_5611_);
    crate::leanh::lean_dec(v_a_5610_);
    return v_res_5618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5643_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_;
    v___x_5644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_;
    v___x_5645_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normPowRatInt___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5646_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5643_, v___x_5644_, v___x_5645_);
    return v___x_5646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23____boxed(
    mut v_a_5647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_();
    return v_res_5648_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5649_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_normPowRatInt___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5650_, 0, v___x_5649_);
    return v___x_5650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: u8 = 0;
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_;
    v___x_5653_ = 1;
    v___x_5654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_);
    v___x_5655_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5652_, v___x_5653_, v___x_5654_);
    return v___x_5655_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25____boxed(
    mut v_a_5656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_();
    return v_res_5657_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: u8 = 0;
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_;
    v___x_5660_ = 1;
    v___x_5661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_);
    v___x_5662_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5659_, v___x_5660_, v___x_5661_);
    return v___x_5662_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27____boxed(
    mut v_a_5663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_();
    return v_res_5664_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_addSimproc(
    mut v_s_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: u8 = 0;
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_;
    v___x_5670_ = 1;
    v___x_5671_ =
        l_Lean_Meta_Simp_Simprocs_add(v_s_5665_, v___x_5669_, v___x_5670_, v_a_5666_, v_a_5667_);
    if crate::leanh::lean_obj_tag(v___x_5671_) == 0 {
        let mut v_a_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5672_ = crate::leanh::lean_ctor_get(v___x_5671_, 0);
        crate::leanh::lean_inc(v_a_5672_);
        crate::leanh::lean_dec_ref_known(v___x_5671_, 1);
        v___x_5673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_;
        v___x_5674_ = l_Lean_Meta_Simp_Simprocs_add(
            v_a_5672_,
            v___x_5673_,
            v___x_5670_,
            v_a_5666_,
            v_a_5667_,
        );
        if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
            let mut v_a_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5677_: u8 = 0;
            let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5675_ = crate::leanh::lean_ctor_get(v___x_5674_, 0);
            crate::leanh::lean_inc(v_a_5675_);
            crate::leanh::lean_dec_ref_known(v___x_5674_, 1);
            v___x_5676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_;
            v___x_5677_ = 0;
            v___x_5678_ = l_Lean_Meta_Simp_Simprocs_add(
                v_a_5675_,
                v___x_5676_,
                v___x_5677_,
                v_a_5666_,
                v_a_5667_,
            );
            if crate::leanh::lean_obj_tag(v___x_5678_) == 0 {
                let mut v_a_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5679_ = crate::leanh::lean_ctor_get(v___x_5678_, 0);
                crate::leanh::lean_inc(v_a_5679_);
                crate::leanh::lean_dec_ref_known(v___x_5678_, 1);
                v___x_5680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_;
                v___x_5681_ = l_Lean_Meta_Simp_Simprocs_add(
                    v_a_5679_,
                    v___x_5680_,
                    v___x_5677_,
                    v_a_5666_,
                    v_a_5667_,
                );
                if crate::leanh::lean_obj_tag(v___x_5681_) == 0 {
                    let mut v_a_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_5682_ = crate::leanh::lean_ctor_get(v___x_5681_, 0);
                    crate::leanh::lean_inc(v_a_5682_);
                    crate::leanh::lean_dec_ref_known(v___x_5681_, 1);
                    v___x_5683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_;
                    v___x_5684_ = l_Lean_Meta_Simp_Simprocs_add(
                        v_a_5682_,
                        v___x_5683_,
                        v___x_5677_,
                        v_a_5666_,
                        v_a_5667_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5684_) == 0 {
                        let mut v_a_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_5685_ = crate::leanh::lean_ctor_get(v___x_5684_, 0);
                        crate::leanh::lean_inc(v_a_5685_);
                        crate::leanh::lean_dec_ref_known(v___x_5684_, 1);
                        v___x_5686_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_;
                        v___x_5687_ = l_Lean_Meta_Simp_Simprocs_add(
                            v_a_5685_,
                            v___x_5686_,
                            v___x_5677_,
                            v_a_5666_,
                            v_a_5667_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5687_) == 0 {
                            let mut v_a_5688_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5689_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5690_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_a_5688_ = crate::leanh::lean_ctor_get(v___x_5687_, 0);
                            crate::leanh::lean_inc(v_a_5688_);
                            crate::leanh::lean_dec_ref_known(v___x_5687_, 1);
                            v___x_5689_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_;
                            v___x_5690_ = l_Lean_Meta_Simp_Simprocs_add(
                                v_a_5688_,
                                v___x_5689_,
                                v___x_5677_,
                                v_a_5666_,
                                v_a_5667_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5690_) == 0 {
                                let mut v_a_5691_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5692_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5693_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_a_5691_ = crate::leanh::lean_ctor_get(v___x_5690_, 0);
                                crate::leanh::lean_inc(v_a_5691_);
                                crate::leanh::lean_dec_ref_known(v___x_5690_, 1);
                                v___x_5692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_;
                                v___x_5693_ = l_Lean_Meta_Simp_Simprocs_add(
                                    v_a_5691_,
                                    v___x_5692_,
                                    v___x_5677_,
                                    v_a_5666_,
                                    v_a_5667_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5693_) == 0 {
                                    let mut v_a_5694_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5695_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5696_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_a_5694_ = crate::leanh::lean_ctor_get(v___x_5693_, 0);
                                    crate::leanh::lean_inc(v_a_5694_);
                                    crate::leanh::lean_dec_ref_known(v___x_5693_, 1);
                                    v___x_5695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_;
                                    v___x_5696_ = l_Lean_Meta_Simp_Simprocs_add(
                                        v_a_5694_,
                                        v___x_5695_,
                                        v___x_5677_,
                                        v_a_5666_,
                                        v_a_5667_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5696_) == 0 {
                                        let mut v_a_5697_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_5698_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_5699_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_a_5697_ = crate::leanh::lean_ctor_get(v___x_5696_, 0);
                                        crate::leanh::lean_inc(v_a_5697_);
                                        crate::leanh::lean_dec_ref_known(v___x_5696_, 1);
                                        v___x_5698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_;
                                        v___x_5699_ = l_Lean_Meta_Simp_Simprocs_add(
                                            v_a_5697_,
                                            v___x_5698_,
                                            v___x_5677_,
                                            v_a_5666_,
                                            v_a_5667_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5699_) == 0 {
                                            let mut v_a_5700_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_5701_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_5702_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v_a_5700_ = crate::leanh::lean_ctor_get(v___x_5699_, 0);
                                            crate::leanh::lean_inc(v_a_5700_);
                                            crate::leanh::lean_dec_ref_known(v___x_5699_, 1);
                                            v___x_5701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_;
                                            v___x_5702_ = l_Lean_Meta_Simp_Simprocs_add(
                                                v_a_5700_,
                                                v___x_5701_,
                                                v___x_5677_,
                                                v_a_5666_,
                                                v_a_5667_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_5702_) == 0 {
                                                let mut v_a_5703_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_5704_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_5705_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v_a_5703_ =
                                                    crate::leanh::lean_ctor_get(v___x_5702_, 0);
                                                crate::leanh::lean_inc(v_a_5703_);
                                                crate::leanh::lean_dec_ref_known(v___x_5702_, 1);
                                                v___x_5704_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_;
                                                v___x_5705_ = l_Lean_Meta_Simp_Simprocs_add(
                                                    v_a_5703_,
                                                    v___x_5704_,
                                                    v___x_5677_,
                                                    v_a_5666_,
                                                    v_a_5667_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_5705_) == 0 {
                                                    let mut v_a_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    v_a_5706_ =
                                                        crate::leanh::lean_ctor_get(v___x_5705_, 0);
                                                    crate::leanh::lean_inc(v_a_5706_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_5705_,
                                                        1,
                                                    );
                                                    v___x_5707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_;
                                                    v___x_5708_ = l_Lean_Meta_Simp_Simprocs_add(
                                                        v_a_5706_,
                                                        v___x_5707_,
                                                        v___x_5677_,
                                                        v_a_5666_,
                                                        v_a_5667_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_5708_) == 0
                                                    {
                                                        let mut v_a_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        v_a_5709_ = crate::leanh::lean_ctor_get(
                                                            v___x_5708_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_5709_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_5708_,
                                                            1,
                                                        );
                                                        v___x_5710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_;
                                                        v___x_5711_ = l_Lean_Meta_Simp_Simprocs_add(
                                                            v_a_5709_,
                                                            v___x_5710_,
                                                            v___x_5677_,
                                                            v_a_5666_,
                                                            v_a_5667_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_5711_)
                                                            == 0
                                                        {
                                                            let mut v_a_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            v_a_5712_ = crate::leanh::lean_ctor_get(
                                                                v___x_5711_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_5712_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_5711_,
                                                                1,
                                                            );
                                                            v___x_5713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_;
                                                            v___x_5714_ =
                                                                l_Lean_Meta_Simp_Simprocs_add(
                                                                    v_a_5712_,
                                                                    v___x_5713_,
                                                                    v___x_5677_,
                                                                    v_a_5666_,
                                                                    v_a_5667_,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_5714_,
                                                            ) == 0
                                                            {
                                                                let mut v_a_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                v_a_5715_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5714_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_5715_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_5714_,
                                                                    1,
                                                                );
                                                                v___x_5716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_;
                                                                v___x_5717_ =
                                                                    l_Lean_Meta_Simp_Simprocs_add(
                                                                        v_a_5715_,
                                                                        v___x_5716_,
                                                                        v___x_5677_,
                                                                        v_a_5666_,
                                                                        v_a_5667_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_5717_,
                                                                ) == 0
                                                                {
                                                                    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    v_a_5718_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_5717_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_5718_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_5717_, 1);
                                                                    v___x_5719_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_;
                                                                    v___x_5720_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5718_, v___x_5719_, v___x_5677_, v_a_5666_, v_a_5667_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_5720_,
                                                                    ) == 0
                                                                    {
                                                                        let mut v_a_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                        v_a_5721_ = crate::leanh::lean_ctor_get(v___x_5720_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5721_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_5720_, 1);
                                                                        v___x_5722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_;
                                                                        v___x_5723_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5721_, v___x_5722_, v___x_5677_, v_a_5666_, v_a_5667_);
                                                                        if crate::leanh::lean_obj_tag(v___x_5723_) == 0 {
let mut v_a_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v_a_5724_ = crate::leanh::lean_ctor_get(v___x_5723_, 0);
crate::leanh::lean_inc(v_a_5724_);
crate::leanh::lean_dec_ref_known(v___x_5723_, 1);
v___x_5725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_;
v___x_5726_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5724_, v___x_5725_, v___x_5677_, v_a_5666_, v_a_5667_);
if crate::leanh::lean_obj_tag(v___x_5726_) == 0 {
let mut v_a_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v_a_5727_ = crate::leanh::lean_ctor_get(v___x_5726_, 0);
crate::leanh::lean_inc(v_a_5727_);
crate::leanh::lean_dec_ref_known(v___x_5726_, 1);
v___x_5728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_;
v___x_5729_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5727_, v___x_5728_, v___x_5677_, v_a_5666_, v_a_5667_);
if crate::leanh::lean_obj_tag(v___x_5729_) == 0 {
let mut v_a_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v_a_5730_ = crate::leanh::lean_ctor_get(v___x_5729_, 0);
crate::leanh::lean_inc(v_a_5730_);
crate::leanh::lean_dec_ref_known(v___x_5729_, 1);
v___x_5731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_;
v___x_5732_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5730_, v___x_5731_, v___x_5677_, v_a_5666_, v_a_5667_);
if crate::leanh::lean_obj_tag(v___x_5732_) == 0 {
let mut v_a_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut(); let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
v_a_5733_ = crate::leanh::lean_ctor_get(v___x_5732_, 0);
crate::leanh::lean_inc(v_a_5733_);
crate::leanh::lean_dec_ref_known(v___x_5732_, 1);
v___x_5734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_;
v___x_5735_ = l_Lean_Meta_Simp_Simprocs_add(v_a_5733_, v___x_5734_, v___x_5677_, v_a_5666_, v_a_5667_);
return v___x_5735_;
} else {
return v___x_5732_;
}
} else {
return v___x_5729_;
}
} else {
return v___x_5726_;
}
} else {
return v___x_5723_;
}
                                                                    } else {
                                                                        return v___x_5720_;
                                                                    }
                                                                } else {
                                                                    return v___x_5717_;
                                                                }
                                                            } else {
                                                                return v___x_5714_;
                                                            }
                                                        } else {
                                                            return v___x_5711_;
                                                        }
                                                    } else {
                                                        return v___x_5708_;
                                                    }
                                                } else {
                                                    return v___x_5705_;
                                                }
                                            } else {
                                                return v___x_5702_;
                                            }
                                        } else {
                                            return v___x_5699_;
                                        }
                                    } else {
                                        return v___x_5696_;
                                    }
                                } else {
                                    return v___x_5693_;
                                }
                            } else {
                                return v___x_5690_;
                            }
                        } else {
                            return v___x_5687_;
                        }
                    } else {
                        return v___x_5684_;
                    }
                } else {
                    return v___x_5681_;
                }
            } else {
                return v___x_5678_;
            }
        } else {
            return v___x_5674_;
        }
    } else {
        return v___x_5671_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_addSimproc___boxed(
    mut v_s_5736_: *mut crate::leanh::LeanObject,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
    mut v_a_5738_: *mut crate::leanh::LeanObject,
    mut v_a_5739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5740_ = l_Lean_Meta_Grind_Arith_addSimproc(v_s_5736_, v_a_5737_, v_a_5738_);
    crate::leanh::lean_dec(v_a_5738_);
    crate::leanh::lean_dec_ref(v_a_5737_);
    return v_res_5740_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField =
        _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField,
    );
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_SafeExponentiation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
}
