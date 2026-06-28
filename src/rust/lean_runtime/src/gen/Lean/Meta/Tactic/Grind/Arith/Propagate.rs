// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Propagate
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    l_Nat_land___boxed, l_Nat_lor___boxed, l_Nat_shiftLeft___boxed, l_Nat_shiftRight___boxed,
    l_Nat_xor___boxed,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue, l_Lean_mkApp5,
    l_Lean_mkApp8, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommRingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
    l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommSemiringM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
    l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::SemiringM::l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring;
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinUpwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_Goal_getRoot, l_Lean_Meta_Grind_pushEqCore___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value: LeanStringObject<5> =
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
        m_data: [72, 65, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value: LeanStringObject<5> =
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
        m_data: [104, 65, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value)
                as *mut LeanObject,
            12657514296478584286 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value)
                as *mut LeanObject,
            14441402839729941302 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [97, 110, 100, 95, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            8407093297865582880 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value)
                as *mut LeanObject,
            11118137186597392547 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [72, 79, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [104, 79, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value)
                as *mut LeanObject,
            10041220898573864337 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value)
                as *mut LeanObject,
            9518792213721863725 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 114, 95, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            8407093297865582880 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value)
                as *mut LeanObject,
            937577760758191742 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value: LeanStringObject<5> =
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
        m_data: [72, 88, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value: LeanStringObject<5> =
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
        m_data: [104, 88, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value)
                as *mut LeanObject,
            5661876967030703708 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value)
                as *mut LeanObject,
            11995384298059439981 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [120, 111, 114, 95, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            8407093297865582880 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value)
                as *mut LeanObject,
            5602409458539743654 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [72, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [104, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value)
                as *mut LeanObject,
            12221703946232912343 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value)
                as *mut LeanObject,
            4302041416438838709 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            115, 104, 105, 102, 116, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            8407093297865582880 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value)
                as *mut LeanObject,
            418335497322784062 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [72, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value)
                as *mut LeanObject,
            5422698995969631099 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value)
                as *mut LeanObject,
            11315714300293431604 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
                as *mut LeanObject,
            8407093297865582880 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value)
                as *mut LeanObject,
            9012786009031937223 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value) as *mut LeanObject,3708748166848919527 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value) as *mut LeanObject,5394957827732845164 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value) as *mut LeanObject,15764114953608429200 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value) as *mut LeanObject,9755723410228041222 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value) as *mut LeanObject,13474504806189678690 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value) as *mut LeanObject,6508593840631735363 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value) as *mut LeanObject,4828225126264449809 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value) as *mut LeanObject,1593258566177356093 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value) as *mut LeanObject,17423969607579146442 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value: LeanStringObject<5> =
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
        m_data: [72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value: LeanStringObject<5> =
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
        m_data: [104, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value)
                as *mut LeanObject,
            1611444129324655608 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            111, 110, 101, 95, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
                as *mut LeanObject,
            12050285396929189622 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value)
                as *mut LeanObject,
            4558874899281809587 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            122, 101, 114, 111, 95, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
                as *mut LeanObject,
            12050285396929189622 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value)
                as *mut LeanObject,
            2337859110404477674 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            109, 117, 108, 95, 111, 110, 101, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
                as *mut LeanObject,
            12050285396929189622 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value)
                as *mut LeanObject,
            2596960839554822006 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            109, 117, 108, 95, 122, 101, 114, 111, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
                as *mut LeanObject,
            12050285396929189622 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value)
                as *mut LeanObject,
            5789827322931640234 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatBinOp(
    mut v_declName_1121_: *mut LeanObject,
    mut v_congrThmName_1122_: *mut LeanObject,
    mut v_op_1123_: *mut LeanObject,
    mut v_e_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
    mut v_a_1127_: *mut LeanObject,
    mut v_a_1128_: *mut LeanObject,
    mut v_a_1129_: *mut LeanObject,
    mut v_a_1130_: *mut LeanObject,
    mut v_a_1131_: *mut LeanObject,
    mut v_a_1132_: *mut LeanObject,
    mut v_a_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_arity_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_val_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1172_: u8 = 0;
    let mut v_val_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_a_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_a_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_a_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_a_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_a_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_a_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_arity_1136_ = lean_unsigned_to_nat(6);
                v___x_1137_ = l_Lean_Expr_isAppOfArity(v_e_1124_, v_declName_1121_, v_arity_1136_);
                if v___x_1137_ == 0 {
                    lean_dec_ref(v_e_1124_);
                    lean_dec_ref(v_op_1123_);
                    lean_dec(v_congrThmName_1122_);
                    v___x_1138_ = lean_box(0);
                    v___x_1139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1139_, 0, v___x_1138_);
                    return v___x_1139_;
                } else {
                    v___x_1140_ = l_Lean_Expr_getAppNumArgs(v_e_1124_);
                    v___x_1141_ = lean_unsigned_to_nat(1);
                    v___x_1142_ = lean_nat_sub(v___x_1140_, v___x_1141_);
                    lean_dec(v___x_1140_);
                    lean_inc(v___x_1142_);
                    v___x_1143_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1142_);
                    v___x_1144_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1;
                    v___x_1145_ = l_Lean_Expr_isConstOf(v___x_1143_, v___x_1144_);
                    lean_dec_ref(v___x_1143_);
                    if v___x_1145_ == 0 {
                        lean_dec(v___x_1142_);
                        lean_dec_ref(v_e_1124_);
                        lean_dec_ref(v_op_1123_);
                        lean_dec(v_congrThmName_1122_);
                        v___x_1146_ = lean_box(0);
                        v___x_1147_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1147_, 0, v___x_1146_);
                        return v___x_1147_;
                    } else {
                        v___x_1148_ = lean_nat_sub(v___x_1142_, v___x_1141_);
                        lean_dec(v___x_1142_);
                        v___x_1149_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1148_);
                        v___x_1150_ = l_Lean_Expr_isConstOf(v___x_1149_, v___x_1144_);
                        lean_dec_ref(v___x_1149_);
                        if v___x_1150_ == 0 {
                            lean_dec_ref(v_e_1124_);
                            lean_dec_ref(v_op_1123_);
                            lean_dec(v_congrThmName_1122_);
                            v___x_1151_ = lean_box(0);
                            v___x_1152_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                            return v___x_1152_;
                        } else {
                            v___x_1153_ = lean_st_ref_get(v_a_1125_);
                            v_a_1154_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1141_);
                            lean_inc_ref(v_a_1154_);
                            v___x_1155_ = l_Lean_Meta_Grind_Goal_getRoot(
                                v___x_1153_,
                                v_a_1154_,
                                v_a_1131_,
                                v_a_1132_,
                                v_a_1133_,
                                v_a_1134_,
                            );
                            lean_dec(v___x_1153_);
                            if lean_obj_tag(v___x_1155_) == 0 {
                                v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
                                lean_inc(v_a_1156_);
                                lean_dec_ref_known(v___x_1155_, 1);
                                v___x_1157_ = l_Lean_Meta_getNatValue_x3f(
                                    v_a_1156_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                                );
                                if lean_obj_tag(v___x_1157_) == 0 {
                                    v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
                                    v_isSharedCheck_1239_ = (!lean_is_exclusive(v___x_1157_)) as u8;
                                    if v_isSharedCheck_1239_ == 0 {
                                        v___x_1160_ = v___x_1157_;
                                        v_isShared_1161_ = v_isSharedCheck_1239_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1158_);
                                        lean_dec(v___x_1157_);
                                        v___x_1160_ = lean_box(0);
                                        v_isShared_1161_ = v_isSharedCheck_1239_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1156_);
                                    lean_dec_ref(v_a_1154_);
                                    lean_dec_ref(v_e_1124_);
                                    lean_dec_ref(v_op_1123_);
                                    lean_dec(v_congrThmName_1122_);
                                    v_a_1240_ = lean_ctor_get(v___x_1157_, 0);
                                    v_isSharedCheck_1247_ = (!lean_is_exclusive(v___x_1157_)) as u8;
                                    if v_isSharedCheck_1247_ == 0 {
                                        v___x_1242_ = v___x_1157_;
                                        v_isShared_1243_ = v_isSharedCheck_1247_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1240_);
                                        lean_dec(v___x_1157_);
                                        v___x_1242_ = lean_box(0);
                                        v_isShared_1243_ = v_isSharedCheck_1247_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_a_1154_);
                                lean_dec_ref(v_e_1124_);
                                lean_dec_ref(v_op_1123_);
                                lean_dec(v_congrThmName_1122_);
                                v_a_1248_ = lean_ctor_get(v___x_1155_, 0);
                                v_isSharedCheck_1255_ = (!lean_is_exclusive(v___x_1155_)) as u8;
                                if v_isSharedCheck_1255_ == 0 {
                                    v___x_1250_ = v___x_1155_;
                                    v_isShared_1251_ = v_isSharedCheck_1255_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_1248_);
                                    lean_dec(v___x_1155_);
                                    v___x_1250_ = lean_box(0);
                                    v_isShared_1251_ = v_isSharedCheck_1255_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1158_) == 1 {
                    lean_del_object(v___x_1160_);
                    v_val_1162_ = lean_ctor_get(v_a_1158_, 0);
                    lean_inc(v_val_1162_);
                    lean_dec_ref_known(v_a_1158_, 1);
                    v___x_1163_ = lean_st_ref_get(v_a_1125_);
                    v___x_1164_ = lean_unsigned_to_nat(0);
                    v___x_1165_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1164_);
                    lean_inc_ref(v___x_1165_);
                    v___x_1166_ = l_Lean_Meta_Grind_Goal_getRoot(
                        v___x_1163_,
                        v___x_1165_,
                        v_a_1131_,
                        v_a_1132_,
                        v_a_1133_,
                        v_a_1134_,
                    );
                    lean_dec(v___x_1163_);
                    if lean_obj_tag(v___x_1166_) == 0 {
                        v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
                        lean_inc(v_a_1167_);
                        lean_dec_ref_known(v___x_1166_, 1);
                        v___x_1168_ = l_Lean_Meta_getNatValue_x3f(
                            v_a_1167_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                        );
                        if lean_obj_tag(v___x_1168_) == 0 {
                            v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
                            v_isSharedCheck_1218_ = (!lean_is_exclusive(v___x_1168_)) as u8;
                            if v_isSharedCheck_1218_ == 0 {
                                v___x_1171_ = v___x_1168_;
                                v_isShared_1172_ = v_isSharedCheck_1218_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1169_);
                                lean_dec(v___x_1168_);
                                v___x_1171_ = lean_box(0);
                                v_isShared_1172_ = v_isSharedCheck_1218_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1167_);
                            lean_dec_ref(v___x_1165_);
                            lean_dec(v_val_1162_);
                            lean_dec(v_a_1156_);
                            lean_dec_ref(v_a_1154_);
                            lean_dec_ref(v_e_1124_);
                            lean_dec_ref(v_op_1123_);
                            lean_dec(v_congrThmName_1122_);
                            v_a_1219_ = lean_ctor_get(v___x_1168_, 0);
                            v_isSharedCheck_1226_ = (!lean_is_exclusive(v___x_1168_)) as u8;
                            if v_isSharedCheck_1226_ == 0 {
                                v___x_1221_ = v___x_1168_;
                                v_isShared_1222_ = v_isSharedCheck_1226_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_1219_);
                                lean_dec(v___x_1168_);
                                v___x_1221_ = lean_box(0);
                                v_isShared_1222_ = v_isSharedCheck_1226_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1165_);
                        lean_dec(v_val_1162_);
                        lean_dec(v_a_1156_);
                        lean_dec_ref(v_a_1154_);
                        lean_dec_ref(v_e_1124_);
                        lean_dec_ref(v_op_1123_);
                        lean_dec(v_congrThmName_1122_);
                        v_a_1227_ = lean_ctor_get(v___x_1166_, 0);
                        v_isSharedCheck_1234_ = (!lean_is_exclusive(v___x_1166_)) as u8;
                        if v_isSharedCheck_1234_ == 0 {
                            v___x_1229_ = v___x_1166_;
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_1227_);
                            lean_dec(v___x_1166_);
                            v___x_1229_ = lean_box(0);
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1158_);
                    lean_dec(v_a_1156_);
                    lean_dec_ref(v_a_1154_);
                    lean_dec_ref(v_e_1124_);
                    lean_dec_ref(v_op_1123_);
                    lean_dec(v_congrThmName_1122_);
                    v___x_1235_ = lean_box(0);
                    if v_isShared_1161_ == 0 {
                        lean_ctor_set(v___x_1160_, 0, v___x_1235_);
                        v___x_1237_ = v___x_1160_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
                        v___x_1237_ = v_reuseFailAlloc_1238_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1169_) == 1 {
                    lean_del_object(v___x_1171_);
                    v_val_1173_ = lean_ctor_get(v_a_1169_, 0);
                    lean_inc(v_val_1173_);
                    lean_dec_ref_known(v_a_1169_, 1);
                    v___x_1174_ = lean_apply_2(v_op_1123_, v_val_1162_, v_val_1173_);
                    v___x_1175_ = l_Lean_mkNatLit(v___x_1174_);
                    v___x_1176_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1175_, v_a_1130_);
                    if lean_obj_tag(v___x_1176_) == 0 {
                        v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
                        lean_inc_n(v_a_1177_, 2);
                        lean_dec_ref_known(v___x_1176_, 1);
                        v___x_1178_ = lean_box(0);
                        lean_inc(v_a_1134_);
                        lean_inc_ref(v_a_1133_);
                        lean_inc(v_a_1132_);
                        lean_inc_ref(v_a_1131_);
                        lean_inc(v_a_1130_);
                        lean_inc_ref(v_a_1129_);
                        lean_inc(v_a_1128_);
                        lean_inc_ref(v_a_1127_);
                        lean_inc(v_a_1126_);
                        lean_inc(v_a_1125_);
                        v___x_1179_ = lean_grind_internalize(
                            v_a_1177_,
                            v___x_1164_,
                            v___x_1178_,
                            v_a_1125_,
                            v_a_1126_,
                            v_a_1127_,
                            v_a_1128_,
                            v_a_1129_,
                            v_a_1130_,
                            v_a_1131_,
                            v_a_1132_,
                            v_a_1133_,
                            v_a_1134_,
                        );
                        if lean_obj_tag(v___x_1179_) == 0 {
                            lean_dec_ref_known(v___x_1179_, 1);
                            lean_inc(v_a_1134_);
                            lean_inc_ref(v_a_1133_);
                            lean_inc(v_a_1132_);
                            lean_inc_ref(v_a_1131_);
                            lean_inc(v_a_1130_);
                            lean_inc_ref(v_a_1129_);
                            lean_inc(v_a_1128_);
                            lean_inc_ref(v_a_1127_);
                            lean_inc(v_a_1126_);
                            lean_inc(v_a_1125_);
                            lean_inc(v_a_1156_);
                            lean_inc_ref(v_a_1154_);
                            v___x_1180_ = lean_grind_mk_eq_proof(
                                v_a_1154_, v_a_1156_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_,
                                v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                            );
                            if lean_obj_tag(v___x_1180_) == 0 {
                                v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
                                lean_inc(v_a_1181_);
                                lean_dec_ref_known(v___x_1180_, 1);
                                lean_inc(v_a_1134_);
                                lean_inc_ref(v_a_1133_);
                                lean_inc(v_a_1132_);
                                lean_inc_ref(v_a_1131_);
                                lean_inc(v_a_1130_);
                                lean_inc_ref(v_a_1129_);
                                lean_inc(v_a_1128_);
                                lean_inc_ref(v_a_1127_);
                                lean_inc(v_a_1126_);
                                lean_inc(v_a_1125_);
                                lean_inc(v_a_1167_);
                                lean_inc_ref(v___x_1165_);
                                v___x_1182_ = lean_grind_mk_eq_proof(
                                    v___x_1165_,
                                    v_a_1167_,
                                    v_a_1125_,
                                    v_a_1126_,
                                    v_a_1127_,
                                    v_a_1128_,
                                    v_a_1129_,
                                    v_a_1130_,
                                    v_a_1131_,
                                    v_a_1132_,
                                    v_a_1133_,
                                    v_a_1134_,
                                );
                                if lean_obj_tag(v___x_1182_) == 0 {
                                    v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
                                    lean_inc(v_a_1183_);
                                    lean_dec_ref_known(v___x_1182_, 1);
                                    v___x_1184_ = lean_box(0);
                                    v___x_1185_ = l_Lean_mkConst(v_congrThmName_1122_, v___x_1184_);
                                    v___x_1186_ = l_Lean_eagerReflBoolTrue;
                                    lean_inc(v_a_1177_);
                                    v___x_1187_ = l_Lean_mkApp8(
                                        v___x_1185_,
                                        v_a_1154_,
                                        v___x_1165_,
                                        v_a_1156_,
                                        v_a_1167_,
                                        v_a_1177_,
                                        v_a_1181_,
                                        v_a_1183_,
                                        v___x_1186_,
                                    );
                                    v___x_1188_ = 0;
                                    v___x_1189_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                        v_e_1124_,
                                        v_a_1177_,
                                        v___x_1187_,
                                        v___x_1188_,
                                        v_a_1125_,
                                        v_a_1127_,
                                        v_a_1131_,
                                        v_a_1132_,
                                        v_a_1133_,
                                        v_a_1134_,
                                    );
                                    return v___x_1189_;
                                } else {
                                    lean_dec(v_a_1181_);
                                    lean_dec(v_a_1177_);
                                    lean_dec(v_a_1167_);
                                    lean_dec_ref(v___x_1165_);
                                    lean_dec(v_a_1156_);
                                    lean_dec_ref(v_a_1154_);
                                    lean_dec_ref(v_e_1124_);
                                    lean_dec(v_congrThmName_1122_);
                                    v_a_1190_ = lean_ctor_get(v___x_1182_, 0);
                                    v_isSharedCheck_1197_ = (!lean_is_exclusive(v___x_1182_)) as u8;
                                    if v_isSharedCheck_1197_ == 0 {
                                        v___x_1192_ = v___x_1182_;
                                        v_isShared_1193_ = v_isSharedCheck_1197_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1190_);
                                        lean_dec(v___x_1182_);
                                        v___x_1192_ = lean_box(0);
                                        v_isShared_1193_ = v_isSharedCheck_1197_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_1177_);
                                lean_dec(v_a_1167_);
                                lean_dec_ref(v___x_1165_);
                                lean_dec(v_a_1156_);
                                lean_dec_ref(v_a_1154_);
                                lean_dec_ref(v_e_1124_);
                                lean_dec(v_congrThmName_1122_);
                                v_a_1198_ = lean_ctor_get(v___x_1180_, 0);
                                v_isSharedCheck_1205_ = (!lean_is_exclusive(v___x_1180_)) as u8;
                                if v_isSharedCheck_1205_ == 0 {
                                    v___x_1200_ = v___x_1180_;
                                    v_isShared_1201_ = v_isSharedCheck_1205_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_1198_);
                                    lean_dec(v___x_1180_);
                                    v___x_1200_ = lean_box(0);
                                    v_isShared_1201_ = v_isSharedCheck_1205_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1177_);
                            lean_dec(v_a_1167_);
                            lean_dec_ref(v___x_1165_);
                            lean_dec(v_a_1156_);
                            lean_dec_ref(v_a_1154_);
                            lean_dec_ref(v_e_1124_);
                            lean_dec(v_congrThmName_1122_);
                            return v___x_1179_;
                        }
                    } else {
                        lean_dec(v_a_1167_);
                        lean_dec_ref(v___x_1165_);
                        lean_dec(v_a_1156_);
                        lean_dec_ref(v_a_1154_);
                        lean_dec_ref(v_e_1124_);
                        lean_dec(v_congrThmName_1122_);
                        v_a_1206_ = lean_ctor_get(v___x_1176_, 0);
                        v_isSharedCheck_1213_ = (!lean_is_exclusive(v___x_1176_)) as u8;
                        if v_isSharedCheck_1213_ == 0 {
                            v___x_1208_ = v___x_1176_;
                            v_isShared_1209_ = v_isSharedCheck_1213_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1206_);
                            lean_dec(v___x_1176_);
                            v___x_1208_ = lean_box(0);
                            v_isShared_1209_ = v_isSharedCheck_1213_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1169_);
                    lean_dec(v_a_1167_);
                    lean_dec_ref(v___x_1165_);
                    lean_dec(v_val_1162_);
                    lean_dec(v_a_1156_);
                    lean_dec_ref(v_a_1154_);
                    lean_dec_ref(v_e_1124_);
                    lean_dec_ref(v_op_1123_);
                    lean_dec(v_congrThmName_1122_);
                    v___x_1214_ = lean_box(0);
                    if v_isShared_1172_ == 0 {
                        lean_ctor_set(v___x_1171_, 0, v___x_1214_);
                        v___x_1216_ = v___x_1171_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
                        v___x_1216_ = v_reuseFailAlloc_1217_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1193_ == 0 {
                    v___x_1195_ = v___x_1192_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
                    v___x_1195_ = v_reuseFailAlloc_1196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1195_;
            }
            5 => {
                if v_isShared_1201_ == 0 {
                    v___x_1203_ = v___x_1200_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
                    v___x_1203_ = v_reuseFailAlloc_1204_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1203_;
            }
            7 => {
                if v_isShared_1209_ == 0 {
                    v___x_1211_ = v___x_1208_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1211_;
            }
            9 => {
                return v___x_1216_;
            }
            10 => {
                if v_isShared_1222_ == 0 {
                    v___x_1224_ = v___x_1221_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1224_;
            }
            12 => {
                if v_isShared_1230_ == 0 {
                    v___x_1232_ = v___x_1229_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
                    v___x_1232_ = v_reuseFailAlloc_1233_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1232_;
            }
            14 => {
                return v___x_1237_;
            }
            15 => {
                if v_isShared_1243_ == 0 {
                    v___x_1245_ = v___x_1242_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
                    v___x_1245_ = v_reuseFailAlloc_1246_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1245_;
            }
            17 => {
                if v_isShared_1251_ == 0 {
                    v___x_1253_ = v___x_1250_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(
    mut v_declName_1256_: *mut LeanObject,
    mut v_congrThmName_1257_: *mut LeanObject,
    mut v_op_1258_: *mut LeanObject,
    mut v_e_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
    mut v_a_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v_declName_1256_,
        v_congrThmName_1257_,
        v_op_1258_,
        v_e_1259_,
        v_a_1260_,
        v_a_1261_,
        v_a_1262_,
        v_a_1263_,
        v_a_1264_,
        v_a_1265_,
        v_a_1266_,
        v_a_1267_,
        v_a_1268_,
        v_a_1269_,
    );
    lean_dec(v_a_1269_);
    lean_dec_ref(v_a_1268_);
    lean_dec(v_a_1267_);
    lean_dec_ref(v_a_1266_);
    lean_dec(v_a_1265_);
    lean_dec_ref(v_a_1264_);
    lean_dec(v_a_1263_);
    lean_dec_ref(v_a_1262_);
    lean_dec(v_a_1261_);
    lean_dec(v_a_1260_);
    lean_dec(v_declName_1256_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatAnd(
    mut v_e_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
    mut v_a_1295_: *mut LeanObject,
    mut v_a_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___f_1298_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0;
    v___x_1299_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
    v___x_1300_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7;
    v___x_1301_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1299_,
        v___x_1300_,
        v___f_1298_,
        v_e_1286_,
        v_a_1287_,
        v_a_1288_,
        v_a_1289_,
        v_a_1290_,
        v_a_1291_,
        v_a_1292_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
    );
    return v___x_1301_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(
    mut v_e_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
    mut v_a_1309_: *mut LeanObject,
    mut v_a_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_Meta_Grind_Arith_propagateNatAnd(
        v_e_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_,
        v_a_1310_, v_a_1311_, v_a_1312_,
    );
    lean_dec(v_a_1312_);
    lean_dec_ref(v_a_1311_);
    lean_dec(v_a_1310_);
    lean_dec_ref(v_a_1309_);
    lean_dec(v_a_1308_);
    lean_dec_ref(v_a_1307_);
    lean_dec(v_a_1306_);
    lean_dec_ref(v_a_1305_);
    lean_dec(v_a_1304_);
    lean_dec(v_a_1303_);
    return v_res_1314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
    v___x_1317_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1318_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1316_, v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(
    mut v_a_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
    return v_res_1320_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatOr(
    mut v_e_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___f_1345_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0;
    v___x_1346_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
    v___x_1347_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5;
    v___x_1348_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1346_,
        v___x_1347_,
        v___f_1345_,
        v_e_1333_,
        v_a_1334_,
        v_a_1335_,
        v_a_1336_,
        v_a_1337_,
        v_a_1338_,
        v_a_1339_,
        v_a_1340_,
        v_a_1341_,
        v_a_1342_,
        v_a_1343_,
    );
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(
    mut v_e_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_a_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_Meta_Grind_Arith_propagateNatOr(
        v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_,
        v_a_1357_, v_a_1358_, v_a_1359_,
    );
    lean_dec(v_a_1359_);
    lean_dec_ref(v_a_1358_);
    lean_dec(v_a_1357_);
    lean_dec_ref(v_a_1356_);
    lean_dec(v_a_1355_);
    lean_dec_ref(v_a_1354_);
    lean_dec(v_a_1353_);
    lean_dec_ref(v_a_1352_);
    lean_dec(v_a_1351_);
    lean_dec(v_a_1350_);
    return v_res_1361_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
    v___x_1364_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatOr___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1365_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1363_, v___x_1364_);
    return v___x_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(
    mut v_a_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_res_1367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
    return v_res_1367_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatXOr(
    mut v_e_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___f_1392_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0;
    v___x_1393_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
    v___x_1394_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5;
    v___x_1395_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1393_,
        v___x_1394_,
        v___f_1392_,
        v_e_1380_,
        v_a_1381_,
        v_a_1382_,
        v_a_1383_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
        v_a_1389_,
        v_a_1390_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(
    mut v_e_1396_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v_res_1408_: *mut LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Meta_Grind_Arith_propagateNatXOr(
        v_e_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_,
        v_a_1404_, v_a_1405_, v_a_1406_,
    );
    lean_dec(v_a_1406_);
    lean_dec_ref(v_a_1405_);
    lean_dec(v_a_1404_);
    lean_dec_ref(v_a_1403_);
    lean_dec(v_a_1402_);
    lean_dec_ref(v_a_1401_);
    lean_dec(v_a_1400_);
    lean_dec_ref(v_a_1399_);
    lean_dec(v_a_1398_);
    lean_dec(v_a_1397_);
    return v_res_1408_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
    v___x_1411_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1412_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1410_, v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(
    mut v_a_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
    return v_res_1414_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(
    mut v_e_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
    mut v_a_1429_: *mut LeanObject,
    mut v_a_1430_: *mut LeanObject,
    mut v_a_1431_: *mut LeanObject,
    mut v_a_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
    mut v_a_1434_: *mut LeanObject,
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
    mut v_a_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___f_1439_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0;
    v___x_1440_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
    v___x_1441_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5;
    v___x_1442_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1440_,
        v___x_1441_,
        v___f_1439_,
        v_e_1427_,
        v_a_1428_,
        v_a_1429_,
        v_a_1430_,
        v_a_1431_,
        v_a_1432_,
        v_a_1433_,
        v_a_1434_,
        v_a_1435_,
        v_a_1436_,
        v_a_1437_,
    );
    return v___x_1442_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(
    mut v_e_1443_: *mut LeanObject,
    mut v_a_1444_: *mut LeanObject,
    mut v_a_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
    mut v_a_1448_: *mut LeanObject,
    mut v_a_1449_: *mut LeanObject,
    mut v_a_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
    mut v_a_1452_: *mut LeanObject,
    mut v_a_1453_: *mut LeanObject,
    mut v_a_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(
        v_e_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_,
        v_a_1451_, v_a_1452_, v_a_1453_,
    );
    lean_dec(v_a_1453_);
    lean_dec_ref(v_a_1452_);
    lean_dec(v_a_1451_);
    lean_dec_ref(v_a_1450_);
    lean_dec(v_a_1449_);
    lean_dec_ref(v_a_1448_);
    lean_dec(v_a_1447_);
    lean_dec_ref(v_a_1446_);
    lean_dec(v_a_1445_);
    lean_dec(v_a_1444_);
    return v_res_1455_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
    v___x_1458_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1459_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1457_, v___x_1458_);
    return v___x_1459_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(
    mut v_a_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
    return v_res_1461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftRight(
    mut v_e_1474_: *mut LeanObject,
    mut v_a_1475_: *mut LeanObject,
    mut v_a_1476_: *mut LeanObject,
    mut v_a_1477_: *mut LeanObject,
    mut v_a_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
    mut v_a_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
    mut v_a_1482_: *mut LeanObject,
    mut v_a_1483_: *mut LeanObject,
    mut v_a_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    v___f_1486_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0;
    v___x_1487_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
    v___x_1488_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5;
    v___x_1489_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1487_,
        v___x_1488_,
        v___f_1486_,
        v_e_1474_,
        v_a_1475_,
        v_a_1476_,
        v_a_1477_,
        v_a_1478_,
        v_a_1479_,
        v_a_1480_,
        v_a_1481_,
        v_a_1482_,
        v_a_1483_,
        v_a_1484_,
    );
    return v___x_1489_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(
    mut v_e_1490_: *mut LeanObject,
    mut v_a_1491_: *mut LeanObject,
    mut v_a_1492_: *mut LeanObject,
    mut v_a_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
    mut v_a_1495_: *mut LeanObject,
    mut v_a_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(
        v_e_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_,
        v_a_1498_, v_a_1499_, v_a_1500_,
    );
    lean_dec(v_a_1500_);
    lean_dec_ref(v_a_1499_);
    lean_dec(v_a_1498_);
    lean_dec_ref(v_a_1497_);
    lean_dec(v_a_1496_);
    lean_dec_ref(v_a_1495_);
    lean_dec(v_a_1494_);
    lean_dec_ref(v_a_1493_);
    lean_dec(v_a_1492_);
    lean_dec(v_a_1491_);
    return v_res_1502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
    v___x_1505_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1506_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1504_, v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(
    mut v_a_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
    return v_res_1508_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u64 = 0;
    v___x_1509_ = lean_unsigned_to_nat(1723);
    v___x_1510_ = lean_uint64_of_nat(v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_1511_: *mut LeanObject,
    mut v_x_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u64 = 0;
    let mut v___x_1522_: u64 = 0;
    let mut v___x_1523_: u64 = 0;
    let mut v_fold_1524_: u64 = 0;
    let mut v___x_1525_: u64 = 0;
    let mut v___x_1526_: u64 = 0;
    let mut v___x_1527_: u64 = 0;
    let mut v___x_1528_: usize = 0;
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: usize = 0;
    let mut v___x_1532_: usize = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u64 = 0;
    let mut v_hash_1540_: u64 = 0;
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1512_) == 0 {
                    return v_x_1511_;
                } else {
                    v_key_1513_ = lean_ctor_get(v_x_1512_, 0);
                    v_value_1514_ = lean_ctor_get(v_x_1512_, 1);
                    v_tail_1515_ = lean_ctor_get(v_x_1512_, 2);
                    v_isSharedCheck_1541_ = (!lean_is_exclusive(v_x_1512_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1517_ = v_x_1512_;
                        v_isShared_1518_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1515_);
                        lean_inc(v_value_1514_);
                        lean_inc(v_key_1513_);
                        lean_dec(v_x_1512_);
                        v___x_1517_ = lean_box(0);
                        v_isShared_1518_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1519_ = lean_array_get_size(v_x_1511_);
                if lean_obj_tag(v_key_1513_) == 0 {
                    v___x_1539_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1521_ = v___x_1539_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1540_ = lean_ctor_get_uint64(
                        v_key_1513_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1521_ = v_hash_1540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1522_ = 32u64;
                v___x_1523_ = lean_uint64_shift_right(v___y_1521_, v___x_1522_);
                v_fold_1524_ = lean_uint64_xor(v___y_1521_, v___x_1523_);
                v___x_1525_ = 16u64;
                v___x_1526_ = lean_uint64_shift_right(v_fold_1524_, v___x_1525_);
                v___x_1527_ = lean_uint64_xor(v_fold_1524_, v___x_1526_);
                v___x_1528_ = lean_uint64_to_usize(v___x_1527_);
                v___x_1529_ = lean_usize_of_nat(v___x_1519_);
                v___x_1530_ = 1usize;
                v___x_1531_ = lean_usize_sub(v___x_1529_, v___x_1530_);
                v___x_1532_ = lean_usize_land(v___x_1528_, v___x_1531_);
                v___x_1533_ = lean_array_uget_borrowed(v_x_1511_, v___x_1532_);
                lean_inc(v___x_1533_);
                if v_isShared_1518_ == 0 {
                    lean_ctor_set(v___x_1517_, 2, v___x_1533_);
                    v___x_1535_ = v___x_1517_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_key_1513_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_value_1514_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 2, v___x_1533_);
                    v___x_1535_ = v_reuseFailAlloc_1538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1536_ = lean_array_uset(v_x_1511_, v___x_1532_, v___x_1535_);
                v_x_1511_ = v___x_1536_;
                v_x_1512_ = v_tail_1515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(
    mut v_i_1542_: *mut LeanObject,
    mut v_source_1543_: *mut LeanObject,
    mut v_target_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v_es_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1545_ = lean_array_get_size(v_source_1543_);
                v___x_1546_ = lean_nat_dec_lt(v_i_1542_, v___x_1545_);
                if v___x_1546_ == 0 {
                    lean_dec_ref(v_source_1543_);
                    lean_dec(v_i_1542_);
                    return v_target_1544_;
                } else {
                    v_es_1547_ = lean_array_fget(v_source_1543_, v_i_1542_);
                    v___x_1548_ = lean_box(0);
                    v_source_1549_ = lean_array_fset(v_source_1543_, v_i_1542_, v___x_1548_);
                    v_target_1550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1544_, v_es_1547_);
                    v___x_1551_ = lean_unsigned_to_nat(1);
                    v___x_1552_ = lean_nat_add(v_i_1542_, v___x_1551_);
                    lean_dec(v_i_1542_);
                    v_i_1542_ = v___x_1552_;
                    v_source_1543_ = v_source_1549_;
                    v_target_1544_ = v_target_1550_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(
    mut v_data_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = lean_array_get_size(v_data_1554_);
    v___x_1556_ = lean_unsigned_to_nat(2);
    v_nbuckets_1557_ = lean_nat_mul(v___x_1555_, v___x_1556_);
    v___x_1558_ = lean_unsigned_to_nat(0);
    v___x_1559_ = lean_box(0);
    v___x_1560_ = lean_mk_array(v_nbuckets_1557_, v___x_1559_);
    v___x_1561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v___x_1558_, v_data_1554_, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(
    mut v_a_1562_: *mut LeanObject,
    mut v_x_1563_: *mut LeanObject,
) -> u8 {
    let mut v___x_1564_: u8 = 0;
    let mut v_key_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1563_) == 0 {
                    v___x_1564_ = 0;
                    return v___x_1564_;
                } else {
                    v_key_1565_ = lean_ctor_get(v_x_1563_, 0);
                    v_tail_1566_ = lean_ctor_get(v_x_1563_, 2);
                    v___x_1567_ = lean_name_eq(v_key_1565_, v_a_1562_);
                    if v___x_1567_ == 0 {
                        v_x_1563_ = v_tail_1566_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1567_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(
    mut v_a_1569_: *mut LeanObject,
    mut v_x_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1569_, v_x_1570_);
    lean_dec(v_x_1570_);
    lean_dec(v_a_1569_);
    v_r_1572_ = lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(
    mut v_m_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
    mut v_b_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1580_: u64 = 0;
    let mut v___x_1581_: u64 = 0;
    let mut v___x_1582_: u64 = 0;
    let mut v_fold_1583_: u64 = 0;
    let mut v___x_1584_: u64 = 0;
    let mut v___x_1585_: u64 = 0;
    let mut v___x_1586_: u64 = 0;
    let mut v___x_1587_: usize = 0;
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: usize = 0;
    let mut v___x_1590_: usize = 0;
    let mut v___x_1591_: usize = 0;
    let mut v_bkt_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    let mut v_val_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v_unused_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u64 = 0;
    let mut v_hash_1618_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1576_ = lean_ctor_get(v_m_1573_, 0);
                v_buckets_1577_ = lean_ctor_get(v_m_1573_, 1);
                v___x_1578_ = lean_array_get_size(v_buckets_1577_);
                if lean_obj_tag(v_a_1574_) == 0 {
                    v___x_1617_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1580_ = v___x_1617_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1618_ = lean_ctor_get_uint64(
                        v_a_1574_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1580_ = v_hash_1618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1581_ = 32u64;
                v___x_1582_ = lean_uint64_shift_right(v___y_1580_, v___x_1581_);
                v_fold_1583_ = lean_uint64_xor(v___y_1580_, v___x_1582_);
                v___x_1584_ = 16u64;
                v___x_1585_ = lean_uint64_shift_right(v_fold_1583_, v___x_1584_);
                v___x_1586_ = lean_uint64_xor(v_fold_1583_, v___x_1585_);
                v___x_1587_ = lean_uint64_to_usize(v___x_1586_);
                v___x_1588_ = lean_usize_of_nat(v___x_1578_);
                v___x_1589_ = 1usize;
                v___x_1590_ = lean_usize_sub(v___x_1588_, v___x_1589_);
                v___x_1591_ = lean_usize_land(v___x_1587_, v___x_1590_);
                v_bkt_1592_ = lean_array_uget_borrowed(v_buckets_1577_, v___x_1591_);
                v___x_1593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1574_, v_bkt_1592_);
                if v___x_1593_ == 0 {
                    lean_inc_ref(v_buckets_1577_);
                    lean_inc(v_size_1576_);
                    v_isSharedCheck_1614_ = (!lean_is_exclusive(v_m_1573_)) as u8;
                    if v_isSharedCheck_1614_ == 0 {
                        v_unused_1615_ = lean_ctor_get(v_m_1573_, 1);
                        lean_dec(v_unused_1615_);
                        v_unused_1616_ = lean_ctor_get(v_m_1573_, 0);
                        lean_dec(v_unused_1616_);
                        v___x_1595_ = v_m_1573_;
                        v_isShared_1596_ = v_isSharedCheck_1614_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1573_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1614_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1575_);
                    lean_dec(v_a_1574_);
                    return v_m_1573_;
                }
            }
            2 => {
                v___x_1597_ = lean_unsigned_to_nat(1);
                v_size_x27_1598_ = lean_nat_add(v_size_1576_, v___x_1597_);
                lean_dec(v_size_1576_);
                lean_inc(v_bkt_1592_);
                v___x_1599_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1599_, 0, v_a_1574_);
                lean_ctor_set(v___x_1599_, 1, v_b_1575_);
                lean_ctor_set(v___x_1599_, 2, v_bkt_1592_);
                v_buckets_x27_1600_ = lean_array_uset(v_buckets_1577_, v___x_1591_, v___x_1599_);
                v___x_1601_ = lean_unsigned_to_nat(4);
                v___x_1602_ = lean_nat_mul(v_size_x27_1598_, v___x_1601_);
                v___x_1603_ = lean_unsigned_to_nat(3);
                v___x_1604_ = lean_nat_div(v___x_1602_, v___x_1603_);
                lean_dec(v___x_1602_);
                v___x_1605_ = lean_array_get_size(v_buckets_x27_1600_);
                v___x_1606_ = lean_nat_dec_le(v___x_1604_, v___x_1605_);
                lean_dec(v___x_1604_);
                if v___x_1606_ == 0 {
                    v_val_1607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_buckets_x27_1600_);
                    if v_isShared_1596_ == 0 {
                        lean_ctor_set(v___x_1595_, 1, v_val_1607_);
                        lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
                        v___x_1609_ = v___x_1595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_x27_1598_);
                        lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_val_1607_);
                        v___x_1609_ = v_reuseFailAlloc_1610_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1596_ == 0 {
                        lean_ctor_set(v___x_1595_, 1, v_buckets_x27_1600_);
                        lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
                        v___x_1612_ = v___x_1595_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_size_x27_1598_);
                        lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_buckets_x27_1600_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1609_;
            }
            4 => {
                return v___x_1612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(
    mut v_x_1619_: *mut LeanObject,
    mut v_x_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1620_) == 0 {
                    return v_x_1619_;
                } else {
                    v_head_1621_ = lean_ctor_get(v_x_1620_, 0);
                    lean_inc(v_head_1621_);
                    v_tail_1622_ = lean_ctor_get(v_x_1620_, 1);
                    lean_inc(v_tail_1622_);
                    lean_dec_ref_known(v_x_1620_, 2);
                    v___x_1623_ = lean_box(0);
                    v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_x_1619_, v_head_1621_, v___x_1623_);
                    v_x_1619_ = v___x_1624_;
                    v_x_1620_ = v_tail_1622_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0()
-> *mut LeanObject {
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = lean_box(0);
    v___x_1627_ = lean_unsigned_to_nat(16);
    v___x_1628_ = lean_mk_array(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1()
-> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
    v___x_1630_ = lean_unsigned_to_nat(0);
    v___x_1631_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    lean_ctor_set(v___x_1631_, 1, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34()
-> *mut LeanObject {
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    v___x_1698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33;
    v___x_1699_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
    v___x_1700_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(v___x_1699_, v___x_1698_);
    return v___x_1700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring()
-> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34);
    return v___x_1701_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(
    mut v_00_u03b2_1702_: *mut LeanObject,
    mut v_m_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
    mut v_b_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_1703_, v_a_1704_, v_b_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(
    mut v_00_u03b2_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_x_1709_: *mut LeanObject,
) -> u8 {
    let mut v___x_1710_: u8 = 0;
    v___x_1710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1708_, v_x_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(
    mut v_00_u03b2_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_x_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: u8 = 0;
    let mut v_r_1715_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(v_00_u03b2_1711_, v_a_1712_, v_x_1713_);
    lean_dec(v_x_1713_);
    lean_dec(v_a_1712_);
    v_r_1715_ = lean_box((v_res_1714_) as usize);
    return v_r_1715_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(
    mut v_00_u03b2_1716_: *mut LeanObject,
    mut v_data_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_data_1717_);
    return v___x_1718_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1719_: *mut LeanObject,
    mut v_i_1720_: *mut LeanObject,
    mut v_source_1721_: *mut LeanObject,
    mut v_target_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v_i_1720_, v_source_1721_, v_target_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1724_: *mut LeanObject,
    mut v_x_1725_: *mut LeanObject,
    mut v_x_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1725_, v_x_1726_);
    return v___x_1727_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(
    mut v_m_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: u64 = 0;
    let mut v___x_1734_: u64 = 0;
    let mut v___x_1735_: u64 = 0;
    let mut v_fold_1736_: u64 = 0;
    let mut v___x_1737_: u64 = 0;
    let mut v___x_1738_: u64 = 0;
    let mut v___x_1739_: u64 = 0;
    let mut v___x_1740_: usize = 0;
    let mut v___x_1741_: usize = 0;
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v_hash_1748_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1730_ = lean_ctor_get(v_m_1728_, 1);
                v___x_1731_ = lean_array_get_size(v_buckets_1730_);
                if lean_obj_tag(v_a_1729_) == 0 {
                    v___x_1747_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1733_ = v___x_1747_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1748_ = lean_ctor_get_uint64(
                        v_a_1729_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1733_ = v_hash_1748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1734_ = 32u64;
                v___x_1735_ = lean_uint64_shift_right(v___y_1733_, v___x_1734_);
                v_fold_1736_ = lean_uint64_xor(v___y_1733_, v___x_1735_);
                v___x_1737_ = 16u64;
                v___x_1738_ = lean_uint64_shift_right(v_fold_1736_, v___x_1737_);
                v___x_1739_ = lean_uint64_xor(v_fold_1736_, v___x_1738_);
                v___x_1740_ = lean_uint64_to_usize(v___x_1739_);
                v___x_1741_ = lean_usize_of_nat(v___x_1731_);
                v___x_1742_ = 1usize;
                v___x_1743_ = lean_usize_sub(v___x_1741_, v___x_1742_);
                v___x_1744_ = lean_usize_land(v___x_1740_, v___x_1743_);
                v___x_1745_ = lean_array_uget_borrowed(v_buckets_1730_, v___x_1744_);
                v___x_1746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1729_, v___x_1745_);
                return v___x_1746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(
    mut v_m_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1751_: u8 = 0;
    let mut v_r_1752_: *mut LeanObject = core::ptr::null_mut();
    v_res_1751_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_1749_, v_a_1750_);
    lean_dec(v_a_1750_);
    lean_dec_ref(v_m_1749_);
    v_r_1752_ = lean_box((v_res_1751_) as usize);
    return v_r_1752_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(
    mut v_type_1753_: *mut LeanObject,
) -> u8 {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_Expr_getAppFn(v_type_1753_);
    if lean_obj_tag(v___x_1754_) == 4 {
        let mut v_declName_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: u8 = 0;
        v_declName_1755_ = lean_ctor_get(v___x_1754_, 0);
        lean_inc(v_declName_1755_);
        lean_dec_ref_known(v___x_1754_, 2);
        v___x_1756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
        v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v___x_1756_, v_declName_1755_);
        lean_dec(v_declName_1755_);
        return v___x_1757_;
    } else {
        let mut v___x_1758_: u8 = 0;
        lean_dec_ref(v___x_1754_);
        v___x_1758_ = 0;
        return v___x_1758_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(
    mut v_type_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1760_: u8 = 0;
    let mut v_r_1761_: *mut LeanObject = core::ptr::null_mut();
    v_res_1760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_1759_);
    lean_dec_ref(v_type_1759_);
    v_r_1761_ = lean_box((v_res_1760_) as usize);
    return v_r_1761_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(
    mut v_00_u03b2_1762_: *mut LeanObject,
    mut v_m_1763_: *mut LeanObject,
    mut v_a_1764_: *mut LeanObject,
) -> u8 {
    let mut v___x_1765_: u8 = 0;
    v___x_1765_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_1763_, v_a_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(
    mut v_00_u03b2_1766_: *mut LeanObject,
    mut v_m_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: u8 = 0;
    let mut v_r_1770_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(v_00_u03b2_1766_, v_m_1767_, v_a_1768_);
    lean_dec(v_a_1768_);
    lean_dec_ref(v_m_1767_);
    v_r_1770_ = lean_box((v_res_1769_) as usize);
    return v_r_1770_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(
    mut v_type_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_a_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
    mut v_a_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v_toSemiring_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_a_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v_semiringInst_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v_a_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v_val_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_semiringInst_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_a_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_a_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_1771_);
                if v___x_1783_ == 0 {
                    lean_inc_ref(v_type_1771_);
                    v___x_1784_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v_type_1771_,
                        v_a_1772_,
                        v_a_1773_,
                        v_a_1774_,
                        v_a_1775_,
                        v_a_1776_,
                        v_a_1777_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                    );
                    if lean_obj_tag(v___x_1784_) == 0 {
                        v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1911_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1787_ = v___x_1784_;
                            v_isShared_1788_ = v_isSharedCheck_1911_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1785_);
                            lean_dec(v___x_1784_);
                            v___x_1787_ = lean_box(0);
                            v_isShared_1788_ = v_isSharedCheck_1911_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_1771_);
                        v_a_1912_ = lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1784_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_1912_);
                            lean_dec(v___x_1784_);
                            v___x_1914_ = lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_1771_);
                    v___x_1920_ = lean_box(0);
                    v___x_1921_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1921_, 0, v___x_1920_);
                    return v___x_1921_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1785_) == 0 {
                    if v___x_1783_ == 0 {
                        lean_del_object(v___x_1787_);
                        lean_inc_ref(v_type_1771_);
                        v___x_1794_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
                            v_type_1771_,
                            v_a_1772_,
                            v_a_1773_,
                            v_a_1774_,
                            v_a_1775_,
                            v_a_1776_,
                            v_a_1777_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                        );
                        if lean_obj_tag(v___x_1794_) == 0 {
                            v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
                            lean_inc(v_a_1795_);
                            lean_dec_ref_known(v___x_1794_, 1);
                            if lean_obj_tag(v_a_1795_) == 1 {
                                lean_dec_ref(v_type_1771_);
                                v_val_1796_ = lean_ctor_get(v_a_1795_, 0);
                                v_isSharedCheck_1822_ = (!lean_is_exclusive(v_a_1795_)) as u8;
                                if v_isSharedCheck_1822_ == 0 {
                                    v___x_1798_ = v_a_1795_;
                                    v_isShared_1799_ = v_isSharedCheck_1822_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_val_1796_);
                                    lean_dec(v_a_1795_);
                                    v___x_1798_ = lean_box(0);
                                    v_isShared_1799_ = v_isSharedCheck_1822_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_1795_);
                                lean_inc_ref(v_type_1771_);
                                v___x_1823_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(
                                    v_type_1771_,
                                    v_a_1772_,
                                    v_a_1773_,
                                    v_a_1774_,
                                    v_a_1775_,
                                    v_a_1776_,
                                    v_a_1777_,
                                    v_a_1778_,
                                    v_a_1779_,
                                    v_a_1780_,
                                    v_a_1781_,
                                );
                                if lean_obj_tag(v___x_1823_) == 0 {
                                    v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
                                    lean_inc(v_a_1824_);
                                    lean_dec_ref_known(v___x_1823_, 1);
                                    if lean_obj_tag(v_a_1824_) == 1 {
                                        lean_dec_ref(v_type_1771_);
                                        v_val_1825_ = lean_ctor_get(v_a_1824_, 0);
                                        v_isSharedCheck_1850_ =
                                            (!lean_is_exclusive(v_a_1824_)) as u8;
                                        if v_isSharedCheck_1850_ == 0 {
                                            v___x_1827_ = v_a_1824_;
                                            v_isShared_1828_ = v_isSharedCheck_1850_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_val_1825_);
                                            lean_dec(v_a_1824_);
                                            v___x_1827_ = lean_box(0);
                                            v_isShared_1828_ = v_isSharedCheck_1850_;
                                            state = 10;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_1824_);
                                        v___x_1851_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1771_, v_a_1772_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
                                        if lean_obj_tag(v___x_1851_) == 0 {
                                            v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
                                            v_isSharedCheck_1886_ =
                                                (!lean_is_exclusive(v___x_1851_)) as u8;
                                            if v_isSharedCheck_1886_ == 0 {
                                                v___x_1854_ = v___x_1851_;
                                                v_isShared_1855_ = v_isSharedCheck_1886_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1852_);
                                                lean_dec(v___x_1851_);
                                                v___x_1854_ = lean_box(0);
                                                v_isShared_1855_ = v_isSharedCheck_1886_;
                                                state = 16;
                                                continue;
                                            }
                                        } else {
                                            v_a_1887_ = lean_ctor_get(v___x_1851_, 0);
                                            v_isSharedCheck_1894_ =
                                                (!lean_is_exclusive(v___x_1851_)) as u8;
                                            if v_isSharedCheck_1894_ == 0 {
                                                v___x_1889_ = v___x_1851_;
                                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                                state = 24;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1887_);
                                                lean_dec(v___x_1851_);
                                                v___x_1889_ = lean_box(0);
                                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_type_1771_);
                                    v_a_1895_ = lean_ctor_get(v___x_1823_, 0);
                                    v_isSharedCheck_1902_ = (!lean_is_exclusive(v___x_1823_)) as u8;
                                    if v_isSharedCheck_1902_ == 0 {
                                        v___x_1897_ = v___x_1823_;
                                        v_isShared_1898_ = v_isSharedCheck_1902_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1895_);
                                        lean_dec(v___x_1823_);
                                        v___x_1897_ = lean_box(0);
                                        v_isShared_1898_ = v_isSharedCheck_1902_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_type_1771_);
                            v_a_1903_ = lean_ctor_get(v___x_1794_, 0);
                            v_isSharedCheck_1910_ = (!lean_is_exclusive(v___x_1794_)) as u8;
                            if v_isSharedCheck_1910_ == 0 {
                                v___x_1905_ = v___x_1794_;
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_1903_);
                                lean_dec(v___x_1794_);
                                v___x_1905_ = lean_box(0);
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_1771_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_1785_, 1);
                    lean_dec_ref(v_type_1771_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1790_ = lean_box(0);
                if v_isShared_1788_ == 0 {
                    lean_ctor_set(v___x_1787_, 0, v___x_1790_);
                    v___x_1792_ = v___x_1787_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1792_;
            }
            4 => {
                v___x_1800_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_val_1796_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                lean_dec(v_val_1796_);
                if lean_obj_tag(v___x_1800_) == 0 {
                    v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
                    v_isSharedCheck_1813_ = (!lean_is_exclusive(v___x_1800_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v___x_1803_ = v___x_1800_;
                        v_isShared_1804_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1801_);
                        lean_dec(v___x_1800_);
                        v___x_1803_ = lean_box(0);
                        v_isShared_1804_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1798_);
                    v_a_1814_ = lean_ctor_get(v___x_1800_, 0);
                    v_isSharedCheck_1821_ = (!lean_is_exclusive(v___x_1800_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1816_ = v___x_1800_;
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1814_);
                        lean_dec(v___x_1800_);
                        v___x_1816_ = lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_toSemiring_1805_ = lean_ctor_get(v_a_1801_, 0);
                lean_inc_ref(v_toSemiring_1805_);
                lean_dec(v_a_1801_);
                v_semiringInst_1806_ = lean_ctor_get(v_toSemiring_1805_, 3);
                lean_inc_ref(v_semiringInst_1806_);
                lean_dec_ref(v_toSemiring_1805_);
                if v_isShared_1799_ == 0 {
                    lean_ctor_set(v___x_1798_, 0, v_semiringInst_1806_);
                    v___x_1808_ = v___x_1798_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_semiringInst_1806_);
                    v___x_1808_ = v_reuseFailAlloc_1812_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1804_ == 0 {
                    lean_ctor_set(v___x_1803_, 0, v___x_1808_);
                    v___x_1810_ = v___x_1803_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1810_;
            }
            8 => {
                if v_isShared_1817_ == 0 {
                    v___x_1819_ = v___x_1816_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1819_;
            }
            10 => {
                v___x_1829_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
                    v_val_1825_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                lean_dec(v_val_1825_);
                if lean_obj_tag(v___x_1829_) == 0 {
                    v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1841_ = (!lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1841_ == 0 {
                        v___x_1832_ = v___x_1829_;
                        v_isShared_1833_ = v_isSharedCheck_1841_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1830_);
                        lean_dec(v___x_1829_);
                        v___x_1832_ = lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1841_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1827_);
                    v_a_1842_ = lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1849_ = (!lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1849_ == 0 {
                        v___x_1844_ = v___x_1829_;
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_1842_);
                        lean_dec(v___x_1829_);
                        v___x_1844_ = lean_box(0);
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_semiringInst_1834_ = lean_ctor_get(v_a_1830_, 4);
                lean_inc_ref(v_semiringInst_1834_);
                lean_dec(v_a_1830_);
                if v_isShared_1828_ == 0 {
                    lean_ctor_set(v___x_1827_, 0, v_semiringInst_1834_);
                    v___x_1836_ = v___x_1827_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_semiringInst_1834_);
                    v___x_1836_ = v_reuseFailAlloc_1840_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1833_ == 0 {
                    lean_ctor_set(v___x_1832_, 0, v___x_1836_);
                    v___x_1838_ = v___x_1832_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1838_;
            }
            14 => {
                if v_isShared_1845_ == 0 {
                    v___x_1847_ = v___x_1844_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1847_;
            }
            16 => {
                if lean_obj_tag(v_a_1852_) == 1 {
                    lean_del_object(v___x_1854_);
                    v_val_1856_ = lean_ctor_get(v_a_1852_, 0);
                    v_isSharedCheck_1881_ = (!lean_is_exclusive(v_a_1852_)) as u8;
                    if v_isSharedCheck_1881_ == 0 {
                        v___x_1858_ = v_a_1852_;
                        v_isShared_1859_ = v_isSharedCheck_1881_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_val_1856_);
                        lean_dec(v_a_1852_);
                        v___x_1858_ = lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1881_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1852_);
                    v___x_1882_ = lean_box(0);
                    if v_isShared_1855_ == 0 {
                        lean_ctor_set(v___x_1854_, 0, v___x_1882_);
                        v___x_1884_ = v___x_1854_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
                        v___x_1884_ = v_reuseFailAlloc_1885_;
                        state = 23;
                        continue;
                    }
                }
            }
            17 => {
                v___x_1860_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(
                    v_val_1856_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                lean_dec(v_val_1856_);
                if lean_obj_tag(v___x_1860_) == 0 {
                    v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1872_ = (!lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1872_ == 0 {
                        v___x_1863_ = v___x_1860_;
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_1861_);
                        lean_dec(v___x_1860_);
                        v___x_1863_ = lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1858_);
                    v_a_1873_ = lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1880_ = (!lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1875_ = v___x_1860_;
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_1873_);
                        lean_dec(v___x_1860_);
                        v___x_1875_ = lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                v_semiringInst_1865_ = lean_ctor_get(v_a_1861_, 3);
                lean_inc_ref(v_semiringInst_1865_);
                lean_dec(v_a_1861_);
                if v_isShared_1859_ == 0 {
                    lean_ctor_set(v___x_1858_, 0, v_semiringInst_1865_);
                    v___x_1867_ = v___x_1858_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_semiringInst_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1871_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1864_ == 0 {
                    lean_ctor_set(v___x_1863_, 0, v___x_1867_);
                    v___x_1869_ = v___x_1863_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
                    v___x_1869_ = v_reuseFailAlloc_1870_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1869_;
            }
            21 => {
                if v_isShared_1876_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1878_;
            }
            23 => {
                return v___x_1884_;
            }
            24 => {
                if v_isShared_1890_ == 0 {
                    v___x_1892_ = v___x_1889_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1892_;
            }
            26 => {
                if v_isShared_1898_ == 0 {
                    v___x_1900_ = v___x_1897_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1900_;
            }
            28 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1908_;
            }
            30 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(
    mut v_type_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
    mut v_a_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
    mut v_a_1930_: *mut LeanObject,
    mut v_a_1931_: *mut LeanObject,
    mut v_a_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
    lean_dec(v_a_1932_);
    lean_dec_ref(v_a_1931_);
    lean_dec(v_a_1930_);
    lean_dec_ref(v_a_1929_);
    lean_dec(v_a_1928_);
    lean_dec_ref(v_a_1927_);
    lean_dec(v_a_1926_);
    lean_dec_ref(v_a_1925_);
    lean_dec(v_a_1924_);
    lean_dec(v_a_1923_);
    return v_res_1934_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(
    mut v_a_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v_arg_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u8 = 0;
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1949_ = l_Lean_Expr_cleanupAnnotations(v_a_1940_);
                v___x_1950_ = l_Lean_Expr_isApp(v___x_1949_);
                if v___x_1950_ == 0 {
                    lean_dec_ref(v___x_1949_);
                    state = 1;
                    continue;
                } else {
                    v___x_1951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1949_);
                    v___x_1952_ = l_Lean_Expr_isApp(v___x_1951_);
                    if v___x_1952_ == 0 {
                        lean_dec_ref(v___x_1951_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1953_ = lean_ctor_get(v___x_1951_, 1);
                        lean_inc_ref(v_arg_1953_);
                        v___x_1954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1951_);
                        v___x_1955_ = l_Lean_Expr_isApp(v___x_1954_);
                        if v___x_1955_ == 0 {
                            lean_dec_ref(v___x_1954_);
                            lean_dec_ref(v_arg_1953_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1954_);
                            v___x_1957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2;
                            v___x_1958_ = l_Lean_Expr_isConstOf(v___x_1956_, v___x_1957_);
                            lean_dec_ref(v___x_1956_);
                            if v___x_1958_ == 0 {
                                lean_dec_ref(v_arg_1953_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1959_ = l_Lean_Meta_getNatValue_x3f(
                                    v_arg_1953_,
                                    v_a_1941_,
                                    v_a_1942_,
                                    v_a_1943_,
                                    v_a_1944_,
                                );
                                lean_dec_ref(v_arg_1953_);
                                return v___x_1959_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1947_ = lean_box(0);
                v___x_1948_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1948_, 0, v___x_1947_);
                return v___x_1948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1966_: *mut LeanObject = core::ptr::null_mut();
    v_res_1966_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(
            v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_,
        );
    lean_dec(v_a_1964_);
    lean_dec_ref(v_a_1963_);
    lean_dec(v_a_1962_);
    lean_dec_ref(v_a_1961_);
    return v_res_1966_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateMul(
    mut v_e_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
    mut v_a_2000_: *mut LeanObject,
    mut v_a_2001_: *mut LeanObject,
    mut v_a_2002_: *mut LeanObject,
    mut v_a_2003_: *mut LeanObject,
    mut v_a_2004_: *mut LeanObject,
    mut v_a_2005_: *mut LeanObject,
    mut v_a_2006_: *mut LeanObject,
    mut v_a_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v_arg_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v_arg_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v_arg_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v_arg_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v_arg_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v_val_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v_val_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v_val_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_a_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_a_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v_a_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_unused_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u8 = 0;
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_a_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1997_);
                v___x_2012_ = l_Lean_Expr_cleanupAnnotations(v_e_1997_);
                v___x_2013_ = l_Lean_Expr_isApp(v___x_2012_);
                if v___x_2013_ == 0 {
                    lean_dec_ref(v___x_2012_);
                    lean_dec_ref(v_e_1997_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2014_ = lean_ctor_get(v___x_2012_, 1);
                    lean_inc_ref(v_arg_2014_);
                    v___x_2015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2012_);
                    v___x_2016_ = l_Lean_Expr_isApp(v___x_2015_);
                    if v___x_2016_ == 0 {
                        lean_dec_ref(v___x_2015_);
                        lean_dec_ref(v_arg_2014_);
                        lean_dec_ref(v_e_1997_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2017_ = lean_ctor_get(v___x_2015_, 1);
                        lean_inc_ref(v_arg_2017_);
                        v___x_2018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2015_);
                        v___x_2019_ = l_Lean_Expr_isApp(v___x_2018_);
                        if v___x_2019_ == 0 {
                            lean_dec_ref(v___x_2018_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2018_);
                            v___x_2021_ = l_Lean_Expr_isApp(v___x_2020_);
                            if v___x_2021_ == 0 {
                                lean_dec_ref(v___x_2020_);
                                lean_dec_ref(v_arg_2017_);
                                lean_dec_ref(v_arg_2014_);
                                lean_dec_ref(v_e_1997_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2022_ = lean_ctor_get(v___x_2020_, 1);
                                lean_inc_ref(v_arg_2022_);
                                v___x_2023_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2020_);
                                v___x_2024_ = l_Lean_Expr_isApp(v___x_2023_);
                                if v___x_2024_ == 0 {
                                    lean_dec_ref(v___x_2023_);
                                    lean_dec_ref(v_arg_2022_);
                                    lean_dec_ref(v_arg_2017_);
                                    lean_dec_ref(v_arg_2014_);
                                    lean_dec_ref(v_e_1997_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2025_ = lean_ctor_get(v___x_2023_, 1);
                                    lean_inc_ref(v_arg_2025_);
                                    v___x_2026_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2023_);
                                    v___x_2027_ = l_Lean_Expr_isApp(v___x_2026_);
                                    if v___x_2027_ == 0 {
                                        lean_dec_ref(v___x_2026_);
                                        lean_dec_ref(v_arg_2025_);
                                        lean_dec_ref(v_arg_2022_);
                                        lean_dec_ref(v_arg_2017_);
                                        lean_dec_ref(v_arg_2014_);
                                        lean_dec_ref(v_e_1997_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2028_ = lean_ctor_get(v___x_2026_, 1);
                                        lean_inc_ref(v_arg_2028_);
                                        v___x_2029_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2026_);
                                        v___x_2030_ =
                                            l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
                                        v___x_2031_ =
                                            l_Lean_Expr_isConstOf(v___x_2029_, v___x_2030_);
                                        if v___x_2031_ == 0 {
                                            lean_dec_ref(v___x_2029_);
                                            lean_dec_ref(v_arg_2028_);
                                            lean_dec_ref(v_arg_2025_);
                                            lean_dec_ref(v_arg_2022_);
                                            lean_dec_ref(v_arg_2017_);
                                            lean_dec_ref(v_arg_2014_);
                                            lean_dec_ref(v_e_1997_);
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc_ref(v_arg_2028_);
                                            v___x_2032_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_arg_2028_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                                            if lean_obj_tag(v___x_2032_) == 0 {
                                                v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
                                                v_isSharedCheck_2207_ =
                                                    (!lean_is_exclusive(v___x_2032_)) as u8;
                                                if v_isSharedCheck_2207_ == 0 {
                                                    v___x_2035_ = v___x_2032_;
                                                    v_isShared_2036_ = v_isSharedCheck_2207_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2033_);
                                                    lean_dec(v___x_2032_);
                                                    v___x_2035_ = lean_box(0);
                                                    v_isShared_2036_ = v_isSharedCheck_2207_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2029_);
                                                lean_dec_ref(v_arg_2028_);
                                                lean_dec_ref(v_arg_2025_);
                                                lean_dec_ref(v_arg_2022_);
                                                lean_dec_ref(v_arg_2017_);
                                                lean_dec_ref(v_arg_2014_);
                                                lean_dec_ref(v_e_1997_);
                                                v_a_2208_ = lean_ctor_get(v___x_2032_, 0);
                                                v_isSharedCheck_2215_ =
                                                    (!lean_is_exclusive(v___x_2032_)) as u8;
                                                if v_isSharedCheck_2215_ == 0 {
                                                    v___x_2210_ = v___x_2032_;
                                                    v_isShared_2211_ = v_isSharedCheck_2215_;
                                                    state = 33;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2208_);
                                                    lean_dec(v___x_2032_);
                                                    v___x_2210_ = lean_box(0);
                                                    v_isShared_2211_ = v_isSharedCheck_2215_;
                                                    state = 33;
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
                v___x_2010_ = lean_box(0);
                v___x_2011_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2011_, 0, v___x_2010_);
                return v___x_2011_;
            }
            2 => {
                if lean_obj_tag(v_a_2033_) == 1 {
                    v_val_2037_ = lean_ctor_get(v_a_2033_, 0);
                    lean_inc(v_val_2037_);
                    lean_dec_ref_known(v_a_2033_, 1);
                    v___x_2201_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2028_,
                            v_arg_2025_,
                        );
                    lean_dec_ref(v_arg_2025_);
                    if v___x_2201_ == 0 {
                        lean_dec_ref(v_arg_2022_);
                        v___y_2039_ = v___x_2201_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2202_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_arg_2028_,
                                v_arg_2022_,
                            );
                        lean_dec_ref(v_arg_2022_);
                        v___y_2039_ = v___x_2202_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2033_);
                    lean_dec_ref(v___x_2029_);
                    lean_dec_ref(v_arg_2028_);
                    lean_dec_ref(v_arg_2025_);
                    lean_dec_ref(v_arg_2022_);
                    lean_dec_ref(v_arg_2017_);
                    lean_dec_ref(v_arg_2014_);
                    lean_dec_ref(v_e_1997_);
                    v___x_2203_ = lean_box(0);
                    if v_isShared_2036_ == 0 {
                        lean_ctor_set(v___x_2035_, 0, v___x_2203_);
                        v___x_2205_ = v___x_2035_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
                        v___x_2205_ = v_reuseFailAlloc_2206_;
                        state = 32;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_2039_ == 0 {
                    lean_dec(v_val_2037_);
                    lean_dec_ref(v___x_2029_);
                    lean_dec_ref(v_arg_2028_);
                    lean_dec_ref(v_arg_2017_);
                    lean_dec_ref(v_arg_2014_);
                    lean_dec_ref(v_e_1997_);
                    v___x_2040_ = lean_box(0);
                    if v_isShared_2036_ == 0 {
                        lean_ctor_set(v___x_2035_, 0, v___x_2040_);
                        v___x_2042_ = v___x_2035_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
                        v___x_2042_ = v_reuseFailAlloc_2043_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2044_ = l_Lean_Expr_constLevels_x21(v___x_2029_);
                    lean_dec_ref(v___x_2029_);
                    if lean_obj_tag(v___x_2044_) == 1 {
                        lean_del_object(v___x_2035_);
                        v_head_2045_ = lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2195_ = (!lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2195_ == 0 {
                            v_unused_2196_ = lean_ctor_get(v___x_2044_, 1);
                            lean_dec(v_unused_2196_);
                            v___x_2047_ = v___x_2044_;
                            v_isShared_2048_ = v_isSharedCheck_2195_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_head_2045_);
                            lean_dec(v___x_2044_);
                            v___x_2047_ = lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2195_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2044_);
                        lean_dec(v_val_2037_);
                        lean_dec_ref(v_arg_2028_);
                        lean_dec_ref(v_arg_2017_);
                        lean_dec_ref(v_arg_2014_);
                        lean_dec_ref(v_e_1997_);
                        v___x_2197_ = lean_box(0);
                        if v_isShared_2036_ == 0 {
                            lean_ctor_set(v___x_2035_, 0, v___x_2197_);
                            v___x_2199_ = v___x_2035_;
                            state = 31;
                            continue;
                        } else {
                            v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                            v___x_2199_ = v_reuseFailAlloc_2200_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2042_;
            }
            5 => {
                v___x_2049_ = lean_st_ref_get(v_a_1998_);
                lean_inc_ref(v_arg_2017_);
                v___x_2050_ = l_Lean_Meta_Grind_Goal_getRoot(
                    v___x_2049_,
                    v_arg_2017_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                lean_dec(v___x_2049_);
                if lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
                    lean_inc(v_a_2051_);
                    lean_dec_ref_known(v___x_2050_, 1);
                    v___x_2052_ = lean_st_ref_get(v_a_1998_);
                    lean_inc_ref(v_arg_2014_);
                    v___x_2053_ = l_Lean_Meta_Grind_Goal_getRoot(
                        v___x_2052_,
                        v_arg_2014_,
                        v_a_2004_,
                        v_a_2005_,
                        v_a_2006_,
                        v_a_2007_,
                    );
                    lean_dec(v___x_2052_);
                    if lean_obj_tag(v___x_2053_) == 0 {
                        v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
                        lean_inc(v_a_2054_);
                        lean_dec_ref_known(v___x_2053_, 1);
                        lean_inc(v_a_2051_);
                        v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_2051_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                        if lean_obj_tag(v___x_2055_) == 0 {
                            v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
                            v_isSharedCheck_2170_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                            if v_isSharedCheck_2170_ == 0 {
                                v___x_2058_ = v___x_2055_;
                                v_isShared_2059_ = v_isSharedCheck_2170_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2056_);
                                lean_dec(v___x_2055_);
                                v___x_2058_ = lean_box(0);
                                v_isShared_2059_ = v_isSharedCheck_2170_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2054_);
                            lean_dec(v_a_2051_);
                            lean_del_object(v___x_2047_);
                            lean_dec(v_head_2045_);
                            lean_dec(v_val_2037_);
                            lean_dec_ref(v_arg_2028_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            v_a_2171_ = lean_ctor_get(v___x_2055_, 0);
                            v_isSharedCheck_2178_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                            if v_isSharedCheck_2178_ == 0 {
                                v___x_2173_ = v___x_2055_;
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_2171_);
                                lean_dec(v___x_2055_);
                                v___x_2173_ = lean_box(0);
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2051_);
                        lean_del_object(v___x_2047_);
                        lean_dec(v_head_2045_);
                        lean_dec(v_val_2037_);
                        lean_dec_ref(v_arg_2028_);
                        lean_dec_ref(v_arg_2017_);
                        lean_dec_ref(v_arg_2014_);
                        lean_dec_ref(v_e_1997_);
                        v_a_2179_ = lean_ctor_get(v___x_2053_, 0);
                        v_isSharedCheck_2186_ = (!lean_is_exclusive(v___x_2053_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2181_ = v___x_2053_;
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_2179_);
                            lean_dec(v___x_2053_);
                            v___x_2181_ = lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2047_);
                    lean_dec(v_head_2045_);
                    lean_dec(v_val_2037_);
                    lean_dec_ref(v_arg_2028_);
                    lean_dec_ref(v_arg_2017_);
                    lean_dec_ref(v_arg_2014_);
                    lean_dec_ref(v_e_1997_);
                    v_a_2187_ = lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2194_ = (!lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v___x_2050_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_2187_);
                        lean_dec(v___x_2050_);
                        v___x_2189_ = lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 29;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_2056_) == 1 {
                    lean_dec(v_a_2054_);
                    v_val_2060_ = lean_ctor_get(v_a_2056_, 0);
                    lean_inc(v_val_2060_);
                    lean_dec_ref_known(v_a_2056_, 1);
                    v___x_2061_ = lean_unsigned_to_nat(0);
                    v___x_2062_ = lean_nat_dec_eq(v_val_2060_, v___x_2061_);
                    if v___x_2062_ == 0 {
                        v___x_2063_ = lean_unsigned_to_nat(1);
                        v___x_2064_ = lean_nat_dec_eq(v_val_2060_, v___x_2063_);
                        lean_dec(v_val_2060_);
                        if v___x_2064_ == 0 {
                            lean_dec(v_a_2051_);
                            lean_del_object(v___x_2047_);
                            lean_dec(v_head_2045_);
                            lean_dec(v_val_2037_);
                            lean_dec_ref(v_arg_2028_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            v___x_2065_ = lean_box(0);
                            if v_isShared_2059_ == 0 {
                                lean_ctor_set(v___x_2058_, 0, v___x_2065_);
                                v___x_2067_ = v___x_2058_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
                                v___x_2067_ = v_reuseFailAlloc_2068_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2058_);
                            lean_inc(v_a_2007_);
                            lean_inc_ref(v_a_2006_);
                            lean_inc(v_a_2005_);
                            lean_inc_ref(v_a_2004_);
                            lean_inc(v_a_2003_);
                            lean_inc_ref(v_a_2002_);
                            lean_inc(v_a_2001_);
                            lean_inc_ref(v_a_2000_);
                            lean_inc(v_a_1999_);
                            lean_inc(v_a_1998_);
                            lean_inc_ref(v_arg_2017_);
                            v___x_2069_ = lean_grind_mk_eq_proof(
                                v_arg_2017_,
                                v_a_2051_,
                                v_a_1998_,
                                v_a_1999_,
                                v_a_2000_,
                                v_a_2001_,
                                v_a_2002_,
                                v_a_2003_,
                                v_a_2004_,
                                v_a_2005_,
                                v_a_2006_,
                                v_a_2007_,
                            );
                            if lean_obj_tag(v___x_2069_) == 0 {
                                v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
                                lean_inc(v_a_2070_);
                                lean_dec_ref_known(v___x_2069_, 1);
                                v___x_2071_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
                                v___x_2072_ = lean_box(0);
                                if v_isShared_2048_ == 0 {
                                    lean_ctor_set(v___x_2047_, 1, v___x_2072_);
                                    v___x_2074_ = v___x_2047_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_head_2045_);
                                    lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2072_);
                                    v___x_2074_ = v_reuseFailAlloc_2078_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_2047_);
                                lean_dec(v_head_2045_);
                                lean_dec(v_val_2037_);
                                lean_dec_ref(v_arg_2028_);
                                lean_dec_ref(v_arg_2017_);
                                lean_dec_ref(v_arg_2014_);
                                lean_dec_ref(v_e_1997_);
                                v_a_2079_ = lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2086_ = (!lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2086_ == 0 {
                                    v___x_2081_ = v___x_2069_;
                                    v_isShared_2082_ = v_isSharedCheck_2086_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2079_);
                                    lean_dec(v___x_2069_);
                                    v___x_2081_ = lean_box(0);
                                    v_isShared_2082_ = v_isSharedCheck_2086_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_2060_);
                        lean_del_object(v___x_2058_);
                        lean_inc(v_a_2007_);
                        lean_inc_ref(v_a_2006_);
                        lean_inc(v_a_2005_);
                        lean_inc_ref(v_a_2004_);
                        lean_inc(v_a_2003_);
                        lean_inc_ref(v_a_2002_);
                        lean_inc(v_a_2001_);
                        lean_inc_ref(v_a_2000_);
                        lean_inc(v_a_1999_);
                        lean_inc(v_a_1998_);
                        lean_inc(v_a_2051_);
                        lean_inc_ref(v_arg_2017_);
                        v___x_2087_ = lean_grind_mk_eq_proof(
                            v_arg_2017_,
                            v_a_2051_,
                            v_a_1998_,
                            v_a_1999_,
                            v_a_2000_,
                            v_a_2001_,
                            v_a_2002_,
                            v_a_2003_,
                            v_a_2004_,
                            v_a_2005_,
                            v_a_2006_,
                            v_a_2007_,
                        );
                        if lean_obj_tag(v___x_2087_) == 0 {
                            v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
                            lean_inc(v_a_2088_);
                            lean_dec_ref_known(v___x_2087_, 1);
                            v___x_2089_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
                            v___x_2090_ = lean_box(0);
                            if v_isShared_2048_ == 0 {
                                lean_ctor_set(v___x_2047_, 1, v___x_2090_);
                                v___x_2092_ = v___x_2047_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_head_2045_);
                                lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2090_);
                                v___x_2092_ = v_reuseFailAlloc_2097_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2051_);
                            lean_del_object(v___x_2047_);
                            lean_dec(v_head_2045_);
                            lean_dec(v_val_2037_);
                            lean_dec_ref(v_arg_2028_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            v_a_2098_ = lean_ctor_get(v___x_2087_, 0);
                            v_isSharedCheck_2105_ = (!lean_is_exclusive(v___x_2087_)) as u8;
                            if v_isSharedCheck_2105_ == 0 {
                                v___x_2100_ = v___x_2087_;
                                v_isShared_2101_ = v_isSharedCheck_2105_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2098_);
                                lean_dec(v___x_2087_);
                                v___x_2100_ = lean_box(0);
                                v_isShared_2101_ = v_isSharedCheck_2105_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2058_);
                    lean_dec(v_a_2056_);
                    lean_dec(v_a_2051_);
                    lean_inc(v_a_2054_);
                    v___x_2106_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_2054_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                    if lean_obj_tag(v___x_2106_) == 0 {
                        v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
                        v_isSharedCheck_2161_ = (!lean_is_exclusive(v___x_2106_)) as u8;
                        if v_isSharedCheck_2161_ == 0 {
                            v___x_2109_ = v___x_2106_;
                            v_isShared_2110_ = v_isSharedCheck_2161_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2107_);
                            lean_dec(v___x_2106_);
                            v___x_2109_ = lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2161_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2054_);
                        lean_del_object(v___x_2047_);
                        lean_dec(v_head_2045_);
                        lean_dec(v_val_2037_);
                        lean_dec_ref(v_arg_2028_);
                        lean_dec_ref(v_arg_2017_);
                        lean_dec_ref(v_arg_2014_);
                        lean_dec_ref(v_e_1997_);
                        v_a_2162_ = lean_ctor_get(v___x_2106_, 0);
                        v_isSharedCheck_2169_ = (!lean_is_exclusive(v___x_2106_)) as u8;
                        if v_isSharedCheck_2169_ == 0 {
                            v___x_2164_ = v___x_2106_;
                            v_isShared_2165_ = v_isSharedCheck_2169_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_2162_);
                            lean_dec(v___x_2106_);
                            v___x_2164_ = lean_box(0);
                            v_isShared_2165_ = v_isSharedCheck_2169_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_2067_;
            }
            8 => {
                v___x_2075_ = l_Lean_mkConst(v___x_2071_, v___x_2074_);
                lean_inc_ref(v_arg_2014_);
                v___x_2076_ = l_Lean_mkApp5(
                    v___x_2075_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2070_,
                );
                v___x_2077_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_arg_2014_,
                    v___x_2076_,
                    v___x_2062_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2077_;
            }
            9 => {
                if v_isShared_2082_ == 0 {
                    v___x_2084_ = v___x_2081_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
                    v___x_2084_ = v_reuseFailAlloc_2085_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2084_;
            }
            11 => {
                v___x_2093_ = l_Lean_mkConst(v___x_2089_, v___x_2092_);
                v___x_2094_ = l_Lean_mkApp5(
                    v___x_2093_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2088_,
                );
                v___x_2095_ = 0;
                v___x_2096_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_a_2051_,
                    v___x_2094_,
                    v___x_2095_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2096_;
            }
            12 => {
                if v_isShared_2101_ == 0 {
                    v___x_2103_ = v___x_2100_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2103_;
            }
            14 => {
                if lean_obj_tag(v_a_2107_) == 1 {
                    v_val_2111_ = lean_ctor_get(v_a_2107_, 0);
                    lean_inc(v_val_2111_);
                    lean_dec_ref_known(v_a_2107_, 1);
                    v___x_2112_ = lean_unsigned_to_nat(0);
                    v___x_2113_ = lean_nat_dec_eq(v_val_2111_, v___x_2112_);
                    if v___x_2113_ == 0 {
                        v___x_2114_ = lean_unsigned_to_nat(1);
                        v___x_2115_ = lean_nat_dec_eq(v_val_2111_, v___x_2114_);
                        lean_dec(v_val_2111_);
                        if v___x_2115_ == 0 {
                            lean_dec(v_a_2054_);
                            lean_del_object(v___x_2047_);
                            lean_dec(v_head_2045_);
                            lean_dec(v_val_2037_);
                            lean_dec_ref(v_arg_2028_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            v___x_2116_ = lean_box(0);
                            if v_isShared_2110_ == 0 {
                                lean_ctor_set(v___x_2109_, 0, v___x_2116_);
                                v___x_2118_ = v___x_2109_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                                v___x_2118_ = v_reuseFailAlloc_2119_;
                                state = 15;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2109_);
                            lean_inc(v_a_2007_);
                            lean_inc_ref(v_a_2006_);
                            lean_inc(v_a_2005_);
                            lean_inc_ref(v_a_2004_);
                            lean_inc(v_a_2003_);
                            lean_inc_ref(v_a_2002_);
                            lean_inc(v_a_2001_);
                            lean_inc_ref(v_a_2000_);
                            lean_inc(v_a_1999_);
                            lean_inc(v_a_1998_);
                            lean_inc_ref(v_arg_2014_);
                            v___x_2120_ = lean_grind_mk_eq_proof(
                                v_arg_2014_,
                                v_a_2054_,
                                v_a_1998_,
                                v_a_1999_,
                                v_a_2000_,
                                v_a_2001_,
                                v_a_2002_,
                                v_a_2003_,
                                v_a_2004_,
                                v_a_2005_,
                                v_a_2006_,
                                v_a_2007_,
                            );
                            if lean_obj_tag(v___x_2120_) == 0 {
                                v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
                                lean_inc(v_a_2121_);
                                lean_dec_ref_known(v___x_2120_, 1);
                                v___x_2122_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
                                v___x_2123_ = lean_box(0);
                                if v_isShared_2048_ == 0 {
                                    lean_ctor_set(v___x_2047_, 1, v___x_2123_);
                                    v___x_2125_ = v___x_2047_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_head_2045_);
                                    lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2123_);
                                    v___x_2125_ = v_reuseFailAlloc_2129_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_2047_);
                                lean_dec(v_head_2045_);
                                lean_dec(v_val_2037_);
                                lean_dec_ref(v_arg_2028_);
                                lean_dec_ref(v_arg_2017_);
                                lean_dec_ref(v_arg_2014_);
                                lean_dec_ref(v_e_1997_);
                                v_a_2130_ = lean_ctor_get(v___x_2120_, 0);
                                v_isSharedCheck_2137_ = (!lean_is_exclusive(v___x_2120_)) as u8;
                                if v_isSharedCheck_2137_ == 0 {
                                    v___x_2132_ = v___x_2120_;
                                    v_isShared_2133_ = v_isSharedCheck_2137_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_2130_);
                                    lean_dec(v___x_2120_);
                                    v___x_2132_ = lean_box(0);
                                    v_isShared_2133_ = v_isSharedCheck_2137_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_2111_);
                        lean_del_object(v___x_2109_);
                        lean_inc(v_a_2007_);
                        lean_inc_ref(v_a_2006_);
                        lean_inc(v_a_2005_);
                        lean_inc_ref(v_a_2004_);
                        lean_inc(v_a_2003_);
                        lean_inc_ref(v_a_2002_);
                        lean_inc(v_a_2001_);
                        lean_inc_ref(v_a_2000_);
                        lean_inc(v_a_1999_);
                        lean_inc(v_a_1998_);
                        lean_inc(v_a_2054_);
                        lean_inc_ref(v_arg_2014_);
                        v___x_2138_ = lean_grind_mk_eq_proof(
                            v_arg_2014_,
                            v_a_2054_,
                            v_a_1998_,
                            v_a_1999_,
                            v_a_2000_,
                            v_a_2001_,
                            v_a_2002_,
                            v_a_2003_,
                            v_a_2004_,
                            v_a_2005_,
                            v_a_2006_,
                            v_a_2007_,
                        );
                        if lean_obj_tag(v___x_2138_) == 0 {
                            v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
                            lean_inc(v_a_2139_);
                            lean_dec_ref_known(v___x_2138_, 1);
                            v___x_2140_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
                            v___x_2141_ = lean_box(0);
                            if v_isShared_2048_ == 0 {
                                lean_ctor_set(v___x_2047_, 1, v___x_2141_);
                                v___x_2143_ = v___x_2047_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_head_2045_);
                                lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2141_);
                                v___x_2143_ = v_reuseFailAlloc_2148_;
                                state = 19;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2054_);
                            lean_del_object(v___x_2047_);
                            lean_dec(v_head_2045_);
                            lean_dec(v_val_2037_);
                            lean_dec_ref(v_arg_2028_);
                            lean_dec_ref(v_arg_2017_);
                            lean_dec_ref(v_arg_2014_);
                            lean_dec_ref(v_e_1997_);
                            v_a_2149_ = lean_ctor_get(v___x_2138_, 0);
                            v_isSharedCheck_2156_ = (!lean_is_exclusive(v___x_2138_)) as u8;
                            if v_isSharedCheck_2156_ == 0 {
                                v___x_2151_ = v___x_2138_;
                                v_isShared_2152_ = v_isSharedCheck_2156_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_2149_);
                                lean_dec(v___x_2138_);
                                v___x_2151_ = lean_box(0);
                                v_isShared_2152_ = v_isSharedCheck_2156_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_2107_);
                    lean_dec(v_a_2054_);
                    lean_del_object(v___x_2047_);
                    lean_dec(v_head_2045_);
                    lean_dec(v_val_2037_);
                    lean_dec_ref(v_arg_2028_);
                    lean_dec_ref(v_arg_2017_);
                    lean_dec_ref(v_arg_2014_);
                    lean_dec_ref(v_e_1997_);
                    v___x_2157_ = lean_box(0);
                    if v_isShared_2110_ == 0 {
                        lean_ctor_set(v___x_2109_, 0, v___x_2157_);
                        v___x_2159_ = v___x_2109_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
                        v___x_2159_ = v_reuseFailAlloc_2160_;
                        state = 22;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_2118_;
            }
            16 => {
                v___x_2126_ = l_Lean_mkConst(v___x_2122_, v___x_2125_);
                lean_inc_ref(v_arg_2017_);
                v___x_2127_ = l_Lean_mkApp5(
                    v___x_2126_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2121_,
                );
                v___x_2128_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_arg_2017_,
                    v___x_2127_,
                    v___x_2113_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2128_;
            }
            17 => {
                if v_isShared_2133_ == 0 {
                    v___x_2135_ = v___x_2132_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
                    v___x_2135_ = v_reuseFailAlloc_2136_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2135_;
            }
            19 => {
                v___x_2144_ = l_Lean_mkConst(v___x_2140_, v___x_2143_);
                v___x_2145_ = l_Lean_mkApp5(
                    v___x_2144_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2139_,
                );
                v___x_2146_ = 0;
                v___x_2147_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_a_2054_,
                    v___x_2145_,
                    v___x_2146_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2147_;
            }
            20 => {
                if v_isShared_2152_ == 0 {
                    v___x_2154_ = v___x_2151_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2154_;
            }
            22 => {
                return v___x_2159_;
            }
            23 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2167_;
            }
            25 => {
                if v_isShared_2174_ == 0 {
                    v___x_2176_ = v___x_2173_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2176_;
            }
            27 => {
                if v_isShared_2182_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2184_;
            }
            29 => {
                if v_isShared_2190_ == 0 {
                    v___x_2192_ = v___x_2189_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2192_;
            }
            31 => {
                return v___x_2199_;
            }
            32 => {
                return v___x_2205_;
            }
            33 => {
                if v_isShared_2211_ == 0 {
                    v___x_2213_ = v___x_2210_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
                    v___x_2213_ = v_reuseFailAlloc_2214_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateMul___boxed(
    mut v_e_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
    mut v_a_2224_: *mut LeanObject,
    mut v_a_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Meta_Grind_Arith_propagateMul(
        v_e_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_,
        v_a_2224_, v_a_2225_, v_a_2226_,
    );
    lean_dec(v_a_2226_);
    lean_dec_ref(v_a_2225_);
    lean_dec(v_a_2224_);
    lean_dec_ref(v_a_2223_);
    lean_dec(v_a_2222_);
    lean_dec_ref(v_a_2221_);
    lean_dec(v_a_2220_);
    lean_dec_ref(v_a_2219_);
    lean_dec(v_a_2218_);
    lean_dec(v_a_2217_);
    return v_res_2228_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
    v___x_2231_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateMul___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_2232_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2230_, v___x_2231_);
    return v___x_2232_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(
    mut v_a_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2234_: *mut LeanObject = core::ptr::null_mut();
    v_res_2234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
    return v_res_2234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring();
    lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
}
