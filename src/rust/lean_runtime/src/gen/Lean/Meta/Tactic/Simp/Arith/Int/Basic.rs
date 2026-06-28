// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Basic
// Imports: Init.Data.Int.Linear Lean.Util.SortExprs Lean.Meta.IntInstTesters Lean.Meta.AppBuilder Lean.Meta.KExprMap Lean.Data.RArray Lean.Meta.LitValues
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::Linear::{
    initialize_Init_Data_Int_Linear, runtime_initialize_Init_Data_Int_Linear,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::RArray::{
    initialize_Lean_Data_RArray, l_Lean_RArray_ofArray___redArg, l_Lean_RArray_toExpr___redArg,
    runtime_initialize_Lean_Data_RArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkIntAdd, l_Lean_mkIntLit, l_Lean_mkIntMul,
    l_Lean_mkIntNeg, l_Lean_mkIntSub, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::IntInstTesters::{
    initialize_Lean_Meta_IntInstTesters, l_Lean_Meta_DefEq_isInstAddInt,
    l_Lean_Meta_DefEq_isInstDvdInt, l_Lean_Meta_DefEq_isInstHAddInt,
    l_Lean_Meta_DefEq_isInstHMulInt, l_Lean_Meta_DefEq_isInstHSubInt,
    l_Lean_Meta_DefEq_isInstLEInt, l_Lean_Meta_DefEq_isInstLTInt, l_Lean_Meta_DefEq_isInstMulInt,
    l_Lean_Meta_DefEq_isInstNegInt, l_Lean_Meta_DefEq_isInstSubInt,
    runtime_initialize_Lean_Meta_IntInstTesters,
};
use crate::r#gen::Lean::Meta::KExprMap::{
    initialize_Lean_Meta_KExprMap, l_Lean_Meta_KExprMap_find_x3f___redArg,
    l_Lean_Meta_KExprMap_insert___redArg, runtime_initialize_Lean_Meta_KExprMap,
};
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getIntValue_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
use crate::r#gen::Lean::Util::SortExprs::{
    initialize_Lean_Util_SortExprs, l_Lean_sortExprs, runtime_initialize_Lean_Util_SortExprs,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_instReprPoly__lean_repr___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 80, 111, 108, 121, 46, 110, 117, 109,
            0,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__0_value) as *mut LeanObject;
pub static l_Int_Linear_instReprPoly__lean_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__1_value) as *mut LeanObject;
pub static l_Int_Linear_instReprPoly__lean_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__2_value) as *mut LeanObject;
static mut l_Int_Linear_instReprPoly__lean_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_instReprPoly__lean_repr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Int_Linear_instReprPoly__lean_repr___closed__4_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 80, 111, 108, 121, 46, 97, 100, 100,
            0,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__4_value) as *mut LeanObject;
pub static l_Int_Linear_instReprPoly__lean_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__5_value) as *mut LeanObject;
pub static l_Int_Linear_instReprPoly__lean_repr___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__5_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprPoly__lean_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean_repr___closed__6_value) as *mut LeanObject;
pub static l_Int_Linear_instReprPoly__lean___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_Linear_instReprPoly__lean_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_Linear_instReprPoly__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean___closed__0_value) as *mut LeanObject;
pub static mut l_Int_Linear_instReprPoly__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprPoly__lean___closed__0_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 110, 117, 109,
            0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__0_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__1_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__2_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__3_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 118, 97, 114,
            0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__3_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__4_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__4_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__5_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__6_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 97, 100, 100,
            0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__6_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__7_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__7_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__8_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__9_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 115, 117, 98,
            0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__9_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__10_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__10_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__11_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__12_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 110, 101, 103,
            0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__12_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__13_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__14_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__13_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__14_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__15_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108,
            76, 0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__15_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__16_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__16_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__17_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__18_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108,
            82, 0,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__18_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__19_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean_repr___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__19_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_instReprExpr__lean_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean_repr___closed__20_value) as *mut LeanObject;
pub static l_Int_Linear_instReprExpr__lean___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_Linear_instReprExpr__lean_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_Linear_instReprExpr__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean___closed__0_value) as *mut LeanObject;
pub static mut l_Int_Linear_instReprExpr__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instReprExpr__lean___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value: LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [76, 105, 110, 101, 97, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value: LeanStringObject<5> =
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
        m_data: [80, 111, 108, 121, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value: LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value)
                as *mut LeanObject,
            17894584726925916262 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value)
                as *mut LeanObject,
            7489268860741262610 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value: LeanStringObject<11> =
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
        m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value)
                as *mut LeanObject,
            6362876895233142233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value: LeanStringObject<4> =
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
        m_data: [97, 100, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value)
                as *mut LeanObject,
            17894584726925916262 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value)
                as *mut LeanObject,
            8769875647215885763 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Int_ofPoly as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value)
                as *mut LeanObject,
            17894584726925916262 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Int_instToExprPoly: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value: LeanStringObject<5> =
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
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value)
                as *mut LeanObject,
            15921401534301841062 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value: LeanStringObject<4> =
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
        m_data: [118, 97, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value)
                as *mut LeanObject,
            13001077567809478747 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value)
                as *mut LeanObject,
            5978910467259543983 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value: LeanStringObject<4> =
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
        m_data: [115, 117, 98, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value)
                as *mut LeanObject,
            18226053226943377868 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value)
                as *mut LeanObject,
            15268137019634215277 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value: LeanStringObject<5> =
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
        m_data: [109, 117, 108, 76, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value)
                as *mut LeanObject,
            11181467458066963749 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value: LeanStringObject<5> =
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
        m_data: [109, 117, 108, 82, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value)
                as *mut LeanObject,
            2201154472605854024 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Int_ofLinearExpr as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Int_instToExprExpr: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value) as *mut LeanObject,16724526780424158430 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value) as *mut LeanObject,12510133671493592946 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value) as *mut LeanObject,11037448870989407423 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value) as *mut LeanObject,15830134773311339036 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value) as *mut LeanObject,4707481103260653979 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value) as *mut LeanObject,11383192766313517692 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value) as *mut LeanObject,17777553589755654859 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value) as *mut LeanObject,13937624386390108825 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value) as *mut LeanObject,17313347264508353403 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value) as *mut LeanObject,6683391611519377970 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value) as *mut LeanObject,16856108565602861689 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value) as *mut LeanObject,4187025665268973031 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value)
                as *mut LeanObject,
            4106874400896129396 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value)
                as *mut LeanObject,
            7789119480763918796 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value)
                as *mut LeanObject,
            2272833755566510320 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value)
                as *mut LeanObject,
            9426339939459091439 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value)
                as *mut LeanObject,
            1755019837031360842 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value)
                as *mut LeanObject,
            5555145617058846791 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value: LeanStringObject<4> =
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
        m_data: [68, 118, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value: LeanStringObject<4> =
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
        m_data: [100, 118, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value)
                as *mut LeanObject,
            4493959381811283967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value)
                as *mut LeanObject,
            1297950917268934889 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0()
-> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2563_ = lean_unsigned_to_nat(1);
    v___x_2564_ = lean_nat_to_int(v___x_2563_);
    return v___x_2564_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1()
-> *mut LeanObject {
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    v___x_2565_ = lean_unsigned_to_nat(0);
    v___x_2566_ = lean_nat_to_int(v___x_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_k_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v_val_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v_k_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2567_) == 0 {
                    if lean_obj_tag(v_a_2568_) == 0 {
                        v_k_2569_ = lean_ctor_get(v_a_2568_, 0);
                        v_isSharedCheck_2576_ = (!lean_is_exclusive(v_a_2568_)) as u8;
                        if v_isSharedCheck_2576_ == 0 {
                            v___x_2571_ = v_a_2568_;
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_2569_);
                            lean_dec(v_a_2568_);
                            v___x_2571_ = lean_box(0);
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_k_2577_ = lean_ctor_get(v_a_2568_, 0);
                        lean_inc(v_k_2577_);
                        v_v_2578_ = lean_ctor_get(v_a_2568_, 1);
                        lean_inc(v_v_2578_);
                        v_p_2579_ = lean_ctor_get(v_a_2568_, 2);
                        lean_inc_ref(v_p_2579_);
                        lean_dec_ref_known(v_a_2568_, 3);
                        v___x_2580_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                        v___x_2581_ = lean_int_dec_eq(v_k_2577_, v___x_2580_);
                        if v___x_2581_ == 0 {
                            v___x_2582_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2582_, 0, v_v_2578_);
                            v___x_2583_ = lean_alloc_ctor(5, 2, (0) as u32);
                            lean_ctor_set(v___x_2583_, 0, v_k_2577_);
                            lean_ctor_set(v___x_2583_, 1, v___x_2582_);
                            v___x_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2584_, 0, v___x_2583_);
                            v_a_2567_ = v___x_2584_;
                            v_a_2568_ = v_p_2579_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_k_2577_);
                            v___x_2586_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2586_, 0, v_v_2578_);
                            v___x_2587_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2587_, 0, v___x_2586_);
                            v_a_2567_ = v___x_2587_;
                            v_a_2568_ = v_p_2579_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_a_2568_) == 0 {
                        v_val_2589_ = lean_ctor_get(v_a_2567_, 0);
                        lean_inc(v_val_2589_);
                        lean_dec_ref_known(v_a_2567_, 1);
                        v_k_2590_ = lean_ctor_get(v_a_2568_, 0);
                        v_isSharedCheck_2600_ = (!lean_is_exclusive(v_a_2568_)) as u8;
                        if v_isSharedCheck_2600_ == 0 {
                            v___x_2592_ = v_a_2568_;
                            v_isShared_2593_ = v_isSharedCheck_2600_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_k_2590_);
                            lean_dec(v_a_2568_);
                            v___x_2592_ = lean_box(0);
                            v_isShared_2593_ = v_isSharedCheck_2600_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_val_2601_ = lean_ctor_get(v_a_2567_, 0);
                        v_isSharedCheck_2623_ = (!lean_is_exclusive(v_a_2567_)) as u8;
                        if v_isSharedCheck_2623_ == 0 {
                            v___x_2603_ = v_a_2567_;
                            v_isShared_2604_ = v_isSharedCheck_2623_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_2601_);
                            lean_dec(v_a_2567_);
                            v___x_2603_ = lean_box(0);
                            v_isShared_2604_ = v_isSharedCheck_2623_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_k_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2574_;
            }
            3 => {
                v___x_2594_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_2595_ = lean_int_dec_eq(v_k_2590_, v___x_2594_);
                if v___x_2595_ == 0 {
                    if v_isShared_2593_ == 0 {
                        v___x_2597_ = v___x_2592_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_k_2590_);
                        v___x_2597_ = v_reuseFailAlloc_2599_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2592_);
                    lean_dec(v_k_2590_);
                    return v_val_2589_;
                }
            }
            4 => {
                v___x_2598_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2598_, 0, v_val_2589_);
                lean_ctor_set(v___x_2598_, 1, v___x_2597_);
                return v___x_2598_;
            }
            5 => {
                v_k_2605_ = lean_ctor_get(v_a_2568_, 0);
                lean_inc(v_k_2605_);
                v_v_2606_ = lean_ctor_get(v_a_2568_, 1);
                lean_inc(v_v_2606_);
                v_p_2607_ = lean_ctor_get(v_a_2568_, 2);
                lean_inc_ref(v_p_2607_);
                lean_dec_ref_known(v_a_2568_, 3);
                v___x_2608_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                v___x_2609_ = lean_int_dec_eq(v_k_2605_, v___x_2608_);
                if v___x_2609_ == 0 {
                    v___x_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2610_, 0, v_v_2606_);
                    v___x_2611_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2611_, 0, v_k_2605_);
                    lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                    v___x_2612_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2612_, 0, v_val_2601_);
                    lean_ctor_set(v___x_2612_, 1, v___x_2611_);
                    if v_isShared_2604_ == 0 {
                        lean_ctor_set(v___x_2603_, 0, v___x_2612_);
                        v___x_2614_ = v___x_2603_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2612_);
                        v___x_2614_ = v_reuseFailAlloc_2616_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_k_2605_);
                    v___x_2617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2617_, 0, v_v_2606_);
                    v___x_2618_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2618_, 0, v_val_2601_);
                    lean_ctor_set(v___x_2618_, 1, v___x_2617_);
                    if v_isShared_2604_ == 0 {
                        lean_ctor_set(v___x_2603_, 0, v___x_2618_);
                        v___x_2620_ = v___x_2603_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2618_);
                        v___x_2620_ = v_reuseFailAlloc_2622_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_2567_ = v___x_2614_;
                v_a_2568_ = v_p_2607_;
                state = 0;
                continue;
            }
            7 => {
                v_a_2567_ = v___x_2620_;
                v_a_2568_ = v_p_2607_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_toExpr(mut v_p_2624_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    v___x_2625_ = lean_box(0);
    v___x_2626_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(
        v___x_2625_,
        v_p_2624_,
    );
    return v___x_2626_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(
    mut v_a_2627_: *mut LeanObject,
    mut v_x_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2628_) == 0 {
                    v___x_2629_ = lean_box(0);
                    return v___x_2629_;
                } else {
                    v_key_2630_ = lean_ctor_get(v_x_2628_, 0);
                    v_value_2631_ = lean_ctor_get(v_x_2628_, 1);
                    v_tail_2632_ = lean_ctor_get(v_x_2628_, 2);
                    v___x_2633_ = lean_nat_dec_eq(v_key_2630_, v_a_2627_);
                    if v___x_2633_ == 0 {
                        v_x_2628_ = v_tail_2632_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2631_);
                        v___x_2635_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2635_, 0, v_value_2631_);
                        return v___x_2635_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(
    mut v_a_2636_: *mut LeanObject,
    mut v_x_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_2636_, v_x_2637_);
    lean_dec(v_x_2637_);
    lean_dec(v_a_2636_);
    return v_res_2638_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(
    mut v_m_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u64 = 0;
    let mut v___x_2644_: u64 = 0;
    let mut v___x_2645_: u64 = 0;
    let mut v_fold_2646_: u64 = 0;
    let mut v___x_2647_: u64 = 0;
    let mut v___x_2648_: u64 = 0;
    let mut v___x_2649_: u64 = 0;
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v___x_2653_: usize = 0;
    let mut v___x_2654_: usize = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2641_ = lean_ctor_get(v_m_2639_, 1);
    v___x_2642_ = lean_array_get_size(v_buckets_2641_);
    v___x_2643_ = lean_uint64_of_nat(v_a_2640_);
    v___x_2644_ = 32u64;
    v___x_2645_ = lean_uint64_shift_right(v___x_2643_, v___x_2644_);
    v_fold_2646_ = lean_uint64_xor(v___x_2643_, v___x_2645_);
    v___x_2647_ = 16u64;
    v___x_2648_ = lean_uint64_shift_right(v_fold_2646_, v___x_2647_);
    v___x_2649_ = lean_uint64_xor(v_fold_2646_, v___x_2648_);
    v___x_2650_ = lean_uint64_to_usize(v___x_2649_);
    v___x_2651_ = lean_usize_of_nat(v___x_2642_);
    v___x_2652_ = 1usize;
    v___x_2653_ = lean_usize_sub(v___x_2651_, v___x_2652_);
    v___x_2654_ = lean_usize_land(v___x_2650_, v___x_2653_);
    v___x_2655_ = lean_array_uget_borrowed(v_buckets_2641_, v___x_2654_);
    v___x_2656_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_2640_, v___x_2655_);
    return v___x_2656_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(
    mut v_m_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2659_: *mut LeanObject = core::ptr::null_mut();
    v_res_2659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_2657_, v_a_2658_);
    lean_dec(v_a_2658_);
    lean_dec_ref(v_m_2657_);
    return v_res_2659_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(
    mut v_perm_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_val_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_unused_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut v_a_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2698_: u8 = 0;
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_k_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_a_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_2661_) {
                0 => {
                    return v_a_2661_;
                }
                1 => {
                    v_i_2662_ = lean_ctor_get(v_a_2661_, 0);
                    v___x_2663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_2660_, v_i_2662_);
                    if lean_obj_tag(v___x_2663_) == 0 {
                        return v_a_2661_;
                    } else {
                        v_isSharedCheck_2671_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                        if v_isSharedCheck_2671_ == 0 {
                            v_unused_2672_ = lean_ctor_get(v_a_2661_, 0);
                            lean_dec(v_unused_2672_);
                            v___x_2665_ = v_a_2661_;
                            v_isShared_2666_ = v_isSharedCheck_2671_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2661_);
                            v___x_2665_ = lean_box(0);
                            v_isShared_2666_ = v_isSharedCheck_2671_;
                            state = 1;
                            continue;
                        }
                    }
                }
                2 => {
                    v_a_2673_ = lean_ctor_get(v_a_2661_, 0);
                    v_b_2674_ = lean_ctor_get(v_a_2661_, 1);
                    v_isSharedCheck_2683_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                    if v_isSharedCheck_2683_ == 0 {
                        v___x_2676_ = v_a_2661_;
                        v_isShared_2677_ = v_isSharedCheck_2683_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_b_2674_);
                        lean_inc(v_a_2673_);
                        lean_dec(v_a_2661_);
                        v___x_2676_ = lean_box(0);
                        v_isShared_2677_ = v_isSharedCheck_2683_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_a_2684_ = lean_ctor_get(v_a_2661_, 0);
                    v_b_2685_ = lean_ctor_get(v_a_2661_, 1);
                    v_isSharedCheck_2694_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                    if v_isSharedCheck_2694_ == 0 {
                        v___x_2687_ = v_a_2661_;
                        v_isShared_2688_ = v_isSharedCheck_2694_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_b_2685_);
                        lean_inc(v_a_2684_);
                        lean_dec(v_a_2661_);
                        v___x_2687_ = lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2694_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_a_2695_ = lean_ctor_get(v_a_2661_, 0);
                    v_isSharedCheck_2703_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2697_ = v_a_2661_;
                        v_isShared_2698_ = v_isSharedCheck_2703_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2695_);
                        lean_dec(v_a_2661_);
                        v___x_2697_ = lean_box(0);
                        v_isShared_2698_ = v_isSharedCheck_2703_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_k_2704_ = lean_ctor_get(v_a_2661_, 0);
                    v_a_2705_ = lean_ctor_get(v_a_2661_, 1);
                    v_isSharedCheck_2713_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v___x_2707_ = v_a_2661_;
                        v_isShared_2708_ = v_isSharedCheck_2713_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2705_);
                        lean_inc(v_k_2704_);
                        lean_dec(v_a_2661_);
                        v___x_2707_ = lean_box(0);
                        v_isShared_2708_ = v_isSharedCheck_2713_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    v_a_2714_ = lean_ctor_get(v_a_2661_, 0);
                    v_k_2715_ = lean_ctor_get(v_a_2661_, 1);
                    v_isSharedCheck_2723_ = (!lean_is_exclusive(v_a_2661_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2717_ = v_a_2661_;
                        v_isShared_2718_ = v_isSharedCheck_2723_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_k_2715_);
                        lean_inc(v_a_2714_);
                        lean_dec(v_a_2661_);
                        v___x_2717_ = lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2723_;
                        state = 11;
                        continue;
                    }
                }
            },
            1 => {
                v_val_2667_ = lean_ctor_get(v___x_2663_, 0);
                lean_inc(v_val_2667_);
                lean_dec_ref_known(v___x_2663_, 1);
                if v_isShared_2666_ == 0 {
                    lean_ctor_set(v___x_2665_, 0, v_val_2667_);
                    v___x_2669_ = v___x_2665_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_val_2667_);
                    v___x_2669_ = v_reuseFailAlloc_2670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2669_;
            }
            3 => {
                v___x_2678_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_a_2673_);
                v___x_2679_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_b_2674_);
                if v_isShared_2677_ == 0 {
                    lean_ctor_set(v___x_2676_, 1, v___x_2679_);
                    lean_ctor_set(v___x_2676_, 0, v___x_2678_);
                    v___x_2681_ = v___x_2676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2678_);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2681_;
            }
            5 => {
                v___x_2689_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_a_2684_);
                v___x_2690_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_b_2685_);
                if v_isShared_2688_ == 0 {
                    lean_ctor_set(v___x_2687_, 1, v___x_2690_);
                    lean_ctor_set(v___x_2687_, 0, v___x_2689_);
                    v___x_2692_ = v___x_2687_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2689_);
                    lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
                    v___x_2692_ = v_reuseFailAlloc_2693_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2692_;
            }
            7 => {
                v___x_2699_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_a_2695_);
                if v_isShared_2698_ == 0 {
                    lean_ctor_set(v___x_2697_, 0, v___x_2699_);
                    v___x_2701_ = v___x_2697_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2701_;
            }
            9 => {
                v___x_2709_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_a_2705_);
                if v_isShared_2708_ == 0 {
                    lean_ctor_set(v___x_2707_, 1, v___x_2709_);
                    v___x_2711_ = v___x_2707_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_k_2704_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2709_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2711_;
            }
            11 => {
                v___x_2719_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_2660_, v_a_2714_);
                if v_isShared_2718_ == 0 {
                    lean_ctor_set(v___x_2717_, 0, v___x_2719_);
                    v___x_2721_ = v___x_2717_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
                    lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_k_2715_);
                    v___x_2721_ = v_reuseFailAlloc_2722_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go___boxed(
    mut v_perm_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2726_: *mut LeanObject = core::ptr::null_mut();
    v_res_2726_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(
        v_perm_2724_,
        v_a_2725_,
    );
    lean_dec_ref(v_perm_2724_);
    return v_res_2726_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(
    mut v_00_u03b2_2727_: *mut LeanObject,
    mut v_m_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_2728_, v_a_2729_);
    return v___x_2730_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___boxed(
    mut v_00_u03b2_2731_: *mut LeanObject,
    mut v_m_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2734_: *mut LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_2731_, v_m_2732_, v_a_2733_);
    lean_dec(v_a_2733_);
    lean_dec_ref(v_m_2732_);
    return v_res_2734_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(
    mut v_00_u03b2_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
    mut v_x_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    v___x_2738_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_2736_, v_x_2737_);
    return v___x_2738_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2739_: *mut LeanObject,
    mut v_a_2740_: *mut LeanObject,
    mut v_x_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2742_: *mut LeanObject = core::ptr::null_mut();
    v_res_2742_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_2739_, v_a_2740_, v_x_2741_);
    lean_dec(v_x_2741_);
    lean_dec(v_a_2740_);
    return v_res_2742_;
}
pub unsafe fn l_Int_Linear_Expr_applyPerm(
    mut v_perm_2743_: *mut LeanObject,
    mut v_e_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(
        v_perm_2743_,
        v_e_2744_,
    );
    return v___x_2745_;
}
pub unsafe fn l_Int_Linear_Expr_applyPerm___boxed(
    mut v_perm_2746_: *mut LeanObject,
    mut v_e_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2748_: *mut LeanObject = core::ptr::null_mut();
    v_res_2748_ = l_Int_Linear_Expr_applyPerm(v_perm_2746_, v_e_2747_);
    lean_dec_ref(v_perm_2746_);
    return v_res_2748_;
}
pub unsafe fn _init_l_Int_Linear_instReprPoly__lean_repr___closed__3() -> *mut LeanObject {
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    v___x_2755_ = lean_unsigned_to_nat(2);
    v___x_2756_ = lean_nat_to_int(v___x_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Int_Linear_instReprPoly__lean_repr(
    mut v_x_2763_: *mut LeanObject,
    mut v_prec_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_k_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2763_) == 0 {
                    v_k_2774_ = lean_ctor_get(v_x_2763_, 0);
                    v_isSharedCheck_2797_ = (!lean_is_exclusive(v_x_2763_)) as u8;
                    if v_isSharedCheck_2797_ == 0 {
                        v___x_2776_ = v_x_2763_;
                        v_isShared_2777_ = v_isSharedCheck_2797_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_2774_);
                        lean_dec(v_x_2763_);
                        v___x_2776_ = lean_box(0);
                        v_isShared_2777_ = v_isSharedCheck_2797_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_2798_ = lean_ctor_get(v_x_2763_, 0);
                    lean_inc(v_k_2798_);
                    v_v_2799_ = lean_ctor_get(v_x_2763_, 1);
                    lean_inc(v_v_2799_);
                    v_p_2800_ = lean_ctor_get(v_x_2763_, 2);
                    lean_inc_ref(v_p_2800_);
                    lean_dec_ref_known(v_x_2763_, 3);
                    v___x_2801_ = lean_unsigned_to_nat(1024);
                    v___x_2830_ = lean_nat_dec_le(v___x_2801_, v_prec_2764_);
                    if v___x_2830_ == 0 {
                        v___x_2831_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_instReprPoly__lean_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                            ),
                            _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                        );
                        v___y_2820_ = v___x_2831_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2832_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                        v___y_2820_ = v___x_2832_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_2766_);
                v___x_2769_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2769_, 0, v___y_2766_);
                lean_ctor_set(v___x_2769_, 1, v___y_2768_);
                lean_inc(v___y_2767_);
                v___x_2770_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2770_, 0, v___y_2767_);
                lean_ctor_set(v___x_2770_, 1, v___x_2769_);
                v___x_2771_ = 0;
                v___x_2772_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2772_, 0, v___x_2770_);
                lean_ctor_set_uint8(
                    v___x_2772_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2771_,
                );
                v___x_2773_ = l_Repr_addAppParen(v___x_2772_, v_prec_2764_);
                return v___x_2773_;
            }
            2 => {
                v___x_2793_ = lean_unsigned_to_nat(1024);
                v___x_2794_ = lean_nat_dec_le(v___x_2793_, v_prec_2764_);
                if v___x_2794_ == 0 {
                    v___x_2795_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_2779_ = v___x_2795_;
                    state = 3;
                    continue;
                } else {
                    v___x_2796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_2779_ = v___x_2796_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2780_ = l_Int_Linear_instReprPoly__lean_repr___closed__2;
                v___x_2781_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_2782_ = lean_int_dec_lt(v_k_2774_, v___x_2781_);
                if v___x_2782_ == 0 {
                    v___x_2783_ = l_Int_repr(v_k_2774_);
                    lean_dec(v_k_2774_);
                    if v_isShared_2777_ == 0 {
                        lean_ctor_set_tag(v___x_2776_, 3);
                        lean_ctor_set(v___x_2776_, 0, v___x_2783_);
                        v___x_2785_ = v___x_2776_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2786_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
                        v___x_2785_ = v_reuseFailAlloc_2786_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2787_ = lean_unsigned_to_nat(1024);
                    v___x_2788_ = l_Int_repr(v_k_2774_);
                    lean_dec(v_k_2774_);
                    if v_isShared_2777_ == 0 {
                        lean_ctor_set_tag(v___x_2776_, 3);
                        lean_ctor_set(v___x_2776_, 0, v___x_2788_);
                        v___x_2790_ = v___x_2776_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2792_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2788_);
                        v___x_2790_ = v_reuseFailAlloc_2792_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_2766_ = v___x_2780_;
                v___y_2767_ = v___y_2779_;
                v___y_2768_ = v___x_2785_;
                state = 1;
                continue;
            }
            5 => {
                v___x_2791_ = l_Repr_addAppParen(v___x_2790_, v___x_2787_);
                v___y_2766_ = v___x_2780_;
                v___y_2767_ = v___y_2779_;
                v___y_2768_ = v___x_2791_;
                state = 1;
                continue;
            }
            6 => {
                lean_inc(v___y_2804_);
                v___x_2807_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2807_, 0, v___y_2804_);
                lean_ctor_set(v___x_2807_, 1, v___y_2806_);
                lean_inc_n(v___y_2805_, 2);
                v___x_2808_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2808_, 0, v___x_2807_);
                lean_ctor_set(v___x_2808_, 1, v___y_2805_);
                v___x_2809_ = l_Nat_reprFast(v_v_2799_);
                v___x_2810_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2810_, 0, v___x_2809_);
                v___x_2811_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2811_, 0, v___x_2808_);
                lean_ctor_set(v___x_2811_, 1, v___x_2810_);
                v___x_2812_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2812_, 0, v___x_2811_);
                lean_ctor_set(v___x_2812_, 1, v___y_2805_);
                v___x_2813_ = l_Int_Linear_instReprPoly__lean_repr(v_p_2800_, v___x_2801_);
                v___x_2814_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2814_, 0, v___x_2812_);
                lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                lean_inc(v___y_2803_);
                v___x_2815_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2815_, 0, v___y_2803_);
                lean_ctor_set(v___x_2815_, 1, v___x_2814_);
                v___x_2816_ = 0;
                v___x_2817_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2817_, 0, v___x_2815_);
                lean_ctor_set_uint8(
                    v___x_2817_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2816_,
                );
                v___x_2818_ = l_Repr_addAppParen(v___x_2817_, v_prec_2764_);
                return v___x_2818_;
            }
            7 => {
                v___x_2821_ = lean_box(1);
                v___x_2822_ = l_Int_Linear_instReprPoly__lean_repr___closed__6;
                v___x_2823_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_2824_ = lean_int_dec_lt(v_k_2798_, v___x_2823_);
                if v___x_2824_ == 0 {
                    v___x_2825_ = l_Int_repr(v_k_2798_);
                    lean_dec(v_k_2798_);
                    v___x_2826_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2826_, 0, v___x_2825_);
                    v___y_2803_ = v___y_2820_;
                    v___y_2804_ = v___x_2822_;
                    v___y_2805_ = v___x_2821_;
                    v___y_2806_ = v___x_2826_;
                    state = 6;
                    continue;
                } else {
                    v___x_2827_ = l_Int_repr(v_k_2798_);
                    lean_dec(v_k_2798_);
                    v___x_2828_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2828_, 0, v___x_2827_);
                    v___x_2829_ = l_Repr_addAppParen(v___x_2828_, v___x_2801_);
                    v___y_2803_ = v___y_2820_;
                    v___y_2804_ = v___x_2822_;
                    v___y_2805_ = v___x_2821_;
                    v___y_2806_ = v___x_2829_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_instReprPoly__lean_repr___boxed(
    mut v_x_2833_: *mut LeanObject,
    mut v_prec_2834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2835_: *mut LeanObject = core::ptr::null_mut();
    v_res_2835_ = l_Int_Linear_instReprPoly__lean_repr(v_x_2833_, v_prec_2834_);
    lean_dec(v_prec_2834_);
    return v_res_2835_;
}
pub unsafe fn l_Int_Linear_instReprExpr__lean_repr(
    mut v_x_2880_: *mut LeanObject,
    mut v_prec_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v___y_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: u8 = 0;
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2923_: u8 = 0;
    let mut v_i_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___y_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_a_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_a_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_a_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: u8 = 0;
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2880_) {
                0 => {
                    v_v_2900_ = lean_ctor_get(v_x_2880_, 0);
                    v_isSharedCheck_2923_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_2923_ == 0 {
                        v___x_2902_ = v_x_2880_;
                        v_isShared_2903_ = v_isSharedCheck_2923_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_v_2900_);
                        lean_dec(v_x_2880_);
                        v___x_2902_ = lean_box(0);
                        v_isShared_2903_ = v_isSharedCheck_2923_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_i_2924_ = lean_ctor_get(v_x_2880_, 0);
                    v_isSharedCheck_2944_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2926_ = v_x_2880_;
                        v_isShared_2927_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_i_2924_);
                        lean_dec(v_x_2880_);
                        v___x_2926_ = lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_a_2945_ = lean_ctor_get(v_x_2880_, 0);
                    v_b_2946_ = lean_ctor_get(v_x_2880_, 1);
                    v_isSharedCheck_2969_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v___x_2948_ = v_x_2880_;
                        v_isShared_2949_ = v_isSharedCheck_2969_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_b_2946_);
                        lean_inc(v_a_2945_);
                        lean_dec(v_x_2880_);
                        v___x_2948_ = lean_box(0);
                        v_isShared_2949_ = v_isSharedCheck_2969_;
                        state = 10;
                        continue;
                    }
                }
                3 => {
                    v_a_2970_ = lean_ctor_get(v_x_2880_, 0);
                    v_b_2971_ = lean_ctor_get(v_x_2880_, 1);
                    v_isSharedCheck_2994_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v___x_2973_ = v_x_2880_;
                        v_isShared_2974_ = v_isSharedCheck_2994_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_b_2971_);
                        lean_inc(v_a_2970_);
                        lean_dec(v_x_2880_);
                        v___x_2973_ = lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2994_;
                        state = 13;
                        continue;
                    }
                }
                4 => {
                    v_a_2995_ = lean_ctor_get(v_x_2880_, 0);
                    lean_inc_ref(v_a_2995_);
                    lean_dec_ref_known(v_x_2880_, 1);
                    v___x_2996_ = lean_unsigned_to_nat(1024);
                    v___x_3006_ = lean_nat_dec_le(v___x_2996_, v_prec_2881_);
                    if v___x_3006_ == 0 {
                        v___x_3007_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_instReprPoly__lean_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                            ),
                            _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                        );
                        v___y_2998_ = v___x_3007_;
                        state = 16;
                        continue;
                    } else {
                        v___x_3008_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                        v___y_2998_ = v___x_3008_;
                        state = 16;
                        continue;
                    }
                }
                5 => {
                    v_k_3009_ = lean_ctor_get(v_x_2880_, 0);
                    v_a_3010_ = lean_ctor_get(v_x_2880_, 1);
                    v_isSharedCheck_3044_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_3044_ == 0 {
                        v___x_3012_ = v_x_2880_;
                        v_isShared_3013_ = v_isSharedCheck_3044_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3010_);
                        lean_inc(v_k_3009_);
                        lean_dec(v_x_2880_);
                        v___x_3012_ = lean_box(0);
                        v_isShared_3013_ = v_isSharedCheck_3044_;
                        state = 17;
                        continue;
                    }
                }
                _ => {
                    v_a_3045_ = lean_ctor_get(v_x_2880_, 0);
                    v_k_3046_ = lean_ctor_get(v_x_2880_, 1);
                    v_isSharedCheck_3070_ = (!lean_is_exclusive(v_x_2880_)) as u8;
                    if v_isSharedCheck_3070_ == 0 {
                        v___x_3048_ = v_x_2880_;
                        v_isShared_3049_ = v_isSharedCheck_3070_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_k_3046_);
                        lean_inc(v_a_3045_);
                        lean_dec(v_x_2880_);
                        v___x_3048_ = lean_box(0);
                        v_isShared_3049_ = v_isSharedCheck_3070_;
                        state = 21;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2886_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2886_, 0, v___y_2883_);
                lean_ctor_set(v___x_2886_, 1, v___y_2885_);
                lean_inc(v___y_2884_);
                v___x_2887_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2887_, 0, v___y_2884_);
                lean_ctor_set(v___x_2887_, 1, v___x_2886_);
                v___x_2888_ = 0;
                v___x_2889_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2889_, 0, v___x_2887_);
                lean_ctor_set_uint8(
                    v___x_2889_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2888_,
                );
                v___x_2890_ = l_Repr_addAppParen(v___x_2889_, v_prec_2881_);
                return v___x_2890_;
            }
            2 => {
                lean_inc(v___y_2892_);
                v___x_2895_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2895_, 0, v___y_2892_);
                lean_ctor_set(v___x_2895_, 1, v___y_2894_);
                lean_inc(v___y_2893_);
                v___x_2896_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2896_, 0, v___y_2893_);
                lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                v___x_2897_ = 0;
                v___x_2898_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2898_, 0, v___x_2896_);
                lean_ctor_set_uint8(
                    v___x_2898_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2897_,
                );
                v___x_2899_ = l_Repr_addAppParen(v___x_2898_, v_prec_2881_);
                return v___x_2899_;
            }
            3 => {
                v___x_2919_ = lean_unsigned_to_nat(1024);
                v___x_2920_ = lean_nat_dec_le(v___x_2919_, v_prec_2881_);
                if v___x_2920_ == 0 {
                    v___x_2921_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_2905_ = v___x_2921_;
                    state = 4;
                    continue;
                } else {
                    v___x_2922_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_2905_ = v___x_2922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2906_ = l_Int_Linear_instReprExpr__lean_repr___closed__2;
                v___x_2907_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_2908_ = lean_int_dec_lt(v_v_2900_, v___x_2907_);
                if v___x_2908_ == 0 {
                    v___x_2909_ = l_Int_repr(v_v_2900_);
                    lean_dec(v_v_2900_);
                    if v_isShared_2903_ == 0 {
                        lean_ctor_set_tag(v___x_2902_, 3);
                        lean_ctor_set(v___x_2902_, 0, v___x_2909_);
                        v___x_2911_ = v___x_2902_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2912_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
                        v___x_2911_ = v_reuseFailAlloc_2912_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2913_ = lean_unsigned_to_nat(1024);
                    v___x_2914_ = l_Int_repr(v_v_2900_);
                    lean_dec(v_v_2900_);
                    if v_isShared_2903_ == 0 {
                        lean_ctor_set_tag(v___x_2902_, 3);
                        lean_ctor_set(v___x_2902_, 0, v___x_2914_);
                        v___x_2916_ = v___x_2902_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2918_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2914_);
                        v___x_2916_ = v_reuseFailAlloc_2918_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2892_ = v___x_2906_;
                v___y_2893_ = v___y_2905_;
                v___y_2894_ = v___x_2911_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2917_ = l_Repr_addAppParen(v___x_2916_, v___x_2913_);
                v___y_2892_ = v___x_2906_;
                v___y_2893_ = v___y_2905_;
                v___y_2894_ = v___x_2917_;
                state = 2;
                continue;
            }
            7 => {
                v___x_2940_ = lean_unsigned_to_nat(1024);
                v___x_2941_ = lean_nat_dec_le(v___x_2940_, v_prec_2881_);
                if v___x_2941_ == 0 {
                    v___x_2942_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_2929_ = v___x_2942_;
                    state = 8;
                    continue;
                } else {
                    v___x_2943_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_2929_ = v___x_2943_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2930_ = l_Int_Linear_instReprExpr__lean_repr___closed__5;
                v___x_2931_ = l_Nat_reprFast(v_i_2924_);
                if v_isShared_2927_ == 0 {
                    lean_ctor_set_tag(v___x_2926_, 3);
                    lean_ctor_set(v___x_2926_, 0, v___x_2931_);
                    v___x_2933_ = v___x_2926_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2939_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2931_);
                    v___x_2933_ = v_reuseFailAlloc_2939_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2934_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2934_, 0, v___x_2930_);
                lean_ctor_set(v___x_2934_, 1, v___x_2933_);
                lean_inc(v___y_2929_);
                v___x_2935_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2935_, 0, v___y_2929_);
                lean_ctor_set(v___x_2935_, 1, v___x_2934_);
                v___x_2936_ = 0;
                v___x_2937_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2937_, 0, v___x_2935_);
                lean_ctor_set_uint8(
                    v___x_2937_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2936_,
                );
                v___x_2938_ = l_Repr_addAppParen(v___x_2937_, v_prec_2881_);
                return v___x_2938_;
            }
            10 => {
                v___x_2950_ = lean_unsigned_to_nat(1024);
                v___x_2966_ = lean_nat_dec_le(v___x_2950_, v_prec_2881_);
                if v___x_2966_ == 0 {
                    v___x_2967_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_2952_ = v___x_2967_;
                    state = 11;
                    continue;
                } else {
                    v___x_2968_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_2952_ = v___x_2968_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2953_ = lean_box(1);
                v___x_2954_ = l_Int_Linear_instReprExpr__lean_repr___closed__8;
                v___x_2955_ = l_Int_Linear_instReprExpr__lean_repr(v_a_2945_, v___x_2950_);
                if v_isShared_2949_ == 0 {
                    lean_ctor_set_tag(v___x_2948_, 5);
                    lean_ctor_set(v___x_2948_, 1, v___x_2955_);
                    lean_ctor_set(v___x_2948_, 0, v___x_2954_);
                    v___x_2957_ = v___x_2948_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2965_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2954_);
                    lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2955_);
                    v___x_2957_ = v_reuseFailAlloc_2965_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2958_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2958_, 0, v___x_2957_);
                lean_ctor_set(v___x_2958_, 1, v___x_2953_);
                v___x_2959_ = l_Int_Linear_instReprExpr__lean_repr(v_b_2946_, v___x_2950_);
                v___x_2960_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2960_, 0, v___x_2958_);
                lean_ctor_set(v___x_2960_, 1, v___x_2959_);
                lean_inc(v___y_2952_);
                v___x_2961_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2961_, 0, v___y_2952_);
                lean_ctor_set(v___x_2961_, 1, v___x_2960_);
                v___x_2962_ = 0;
                v___x_2963_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2963_, 0, v___x_2961_);
                lean_ctor_set_uint8(
                    v___x_2963_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2962_,
                );
                v___x_2964_ = l_Repr_addAppParen(v___x_2963_, v_prec_2881_);
                return v___x_2964_;
            }
            13 => {
                v___x_2975_ = lean_unsigned_to_nat(1024);
                v___x_2991_ = lean_nat_dec_le(v___x_2975_, v_prec_2881_);
                if v___x_2991_ == 0 {
                    v___x_2992_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_2977_ = v___x_2992_;
                    state = 14;
                    continue;
                } else {
                    v___x_2993_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_2977_ = v___x_2993_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2978_ = lean_box(1);
                v___x_2979_ = l_Int_Linear_instReprExpr__lean_repr___closed__11;
                v___x_2980_ = l_Int_Linear_instReprExpr__lean_repr(v_a_2970_, v___x_2975_);
                if v_isShared_2974_ == 0 {
                    lean_ctor_set_tag(v___x_2973_, 5);
                    lean_ctor_set(v___x_2973_, 1, v___x_2980_);
                    lean_ctor_set(v___x_2973_, 0, v___x_2979_);
                    v___x_2982_ = v___x_2973_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2979_);
                    lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2980_);
                    v___x_2982_ = v_reuseFailAlloc_2990_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2983_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2983_, 0, v___x_2982_);
                lean_ctor_set(v___x_2983_, 1, v___x_2978_);
                v___x_2984_ = l_Int_Linear_instReprExpr__lean_repr(v_b_2971_, v___x_2975_);
                v___x_2985_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2985_, 0, v___x_2983_);
                lean_ctor_set(v___x_2985_, 1, v___x_2984_);
                lean_inc(v___y_2977_);
                v___x_2986_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2986_, 0, v___y_2977_);
                lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                v___x_2987_ = 0;
                v___x_2988_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2988_, 0, v___x_2986_);
                lean_ctor_set_uint8(
                    v___x_2988_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2987_,
                );
                v___x_2989_ = l_Repr_addAppParen(v___x_2988_, v_prec_2881_);
                return v___x_2989_;
            }
            16 => {
                v___x_2999_ = l_Int_Linear_instReprExpr__lean_repr___closed__14;
                v___x_3000_ = l_Int_Linear_instReprExpr__lean_repr(v_a_2995_, v___x_2996_);
                v___x_3001_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3001_, 0, v___x_2999_);
                lean_ctor_set(v___x_3001_, 1, v___x_3000_);
                lean_inc(v___y_2998_);
                v___x_3002_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3002_, 0, v___y_2998_);
                lean_ctor_set(v___x_3002_, 1, v___x_3001_);
                v___x_3003_ = 0;
                v___x_3004_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3004_, 0, v___x_3002_);
                lean_ctor_set_uint8(
                    v___x_3004_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3003_,
                );
                v___x_3005_ = l_Repr_addAppParen(v___x_3004_, v_prec_2881_);
                return v___x_3005_;
            }
            17 => {
                v___x_3014_ = lean_unsigned_to_nat(1024);
                v___x_3041_ = lean_nat_dec_le(v___x_3014_, v_prec_2881_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_3031_ = v___x_3042_;
                    state = 20;
                    continue;
                } else {
                    v___x_3043_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_3031_ = v___x_3043_;
                    state = 20;
                    continue;
                }
            }
            18 => {
                lean_inc(v___y_3018_);
                if v_isShared_3013_ == 0 {
                    lean_ctor_set(v___x_3012_, 1, v___y_3019_);
                    lean_ctor_set(v___x_3012_, 0, v___y_3018_);
                    v___x_3021_ = v___x_3012_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___y_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___y_3019_);
                    v___x_3021_ = v_reuseFailAlloc_3029_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                lean_inc(v___y_3016_);
                v___x_3022_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3022_, 0, v___x_3021_);
                lean_ctor_set(v___x_3022_, 1, v___y_3016_);
                v___x_3023_ = l_Int_Linear_instReprExpr__lean_repr(v_a_3010_, v___x_3014_);
                v___x_3024_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3024_, 0, v___x_3022_);
                lean_ctor_set(v___x_3024_, 1, v___x_3023_);
                lean_inc(v___y_3017_);
                v___x_3025_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3025_, 0, v___y_3017_);
                lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                v___x_3026_ = 0;
                v___x_3027_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3027_, 0, v___x_3025_);
                lean_ctor_set_uint8(
                    v___x_3027_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3026_,
                );
                v___x_3028_ = l_Repr_addAppParen(v___x_3027_, v_prec_2881_);
                return v___x_3028_;
            }
            20 => {
                v___x_3032_ = lean_box(1);
                v___x_3033_ = l_Int_Linear_instReprExpr__lean_repr___closed__17;
                v___x_3034_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3035_ = lean_int_dec_lt(v_k_3009_, v___x_3034_);
                if v___x_3035_ == 0 {
                    v___x_3036_ = l_Int_repr(v_k_3009_);
                    lean_dec(v_k_3009_);
                    v___x_3037_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3037_, 0, v___x_3036_);
                    v___y_3016_ = v___x_3032_;
                    v___y_3017_ = v___y_3031_;
                    v___y_3018_ = v___x_3033_;
                    v___y_3019_ = v___x_3037_;
                    state = 18;
                    continue;
                } else {
                    v___x_3038_ = l_Int_repr(v_k_3009_);
                    lean_dec(v_k_3009_);
                    v___x_3039_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3039_, 0, v___x_3038_);
                    v___x_3040_ = l_Repr_addAppParen(v___x_3039_, v___x_3014_);
                    v___y_3016_ = v___x_3032_;
                    v___y_3017_ = v___y_3031_;
                    v___y_3018_ = v___x_3033_;
                    v___y_3019_ = v___x_3040_;
                    state = 18;
                    continue;
                }
            }
            21 => {
                v___x_3050_ = lean_unsigned_to_nat(1024);
                v___x_3067_ = lean_nat_dec_le(v___x_3050_, v_prec_2881_);
                if v___x_3067_ == 0 {
                    v___x_3068_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instReprPoly__lean_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instReprPoly__lean_repr___closed__3_once
                        ),
                        _init_l_Int_Linear_instReprPoly__lean_repr___closed__3,
                    );
                    v___y_3052_ = v___x_3068_;
                    state = 22;
                    continue;
                } else {
                    v___x_3069_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___y_3052_ = v___x_3069_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_3053_ = lean_box(1);
                v___x_3054_ = l_Int_Linear_instReprExpr__lean_repr___closed__20;
                v___x_3055_ = l_Int_Linear_instReprExpr__lean_repr(v_a_3045_, v___x_3050_);
                if v_isShared_3049_ == 0 {
                    lean_ctor_set_tag(v___x_3048_, 5);
                    lean_ctor_set(v___x_3048_, 1, v___x_3055_);
                    lean_ctor_set(v___x_3048_, 0, v___x_3054_);
                    v___x_3057_ = v___x_3048_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3054_);
                    lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3055_);
                    v___x_3057_ = v_reuseFailAlloc_3066_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_3058_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3058_, 0, v___x_3057_);
                lean_ctor_set(v___x_3058_, 1, v___x_3053_);
                v___x_3059_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3060_ = lean_int_dec_lt(v_k_3046_, v___x_3059_);
                if v___x_3060_ == 0 {
                    v___x_3061_ = l_Int_repr(v_k_3046_);
                    lean_dec(v_k_3046_);
                    v___x_3062_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3062_, 0, v___x_3061_);
                    v___y_2883_ = v___x_3058_;
                    v___y_2884_ = v___y_3052_;
                    v___y_2885_ = v___x_3062_;
                    state = 1;
                    continue;
                } else {
                    v___x_3063_ = l_Int_repr(v_k_3046_);
                    lean_dec(v_k_3046_);
                    v___x_3064_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3064_, 0, v___x_3063_);
                    v___x_3065_ = l_Repr_addAppParen(v___x_3064_, v___x_3050_);
                    v___y_2883_ = v___x_3058_;
                    v___y_2884_ = v___y_3052_;
                    v___y_2885_ = v___x_3065_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_instReprExpr__lean_repr___boxed(
    mut v_x_3071_: *mut LeanObject,
    mut v_prec_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3073_: *mut LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Int_Linear_instReprExpr__lean_repr(v_x_3071_, v_prec_3072_);
    lean_dec(v_prec_3072_);
    return v_res_3073_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5() -> *mut LeanObject {
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    v___x_3085_ = lean_box(0);
    v___x_3086_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4;
    v___x_3087_ = l_Lean_mkConst(v___x_3086_, v___x_3085_);
    return v___x_3087_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9() -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = lean_unsigned_to_nat(0);
    v___x_3094_ = l_Lean_Level_ofNat(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10() -> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    v___x_3095_ = lean_box(0);
    v___x_3096_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_once),
        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9,
    );
    v___x_3097_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3097_, 0, v___x_3096_);
    lean_ctor_set(v___x_3097_, 1, v___x_3095_);
    return v___x_3097_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11() -> *mut LeanObject {
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    v___x_3098_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once),
        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10,
    );
    v___x_3099_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
    v___x_3100_ = l_Lean_Expr_const___override(v___x_3099_, v___x_3098_);
    return v___x_3100_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13() -> *mut LeanObject {
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    v___x_3103_ = lean_box(0);
    v___x_3104_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
    v___x_3105_ = l_Lean_Expr_const___override(v___x_3104_, v___x_3103_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16() -> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v___x_3110_ = lean_box(0);
    v___x_3111_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15;
    v___x_3112_ = l_Lean_Expr_const___override(v___x_3111_, v___x_3110_);
    return v___x_3112_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19() -> *mut LeanObject {
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3119_ = lean_box(0);
    v___x_3120_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18;
    v___x_3121_ = l_Lean_mkConst(v___x_3120_, v___x_3119_);
    return v___x_3121_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ofPoly(mut v_p_3122_: *mut LeanObject) -> *mut LeanObject {
    let mut v_k_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3122_) == 0 {
                    v_k_3123_ = lean_ctor_get(v_p_3122_, 0);
                    lean_inc(v_k_3123_);
                    lean_dec_ref_known(v_p_3122_, 1);
                    v___x_3124_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_once),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5,
                    );
                    v___x_3125_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                    v___x_3126_ = lean_int_dec_le(v___x_3125_, v_k_3123_);
                    if v___x_3126_ == 0 {
                        v___x_3127_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3128_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3129_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3130_ = lean_int_neg(v_k_3123_);
                        lean_dec(v_k_3123_);
                        v___x_3131_ = l_Int_toNat(v___x_3130_);
                        lean_dec(v___x_3130_);
                        v___x_3132_ = l_Lean_instToExprInt_mkNat(v___x_3131_);
                        v___x_3133_ =
                            l_Lean_mkApp3(v___x_3127_, v___x_3128_, v___x_3129_, v___x_3132_);
                        v___x_3134_ = l_Lean_Expr_app___override(v___x_3124_, v___x_3133_);
                        return v___x_3134_;
                    } else {
                        v___x_3135_ = l_Int_toNat(v_k_3123_);
                        lean_dec(v_k_3123_);
                        v___x_3136_ = l_Lean_instToExprInt_mkNat(v___x_3135_);
                        v___x_3137_ = l_Lean_Expr_app___override(v___x_3124_, v___x_3136_);
                        return v___x_3137_;
                    }
                } else {
                    v_k_3138_ = lean_ctor_get(v_p_3122_, 0);
                    lean_inc(v_k_3138_);
                    v_v_3139_ = lean_ctor_get(v_p_3122_, 1);
                    lean_inc(v_v_3139_);
                    v_p_3140_ = lean_ctor_get(v_p_3122_, 2);
                    lean_inc_ref(v_p_3140_);
                    lean_dec_ref_known(v_p_3122_, 3);
                    v___x_3141_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19,
                    );
                    v___x_3147_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                    v___x_3148_ = lean_int_dec_le(v___x_3147_, v_k_3138_);
                    if v___x_3148_ == 0 {
                        v___x_3149_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3150_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3151_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3152_ = lean_int_neg(v_k_3138_);
                        lean_dec(v_k_3138_);
                        v___x_3153_ = l_Int_toNat(v___x_3152_);
                        lean_dec(v___x_3152_);
                        v___x_3154_ = l_Lean_instToExprInt_mkNat(v___x_3153_);
                        v___x_3155_ =
                            l_Lean_mkApp3(v___x_3149_, v___x_3150_, v___x_3151_, v___x_3154_);
                        v___y_3143_ = v___x_3155_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3156_ = l_Int_toNat(v_k_3138_);
                        lean_dec(v_k_3138_);
                        v___x_3157_ = l_Lean_instToExprInt_mkNat(v___x_3156_);
                        v___y_3143_ = v___x_3157_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3144_ = l_Lean_mkNatLit(v_v_3139_);
                v___x_3145_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v_p_3140_);
                v___x_3146_ = l_Lean_mkApp3(v___x_3141_, v___y_3143_, v___x_3144_, v___x_3145_);
                return v___x_3146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2() -> *mut LeanObject {
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    v___x_3163_ = lean_box(0);
    v___x_3164_ = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1;
    v___x_3165_ = l_Lean_mkConst(v___x_3164_, v___x_3163_);
    return v___x_3165_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3() -> *mut LeanObject {
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3166_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2,
    );
    v___f_3167_ = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0;
    v___x_3168_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3168_, 0, v___f_3167_);
    lean_ctor_set(v___x_3168_, 1, v___x_3166_);
    return v___x_3168_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly() -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    v___x_3169_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3,
    );
    return v___x_3169_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2() -> *mut LeanObject {
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    v___x_3176_ = lean_box(0);
    v___x_3177_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1;
    v___x_3178_ = l_Lean_mkConst(v___x_3177_, v___x_3176_);
    return v___x_3178_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5() -> *mut LeanObject {
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    v___x_3185_ = lean_box(0);
    v___x_3186_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4;
    v___x_3187_ = l_Lean_mkConst(v___x_3186_, v___x_3185_);
    return v___x_3187_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7() -> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = lean_box(0);
    v___x_3194_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6;
    v___x_3195_ = l_Lean_mkConst(v___x_3194_, v___x_3193_);
    return v___x_3195_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10() -> *mut LeanObject {
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    v___x_3202_ = lean_box(0);
    v___x_3203_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9;
    v___x_3204_ = l_Lean_mkConst(v___x_3203_, v___x_3202_);
    return v___x_3204_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12() -> *mut LeanObject {
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    v___x_3210_ = lean_box(0);
    v___x_3211_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11;
    v___x_3212_ = l_Lean_mkConst(v___x_3211_, v___x_3210_);
    return v___x_3212_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15() -> *mut LeanObject {
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    v___x_3219_ = lean_box(0);
    v___x_3220_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14;
    v___x_3221_ = l_Lean_mkConst(v___x_3220_, v___x_3219_);
    return v___x_3221_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18() -> *mut LeanObject {
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    v___x_3228_ = lean_box(0);
    v___x_3229_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17;
    v___x_3230_ = l_Lean_mkConst(v___x_3229_, v___x_3228_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(
    mut v_e_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_3231_) {
                0 => {
                    v_v_3232_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc(v_v_3232_);
                    lean_dec_ref_known(v_e_3231_, 1);
                    v___x_3233_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2,
                    );
                    v___x_3234_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                    v___x_3235_ = lean_int_dec_le(v___x_3234_, v_v_3232_);
                    if v___x_3235_ == 0 {
                        v___x_3236_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3237_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3238_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3239_ = lean_int_neg(v_v_3232_);
                        lean_dec(v_v_3232_);
                        v___x_3240_ = l_Int_toNat(v___x_3239_);
                        lean_dec(v___x_3239_);
                        v___x_3241_ = l_Lean_instToExprInt_mkNat(v___x_3240_);
                        v___x_3242_ =
                            l_Lean_mkApp3(v___x_3236_, v___x_3237_, v___x_3238_, v___x_3241_);
                        v___x_3243_ = l_Lean_Expr_app___override(v___x_3233_, v___x_3242_);
                        return v___x_3243_;
                    } else {
                        v___x_3244_ = l_Int_toNat(v_v_3232_);
                        lean_dec(v_v_3232_);
                        v___x_3245_ = l_Lean_instToExprInt_mkNat(v___x_3244_);
                        v___x_3246_ = l_Lean_Expr_app___override(v___x_3233_, v___x_3245_);
                        return v___x_3246_;
                    }
                }
                1 => {
                    v_i_3247_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc(v_i_3247_);
                    lean_dec_ref_known(v_e_3231_, 1);
                    v___x_3248_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5,
                    );
                    v___x_3249_ = l_Lean_mkNatLit(v_i_3247_);
                    v___x_3250_ = l_Lean_Expr_app___override(v___x_3248_, v___x_3249_);
                    return v___x_3250_;
                }
                2 => {
                    v_a_3251_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc_ref(v_a_3251_);
                    v_b_3252_ = lean_ctor_get(v_e_3231_, 1);
                    lean_inc_ref(v_b_3252_);
                    lean_dec_ref_known(v_e_3231_, 2);
                    v___x_3253_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7,
                    );
                    v___x_3254_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_3251_);
                    v___x_3255_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_3252_);
                    v___x_3256_ = l_Lean_mkAppB(v___x_3253_, v___x_3254_, v___x_3255_);
                    return v___x_3256_;
                }
                3 => {
                    v_a_3257_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc_ref(v_a_3257_);
                    v_b_3258_ = lean_ctor_get(v_e_3231_, 1);
                    lean_inc_ref(v_b_3258_);
                    lean_dec_ref_known(v_e_3231_, 2);
                    v___x_3259_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10,
                    );
                    v___x_3260_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_3257_);
                    v___x_3261_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_3258_);
                    v___x_3262_ = l_Lean_mkAppB(v___x_3259_, v___x_3260_, v___x_3261_);
                    return v___x_3262_;
                }
                4 => {
                    v_a_3263_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc_ref(v_a_3263_);
                    lean_dec_ref_known(v_e_3231_, 1);
                    v___x_3264_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12,
                    );
                    v___x_3265_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_3263_);
                    v___x_3266_ = l_Lean_Expr_app___override(v___x_3264_, v___x_3265_);
                    return v___x_3266_;
                }
                5 => {
                    v_k_3267_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc(v_k_3267_);
                    v_a_3268_ = lean_ctor_get(v_e_3231_, 1);
                    lean_inc_ref(v_a_3268_);
                    lean_dec_ref_known(v_e_3231_, 2);
                    v___x_3269_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15,
                    );
                    v___x_3274_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                    v___x_3275_ = lean_int_dec_le(v___x_3274_, v_k_3267_);
                    if v___x_3275_ == 0 {
                        v___x_3276_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3277_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3278_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3279_ = lean_int_neg(v_k_3267_);
                        lean_dec(v_k_3267_);
                        v___x_3280_ = l_Int_toNat(v___x_3279_);
                        lean_dec(v___x_3279_);
                        v___x_3281_ = l_Lean_instToExprInt_mkNat(v___x_3280_);
                        v___x_3282_ =
                            l_Lean_mkApp3(v___x_3276_, v___x_3277_, v___x_3278_, v___x_3281_);
                        v___y_3271_ = v___x_3282_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3283_ = l_Int_toNat(v_k_3267_);
                        lean_dec(v_k_3267_);
                        v___x_3284_ = l_Lean_instToExprInt_mkNat(v___x_3283_);
                        v___y_3271_ = v___x_3284_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_a_3285_ = lean_ctor_get(v_e_3231_, 0);
                    lean_inc_ref(v_a_3285_);
                    v_k_3286_ = lean_ctor_get(v_e_3231_, 1);
                    lean_inc(v_k_3286_);
                    lean_dec_ref_known(v_e_3231_, 2);
                    v___x_3287_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18,
                    );
                    v___x_3288_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_3285_);
                    v___x_3289_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                    v___x_3290_ = lean_int_dec_le(v___x_3289_, v_k_3286_);
                    if v___x_3290_ == 0 {
                        v___x_3291_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3292_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3293_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3294_ = lean_int_neg(v_k_3286_);
                        lean_dec(v_k_3286_);
                        v___x_3295_ = l_Int_toNat(v___x_3294_);
                        lean_dec(v___x_3294_);
                        v___x_3296_ = l_Lean_instToExprInt_mkNat(v___x_3295_);
                        v___x_3297_ =
                            l_Lean_mkApp3(v___x_3291_, v___x_3292_, v___x_3293_, v___x_3296_);
                        v___x_3298_ = l_Lean_mkAppB(v___x_3287_, v___x_3288_, v___x_3297_);
                        return v___x_3298_;
                    } else {
                        v___x_3299_ = l_Int_toNat(v_k_3286_);
                        lean_dec(v_k_3286_);
                        v___x_3300_ = l_Lean_instToExprInt_mkNat(v___x_3299_);
                        v___x_3301_ = l_Lean_mkAppB(v___x_3287_, v___x_3288_, v___x_3300_);
                        return v___x_3301_;
                    }
                }
            },
            1 => {
                v___x_3272_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_3268_);
                v___x_3273_ = l_Lean_mkAppB(v___x_3269_, v___y_3271_, v___x_3272_);
                return v___x_3273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2() -> *mut LeanObject {
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    v___x_3307_ = lean_box(0);
    v___x_3308_ = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1;
    v___x_3309_ = l_Lean_mkConst(v___x_3308_, v___x_3307_);
    return v___x_3309_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3() -> *mut LeanObject {
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3310_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2,
    );
    v___f_3311_ = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0;
    v___x_3312_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3312_, 0, v___f_3311_);
    lean_ctor_set(v___x_3312_, 1, v___x_3310_);
    return v___x_3312_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr() -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3,
    );
    return v___x_3313_;
}
pub unsafe fn l_Int_Linear_Expr_denoteExpr___redArg(
    mut v_ctx_3314_: *mut LeanObject,
    mut v_e_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3338_: u8 = 0;
    let mut v_i_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3342_: u8 = 0;
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3347_: u8 = 0;
    let mut v_a_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3361_: u8 = 0;
    let mut v_a_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_a_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_k_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___y_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3411_: u8 = 0;
    let mut v_a_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___y_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_3315_) {
                0 => {
                    lean_dec_ref(v_ctx_3314_);
                    v_v_3317_ = lean_ctor_get(v_e_3315_, 0);
                    v_isSharedCheck_3338_ = (!lean_is_exclusive(v_e_3315_)) as u8;
                    if v_isSharedCheck_3338_ == 0 {
                        v___x_3319_ = v_e_3315_;
                        v_isShared_3320_ = v_isSharedCheck_3338_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_3317_);
                        lean_dec(v_e_3315_);
                        v___x_3319_ = lean_box(0);
                        v_isShared_3320_ = v_isSharedCheck_3338_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_3339_ = lean_ctor_get(v_e_3315_, 0);
                    v_isSharedCheck_3347_ = (!lean_is_exclusive(v_e_3315_)) as u8;
                    if v_isSharedCheck_3347_ == 0 {
                        v___x_3341_ = v_e_3315_;
                        v_isShared_3342_ = v_isSharedCheck_3347_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_i_3339_);
                        lean_dec(v_e_3315_);
                        v___x_3341_ = lean_box(0);
                        v_isShared_3342_ = v_isSharedCheck_3347_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_a_3348_ = lean_ctor_get(v_e_3315_, 0);
                    lean_inc_ref(v_a_3348_);
                    v_b_3349_ = lean_ctor_get(v_e_3315_, 1);
                    lean_inc_ref(v_b_3349_);
                    lean_dec_ref_known(v_e_3315_, 2);
                    lean_inc_ref(v_ctx_3314_);
                    v___x_3350_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_a_3348_);
                    v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
                    lean_inc(v_a_3351_);
                    lean_dec_ref(v___x_3350_);
                    v___x_3352_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_b_3349_);
                    v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
                    v_isSharedCheck_3361_ = (!lean_is_exclusive(v___x_3352_)) as u8;
                    if v_isSharedCheck_3361_ == 0 {
                        v___x_3355_ = v___x_3352_;
                        v_isShared_3356_ = v_isSharedCheck_3361_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3353_);
                        lean_dec(v___x_3352_);
                        v___x_3355_ = lean_box(0);
                        v_isShared_3356_ = v_isSharedCheck_3361_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    v_a_3362_ = lean_ctor_get(v_e_3315_, 0);
                    lean_inc_ref(v_a_3362_);
                    v_b_3363_ = lean_ctor_get(v_e_3315_, 1);
                    lean_inc_ref(v_b_3363_);
                    lean_dec_ref_known(v_e_3315_, 2);
                    lean_inc_ref(v_ctx_3314_);
                    v___x_3364_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_a_3362_);
                    v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
                    lean_inc(v_a_3365_);
                    lean_dec_ref(v___x_3364_);
                    v___x_3366_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_b_3363_);
                    v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
                    v_isSharedCheck_3375_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                    if v_isSharedCheck_3375_ == 0 {
                        v___x_3369_ = v___x_3366_;
                        v_isShared_3370_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3367_);
                        lean_dec(v___x_3366_);
                        v___x_3369_ = lean_box(0);
                        v_isShared_3370_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    v_a_3376_ = lean_ctor_get(v_e_3315_, 0);
                    lean_inc_ref(v_a_3376_);
                    lean_dec_ref_known(v_e_3315_, 1);
                    v___x_3377_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_a_3376_);
                    v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
                    v_isSharedCheck_3386_ = (!lean_is_exclusive(v___x_3377_)) as u8;
                    if v_isSharedCheck_3386_ == 0 {
                        v___x_3380_ = v___x_3377_;
                        v_isShared_3381_ = v_isSharedCheck_3386_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3378_);
                        lean_dec(v___x_3377_);
                        v___x_3380_ = lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3386_;
                        state = 10;
                        continue;
                    }
                }
                5 => {
                    v_k_3387_ = lean_ctor_get(v_e_3315_, 0);
                    lean_inc(v_k_3387_);
                    v_a_3388_ = lean_ctor_get(v_e_3315_, 1);
                    lean_inc_ref(v_a_3388_);
                    lean_dec_ref_known(v_e_3315_, 2);
                    v___x_3389_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_a_3388_);
                    v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
                    v_isSharedCheck_3411_ = (!lean_is_exclusive(v___x_3389_)) as u8;
                    if v_isSharedCheck_3411_ == 0 {
                        v___x_3392_ = v___x_3389_;
                        v_isShared_3393_ = v_isSharedCheck_3411_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3390_);
                        lean_dec(v___x_3389_);
                        v___x_3392_ = lean_box(0);
                        v_isShared_3393_ = v_isSharedCheck_3411_;
                        state = 12;
                        continue;
                    }
                }
                _ => {
                    v_a_3412_ = lean_ctor_get(v_e_3315_, 0);
                    lean_inc_ref(v_a_3412_);
                    v_k_3413_ = lean_ctor_get(v_e_3315_, 1);
                    lean_inc(v_k_3413_);
                    lean_dec_ref_known(v_e_3315_, 2);
                    v___x_3414_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3314_, v_a_3412_);
                    v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
                    v_isSharedCheck_3436_ = (!lean_is_exclusive(v___x_3414_)) as u8;
                    if v_isSharedCheck_3436_ == 0 {
                        v___x_3417_ = v___x_3414_;
                        v_isShared_3418_ = v_isSharedCheck_3436_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3415_);
                        lean_dec(v___x_3414_);
                        v___x_3417_ = lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3436_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3322_ = lean_int_dec_le(v___x_3321_, v_v_3317_);
                if v___x_3322_ == 0 {
                    v___x_3323_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                    );
                    v___x_3324_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                    );
                    v___x_3325_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                    );
                    v___x_3326_ = lean_int_neg(v_v_3317_);
                    lean_dec(v_v_3317_);
                    v___x_3327_ = l_Int_toNat(v___x_3326_);
                    lean_dec(v___x_3326_);
                    v___x_3328_ = l_Lean_instToExprInt_mkNat(v___x_3327_);
                    v___x_3329_ = l_Lean_mkApp3(v___x_3323_, v___x_3324_, v___x_3325_, v___x_3328_);
                    if v_isShared_3320_ == 0 {
                        lean_ctor_set(v___x_3319_, 0, v___x_3329_);
                        v___x_3331_ = v___x_3319_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                        v___x_3331_ = v_reuseFailAlloc_3332_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3333_ = l_Int_toNat(v_v_3317_);
                    lean_dec(v_v_3317_);
                    v___x_3334_ = l_Lean_instToExprInt_mkNat(v___x_3333_);
                    if v_isShared_3320_ == 0 {
                        lean_ctor_set(v___x_3319_, 0, v___x_3334_);
                        v___x_3336_ = v___x_3319_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
                        v___x_3336_ = v_reuseFailAlloc_3337_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3331_;
            }
            3 => {
                return v___x_3336_;
            }
            4 => {
                v___x_3343_ = lean_apply_1(v_ctx_3314_, v_i_3339_);
                if v_isShared_3342_ == 0 {
                    lean_ctor_set_tag(v___x_3341_, 0);
                    lean_ctor_set(v___x_3341_, 0, v___x_3343_);
                    v___x_3345_ = v___x_3341_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
                    v___x_3345_ = v_reuseFailAlloc_3346_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3345_;
            }
            6 => {
                v___x_3357_ = l_Lean_mkIntAdd(v_a_3351_, v_a_3353_);
                if v_isShared_3356_ == 0 {
                    lean_ctor_set(v___x_3355_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
                    v___x_3359_ = v_reuseFailAlloc_3360_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3359_;
            }
            8 => {
                v___x_3371_ = l_Lean_mkIntSub(v_a_3365_, v_a_3367_);
                if v_isShared_3370_ == 0 {
                    lean_ctor_set(v___x_3369_, 0, v___x_3371_);
                    v___x_3373_ = v___x_3369_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
                    v___x_3373_ = v_reuseFailAlloc_3374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3373_;
            }
            10 => {
                v___x_3382_ = l_Lean_mkIntNeg(v_a_3378_);
                if v_isShared_3381_ == 0 {
                    lean_ctor_set(v___x_3380_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3380_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3384_;
            }
            12 => {
                v___x_3400_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3401_ = lean_int_dec_le(v___x_3400_, v_k_3387_);
                if v___x_3401_ == 0 {
                    v___x_3402_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                    );
                    v___x_3403_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                    );
                    v___x_3404_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                    );
                    v___x_3405_ = lean_int_neg(v_k_3387_);
                    lean_dec(v_k_3387_);
                    v___x_3406_ = l_Int_toNat(v___x_3405_);
                    lean_dec(v___x_3405_);
                    v___x_3407_ = l_Lean_instToExprInt_mkNat(v___x_3406_);
                    v___x_3408_ = l_Lean_mkApp3(v___x_3402_, v___x_3403_, v___x_3404_, v___x_3407_);
                    v___y_3395_ = v___x_3408_;
                    state = 13;
                    continue;
                } else {
                    v___x_3409_ = l_Int_toNat(v_k_3387_);
                    lean_dec(v_k_3387_);
                    v___x_3410_ = l_Lean_instToExprInt_mkNat(v___x_3409_);
                    v___y_3395_ = v___x_3410_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3396_ = l_Lean_mkIntMul(v___y_3395_, v_a_3390_);
                if v_isShared_3393_ == 0 {
                    lean_ctor_set(v___x_3392_, 0, v___x_3396_);
                    v___x_3398_ = v___x_3392_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
                    v___x_3398_ = v_reuseFailAlloc_3399_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3398_;
            }
            15 => {
                v___x_3425_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3426_ = lean_int_dec_le(v___x_3425_, v_k_3413_);
                if v___x_3426_ == 0 {
                    v___x_3427_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                    );
                    v___x_3428_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                    );
                    v___x_3429_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                    );
                    v___x_3430_ = lean_int_neg(v_k_3413_);
                    lean_dec(v_k_3413_);
                    v___x_3431_ = l_Int_toNat(v___x_3430_);
                    lean_dec(v___x_3430_);
                    v___x_3432_ = l_Lean_instToExprInt_mkNat(v___x_3431_);
                    v___x_3433_ = l_Lean_mkApp3(v___x_3427_, v___x_3428_, v___x_3429_, v___x_3432_);
                    v___y_3420_ = v___x_3433_;
                    state = 16;
                    continue;
                } else {
                    v___x_3434_ = l_Int_toNat(v_k_3413_);
                    lean_dec(v_k_3413_);
                    v___x_3435_ = l_Lean_instToExprInt_mkNat(v___x_3434_);
                    v___y_3420_ = v___x_3435_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3421_ = l_Lean_mkIntMul(v_a_3415_, v___y_3420_);
                if v_isShared_3418_ == 0 {
                    lean_ctor_set(v___x_3417_, 0, v___x_3421_);
                    v___x_3423_ = v___x_3417_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
                    v___x_3423_ = v_reuseFailAlloc_3424_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_denoteExpr___redArg___boxed(
    mut v_ctx_3437_: *mut LeanObject,
    mut v_e_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3440_: *mut LeanObject = core::ptr::null_mut();
    v_res_3440_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3437_, v_e_3438_);
    return v_res_3440_;
}
pub unsafe fn l_Int_Linear_Expr_denoteExpr(
    mut v_ctx_3441_: *mut LeanObject,
    mut v_e_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_3441_, v_e_3442_);
    return v___x_3448_;
}
pub unsafe fn l_Int_Linear_Expr_denoteExpr___boxed(
    mut v_ctx_3449_: *mut LeanObject,
    mut v_e_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
    mut v_a_3454_: *mut LeanObject,
    mut v_a_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3456_ = l_Int_Linear_Expr_denoteExpr(
        v_ctx_3449_,
        v_e_3450_,
        v_a_3451_,
        v_a_3452_,
        v_a_3453_,
        v_a_3454_,
    );
    lean_dec(v_a_3454_);
    lean_dec_ref(v_a_3453_);
    lean_dec(v_a_3452_);
    lean_dec_ref(v_a_3451_);
    return v_res_3456_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(
    mut v_ctx_3457_: *mut LeanObject,
    mut v_r_3458_: *mut LeanObject,
    mut v_p_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut v_k_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3459_) == 0 {
                    lean_dec_ref(v_ctx_3457_);
                    v_k_3465_ = lean_ctor_get(v_p_3459_, 0);
                    v_isSharedCheck_3484_ = (!lean_is_exclusive(v_p_3459_)) as u8;
                    if v_isSharedCheck_3484_ == 0 {
                        v___x_3467_ = v_p_3459_;
                        v_isShared_3468_ = v_isSharedCheck_3484_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_3465_);
                        lean_dec(v_p_3459_);
                        v___x_3467_ = lean_box(0);
                        v_isShared_3468_ = v_isSharedCheck_3484_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_3485_ = lean_ctor_get(v_p_3459_, 0);
                    lean_inc(v_k_3485_);
                    v_v_3486_ = lean_ctor_get(v_p_3459_, 1);
                    lean_inc(v_v_3486_);
                    v_p_3487_ = lean_ctor_get(v_p_3459_, 2);
                    lean_inc_ref(v_p_3487_);
                    lean_dec_ref_known(v_p_3459_, 3);
                    v___x_3494_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___x_3495_ = lean_int_dec_eq(v_k_3485_, v___x_3494_);
                    if v___x_3495_ == 0 {
                        v___x_3496_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                        v___x_3497_ = lean_int_dec_le(v___x_3496_, v_k_3485_);
                        if v___x_3497_ == 0 {
                            v___x_3498_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                            );
                            v___x_3499_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                            );
                            v___x_3500_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                            );
                            v___x_3501_ = lean_int_neg(v_k_3485_);
                            lean_dec(v_k_3485_);
                            v___x_3502_ = l_Int_toNat(v___x_3501_);
                            lean_dec(v___x_3501_);
                            v___x_3503_ = l_Lean_instToExprInt_mkNat(v___x_3502_);
                            v___x_3504_ =
                                l_Lean_mkApp3(v___x_3498_, v___x_3499_, v___x_3500_, v___x_3503_);
                            v___y_3489_ = v___x_3504_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3505_ = l_Int_toNat(v_k_3485_);
                            lean_dec(v_k_3485_);
                            v___x_3506_ = l_Lean_instToExprInt_mkNat(v___x_3505_);
                            v___y_3489_ = v___x_3506_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_3485_);
                        lean_inc_ref(v_ctx_3457_);
                        v___x_3507_ = lean_apply_1(v_ctx_3457_, v_v_3486_);
                        v___x_3508_ = l_Lean_mkIntAdd(v_r_3458_, v___x_3507_);
                        v_r_3458_ = v___x_3508_;
                        v_p_3459_ = v_p_3487_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3463_ = l_Lean_mkIntAdd(v_r_3458_, v___y_3462_);
                v___x_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3464_, 0, v___x_3463_);
                return v___x_3464_;
            }
            2 => {
                v___x_3469_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3470_ = lean_int_dec_eq(v_k_3465_, v___x_3469_);
                if v___x_3470_ == 0 {
                    lean_del_object(v___x_3467_);
                    v___x_3471_ = lean_int_dec_le(v___x_3469_, v_k_3465_);
                    if v___x_3471_ == 0 {
                        v___x_3472_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                        );
                        v___x_3473_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                        );
                        v___x_3474_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                        );
                        v___x_3475_ = lean_int_neg(v_k_3465_);
                        lean_dec(v_k_3465_);
                        v___x_3476_ = l_Int_toNat(v___x_3475_);
                        lean_dec(v___x_3475_);
                        v___x_3477_ = l_Lean_instToExprInt_mkNat(v___x_3476_);
                        v___x_3478_ =
                            l_Lean_mkApp3(v___x_3472_, v___x_3473_, v___x_3474_, v___x_3477_);
                        v___y_3462_ = v___x_3478_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3479_ = l_Int_toNat(v_k_3465_);
                        lean_dec(v_k_3465_);
                        v___x_3480_ = l_Lean_instToExprInt_mkNat(v___x_3479_);
                        v___y_3462_ = v___x_3480_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3465_);
                    if v_isShared_3468_ == 0 {
                        lean_ctor_set(v___x_3467_, 0, v_r_3458_);
                        v___x_3482_ = v___x_3467_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_r_3458_);
                        v___x_3482_ = v_reuseFailAlloc_3483_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3482_;
            }
            4 => {
                lean_inc_ref(v_ctx_3457_);
                v___x_3490_ = lean_apply_1(v_ctx_3457_, v_v_3486_);
                v___x_3491_ = l_Lean_mkIntMul(v___y_3489_, v___x_3490_);
                v___x_3492_ = l_Lean_mkIntAdd(v_r_3458_, v___x_3491_);
                v_r_3458_ = v___x_3492_;
                v_p_3459_ = v_p_3487_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg___boxed(
    mut v_ctx_3510_: *mut LeanObject,
    mut v_r_3511_: *mut LeanObject,
    mut v_p_3512_: *mut LeanObject,
    mut v_a_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3514_: *mut LeanObject = core::ptr::null_mut();
    v_res_3514_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(
            v_ctx_3510_,
            v_r_3511_,
            v_p_3512_,
        );
    return v_res_3514_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(
    mut v_ctx_3515_: *mut LeanObject,
    mut v_r_3516_: *mut LeanObject,
    mut v_p_3517_: *mut LeanObject,
    mut v_a_3518_: *mut LeanObject,
    mut v_a_3519_: *mut LeanObject,
    mut v_a_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    v___x_3523_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(
            v_ctx_3515_,
            v_r_3516_,
            v_p_3517_,
        );
    return v___x_3523_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___boxed(
    mut v_ctx_3524_: *mut LeanObject,
    mut v_r_3525_: *mut LeanObject,
    mut v_p_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
    mut v_a_3529_: *mut LeanObject,
    mut v_a_3530_: *mut LeanObject,
    mut v_a_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3532_: *mut LeanObject = core::ptr::null_mut();
    v_res_3532_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(
            v_ctx_3524_,
            v_r_3525_,
            v_p_3526_,
            v_a_3527_,
            v_a_3528_,
            v_a_3529_,
            v_a_3530_,
        );
    lean_dec(v_a_3530_);
    lean_dec_ref(v_a_3529_);
    lean_dec(v_a_3528_);
    lean_dec_ref(v_a_3527_);
    return v_res_3532_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr___redArg(
    mut v_ctx_3533_: *mut LeanObject,
    mut v_p_3534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut v_k_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3534_) == 0 {
                    lean_dec_ref(v_ctx_3533_);
                    v_k_3536_ = lean_ctor_get(v_p_3534_, 0);
                    v_isSharedCheck_3557_ = (!lean_is_exclusive(v_p_3534_)) as u8;
                    if v_isSharedCheck_3557_ == 0 {
                        v___x_3538_ = v_p_3534_;
                        v_isShared_3539_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_3536_);
                        lean_dec(v_p_3534_);
                        v___x_3538_ = lean_box(0);
                        v_isShared_3539_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3558_ = lean_ctor_get(v_p_3534_, 0);
                    lean_inc(v_k_3558_);
                    v_v_3559_ = lean_ctor_get(v_p_3534_, 1);
                    lean_inc(v_v_3559_);
                    v_p_3560_ = lean_ctor_get(v_p_3534_, 2);
                    lean_inc_ref(v_p_3560_);
                    lean_dec_ref_known(v_p_3534_, 3);
                    v___x_3566_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
                    v___x_3567_ = lean_int_dec_eq(v_k_3558_, v___x_3566_);
                    if v___x_3567_ == 0 {
                        v___x_3568_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                        v___x_3569_ = lean_int_dec_le(v___x_3568_, v_k_3558_);
                        if v___x_3569_ == 0 {
                            v___x_3570_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                            );
                            v___x_3571_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                            );
                            v___x_3572_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                            );
                            v___x_3573_ = lean_int_neg(v_k_3558_);
                            lean_dec(v_k_3558_);
                            v___x_3574_ = l_Int_toNat(v___x_3573_);
                            lean_dec(v___x_3573_);
                            v___x_3575_ = l_Lean_instToExprInt_mkNat(v___x_3574_);
                            v___x_3576_ =
                                l_Lean_mkApp3(v___x_3570_, v___x_3571_, v___x_3572_, v___x_3575_);
                            v___y_3562_ = v___x_3576_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3577_ = l_Int_toNat(v_k_3558_);
                            lean_dec(v_k_3558_);
                            v___x_3578_ = l_Lean_instToExprInt_mkNat(v___x_3577_);
                            v___y_3562_ = v___x_3578_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_3558_);
                        lean_inc_ref(v_ctx_3533_);
                        v___x_3579_ = lean_apply_1(v_ctx_3533_, v_v_3559_);
                        v___x_3580_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_3533_, v___x_3579_, v_p_3560_);
                        return v___x_3580_;
                    }
                }
            }
            1 => {
                v___x_3540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
                v___x_3541_ = lean_int_dec_le(v___x_3540_, v_k_3536_);
                if v___x_3541_ == 0 {
                    v___x_3542_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11,
                    );
                    v___x_3543_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13,
                    );
                    v___x_3544_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16,
                    );
                    v___x_3545_ = lean_int_neg(v_k_3536_);
                    lean_dec(v_k_3536_);
                    v___x_3546_ = l_Int_toNat(v___x_3545_);
                    lean_dec(v___x_3545_);
                    v___x_3547_ = l_Lean_instToExprInt_mkNat(v___x_3546_);
                    v___x_3548_ = l_Lean_mkApp3(v___x_3542_, v___x_3543_, v___x_3544_, v___x_3547_);
                    if v_isShared_3539_ == 0 {
                        lean_ctor_set(v___x_3538_, 0, v___x_3548_);
                        v___x_3550_ = v___x_3538_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
                        v___x_3550_ = v_reuseFailAlloc_3551_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3552_ = l_Int_toNat(v_k_3536_);
                    lean_dec(v_k_3536_);
                    v___x_3553_ = l_Lean_instToExprInt_mkNat(v___x_3552_);
                    if v_isShared_3539_ == 0 {
                        lean_ctor_set(v___x_3538_, 0, v___x_3553_);
                        v___x_3555_ = v___x_3538_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
                        v___x_3555_ = v_reuseFailAlloc_3556_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3550_;
            }
            3 => {
                return v___x_3555_;
            }
            4 => {
                lean_inc_ref(v_ctx_3533_);
                v___x_3563_ = lean_apply_1(v_ctx_3533_, v_v_3559_);
                v___x_3564_ = l_Lean_mkIntMul(v___y_3562_, v___x_3563_);
                v___x_3565_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_3533_, v___x_3564_, v_p_3560_);
                return v___x_3565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr___redArg___boxed(
    mut v_ctx_3581_: *mut LeanObject,
    mut v_p_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3584_: *mut LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Int_Linear_Poly_denoteExpr___redArg(v_ctx_3581_, v_p_3582_);
    return v_res_3584_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr(
    mut v_ctx_3585_: *mut LeanObject,
    mut v_p_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Int_Linear_Poly_denoteExpr___redArg(v_ctx_3585_, v_p_3586_);
    return v___x_3592_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr___boxed(
    mut v_ctx_3593_: *mut LeanObject,
    mut v_p_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3600_: *mut LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Int_Linear_Poly_denoteExpr(
        v_ctx_3593_,
        v_p_3594_,
        v_a_3595_,
        v_a_3596_,
        v_a_3597_,
        v_a_3598_,
    );
    lean_dec(v_a_3598_);
    lean_dec_ref(v_a_3597_);
    lean_dec(v_a_3596_);
    lean_dec_ref(v_a_3595_);
    return v_res_3600_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
    mut v_e_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_val_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_a_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_a_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3608_ = lean_st_ref_get(v_a_3602_);
                v_varMap_3609_ = lean_ctor_get(v___x_3608_, 0);
                lean_inc_ref(v_varMap_3609_);
                lean_dec(v___x_3608_);
                lean_inc_ref(v_e_3601_);
                v___x_3610_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
                    v_varMap_3609_,
                    v_e_3601_,
                    v_a_3603_,
                    v_a_3604_,
                    v_a_3605_,
                    v_a_3606_,
                );
                lean_dec_ref(v_varMap_3609_);
                if lean_obj_tag(v___x_3610_) == 0 {
                    v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3659_ = (!lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3659_ == 0 {
                        v___x_3613_ = v___x_3610_;
                        v_isShared_3614_ = v_isSharedCheck_3659_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3611_);
                        lean_dec(v___x_3610_);
                        v___x_3613_ = lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3659_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3601_);
                    v_a_3660_ = lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3667_ = (!lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3610_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3660_);
                        lean_dec(v___x_3610_);
                        v___x_3662_ = lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3611_) == 1 {
                    lean_dec_ref(v_e_3601_);
                    v_val_3615_ = lean_ctor_get(v_a_3611_, 0);
                    v_isSharedCheck_3625_ = (!lean_is_exclusive(v_a_3611_)) as u8;
                    if v_isSharedCheck_3625_ == 0 {
                        v___x_3617_ = v_a_3611_;
                        v_isShared_3618_ = v_isSharedCheck_3625_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3615_);
                        lean_dec(v_a_3611_);
                        v___x_3617_ = lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3625_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3613_);
                    lean_dec(v_a_3611_);
                    v___x_3626_ = lean_st_ref_get(v_a_3602_);
                    v___x_3627_ = lean_st_ref_get(v_a_3602_);
                    v_vars_3628_ = lean_ctor_get(v___x_3626_, 1);
                    lean_inc_ref(v_vars_3628_);
                    lean_dec(v___x_3626_);
                    v_varMap_3629_ = lean_ctor_get(v___x_3627_, 0);
                    v_vars_3630_ = lean_ctor_get(v___x_3627_, 1);
                    v_isSharedCheck_3658_ = (!lean_is_exclusive(v___x_3627_)) as u8;
                    if v_isSharedCheck_3658_ == 0 {
                        v___x_3632_ = v___x_3627_;
                        v_isShared_3633_ = v_isSharedCheck_3658_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_vars_3630_);
                        lean_inc(v_varMap_3629_);
                        lean_dec(v___x_3627_);
                        v___x_3632_ = lean_box(0);
                        v_isShared_3633_ = v_isSharedCheck_3658_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3618_ == 0 {
                    v___x_3620_ = v___x_3617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_val_3615_);
                    v___x_3620_ = v_reuseFailAlloc_3624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3614_ == 0 {
                    lean_ctor_set(v___x_3613_, 0, v___x_3620_);
                    v___x_3622_ = v___x_3613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3622_;
            }
            5 => {
                v___x_3634_ = lean_array_get_size(v_vars_3628_);
                lean_dec_ref(v_vars_3628_);
                lean_inc_ref(v_e_3601_);
                v___x_3635_ = l_Lean_Meta_KExprMap_insert___redArg(
                    v_varMap_3629_,
                    v_e_3601_,
                    v___x_3634_,
                    v_a_3603_,
                    v_a_3604_,
                    v_a_3605_,
                    v_a_3606_,
                );
                if lean_obj_tag(v___x_3635_) == 0 {
                    v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3649_ = (!lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v___x_3638_ = v___x_3635_;
                        v_isShared_3639_ = v_isSharedCheck_3649_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3636_);
                        lean_dec(v___x_3635_);
                        v___x_3638_ = lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3649_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3632_);
                    lean_dec_ref(v_vars_3630_);
                    lean_dec_ref(v_e_3601_);
                    v_a_3650_ = lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3657_ = (!lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3657_ == 0 {
                        v___x_3652_ = v___x_3635_;
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3650_);
                        lean_dec(v___x_3635_);
                        v___x_3652_ = lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3640_ = lean_array_push(v_vars_3630_, v_e_3601_);
                if v_isShared_3633_ == 0 {
                    lean_ctor_set(v___x_3632_, 1, v___x_3640_);
                    lean_ctor_set(v___x_3632_, 0, v_a_3636_);
                    v___x_3642_ = v___x_3632_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3636_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3640_);
                    v___x_3642_ = v_reuseFailAlloc_3648_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3643_ = lean_st_ref_set(v_a_3602_, v___x_3642_);
                v___x_3644_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3644_, 0, v___x_3634_);
                if v_isShared_3639_ == 0 {
                    lean_ctor_set(v___x_3638_, 0, v___x_3644_);
                    v___x_3646_ = v___x_3638_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3646_;
            }
            9 => {
                if v_isShared_3653_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3655_;
            }
            11 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(
    mut v_e_3668_: *mut LeanObject,
    mut v_a_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
    mut v_a_3671_: *mut LeanObject,
    mut v_a_3672_: *mut LeanObject,
    mut v_a_3673_: *mut LeanObject,
    mut v_a_3674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3675_: *mut LeanObject = core::ptr::null_mut();
    v_res_3675_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
        v_e_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_,
    );
    lean_dec(v_a_3673_);
    lean_dec_ref(v_a_3672_);
    lean_dec(v_a_3671_);
    lean_dec_ref(v_a_3670_);
    lean_dec(v_a_3669_);
    return v_res_3675_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(
    mut v_e_3721_: *mut LeanObject,
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_val_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3776_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_a_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: u8 = 0;
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: u8 = 0;
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: u8 = 0;
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3837_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_a_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_a_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3874_: u8 = 0;
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: u8 = 0;
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_a_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: u8 = 0;
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_val_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3964_: u8 = 0;
    let mut v_a_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_a_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4006_: u8 = 0;
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4018_: u8 = 0;
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_a_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3721_);
                v___x_3728_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3721_, v_a_3724_);
                if lean_obj_tag(v___x_3728_) == 0 {
                    v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
                    lean_inc(v_a_3729_);
                    lean_dec_ref_known(v___x_3728_, 1);
                    v___x_3730_ = l_Lean_Expr_cleanupAnnotations(v_a_3729_);
                    v___x_3731_ = l_Lean_Expr_isApp(v___x_3730_);
                    if v___x_3731_ == 0 {
                        lean_dec_ref(v___x_3730_);
                        v___x_3732_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                            v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_,
                        );
                        return v___x_3732_;
                    } else {
                        v_arg_3733_ = lean_ctor_get(v___x_3730_, 1);
                        lean_inc_ref(v_arg_3733_);
                        v___x_3734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3730_);
                        v___x_3735_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0;
                        v___x_3736_ = l_Lean_Expr_isConstOf(v___x_3734_, v___x_3735_);
                        if v___x_3736_ == 0 {
                            v___x_3737_ = l_Lean_Expr_isApp(v___x_3734_);
                            if v___x_3737_ == 0 {
                                lean_dec_ref(v___x_3734_);
                                lean_dec_ref(v_arg_3733_);
                                v___x_3738_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                                    v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_,
                                    v_a_3726_,
                                );
                                return v___x_3738_;
                            } else {
                                v_arg_3739_ = lean_ctor_get(v___x_3734_, 1);
                                lean_inc_ref(v_arg_3739_);
                                v___x_3790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3734_);
                                v___x_3791_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2;
                                v___x_3792_ = l_Lean_Expr_isConstOf(v___x_3790_, v___x_3791_);
                                if v___x_3792_ == 0 {
                                    v___x_3793_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3;
                                    v___x_3794_ = l_Lean_Expr_isConstOf(v___x_3790_, v___x_3793_);
                                    if v___x_3794_ == 0 {
                                        v___x_3795_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4;
                                        v___x_3796_ =
                                            l_Lean_Expr_isConstOf(v___x_3790_, v___x_3795_);
                                        if v___x_3796_ == 0 {
                                            v___x_3797_ = l_Lean_Expr_isApp(v___x_3790_);
                                            if v___x_3797_ == 0 {
                                                lean_dec_ref(v___x_3790_);
                                                lean_dec_ref(v_arg_3739_);
                                                lean_dec_ref(v_arg_3733_);
                                                v___x_3798_ =
                                                    l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                                                        v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_,
                                                        v_a_3725_, v_a_3726_,
                                                    );
                                                return v___x_3798_;
                                            } else {
                                                v_arg_3799_ = lean_ctor_get(v___x_3790_, 1);
                                                lean_inc_ref(v_arg_3799_);
                                                v___x_3800_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_3790_);
                                                v___x_3801_ =
                                                    l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
                                                v___x_3802_ =
                                                    l_Lean_Expr_isConstOf(v___x_3800_, v___x_3801_);
                                                if v___x_3802_ == 0 {
                                                    v___x_3803_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7;
                                                    v___x_3804_ = l_Lean_Expr_isConstOf(
                                                        v___x_3800_,
                                                        v___x_3803_,
                                                    );
                                                    if v___x_3804_ == 0 {
                                                        v___x_3805_ =
                                                            l_Lean_Expr_isApp(v___x_3800_);
                                                        if v___x_3805_ == 0 {
                                                            lean_dec_ref(v___x_3800_);
                                                            lean_dec_ref(v_arg_3799_);
                                                            lean_dec_ref(v_arg_3739_);
                                                            lean_dec_ref(v_arg_3733_);
                                                            v___x_3806_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                            return v___x_3806_;
                                                        } else {
                                                            v___x_3807_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_3800_,
                                                                );
                                                            v___x_3808_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9;
                                                            v___x_3809_ = l_Lean_Expr_isConstOf(
                                                                v___x_3807_,
                                                                v___x_3808_,
                                                            );
                                                            if v___x_3809_ == 0 {
                                                                v___x_3810_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11;
                                                                v___x_3811_ = l_Lean_Expr_isConstOf(
                                                                    v___x_3807_,
                                                                    v___x_3810_,
                                                                );
                                                                if v___x_3811_ == 0 {
                                                                    v___x_3812_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13;
                                                                    v___x_3813_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_3807_,
                                                                            v___x_3812_,
                                                                        );
                                                                    if v___x_3813_ == 0 {
                                                                        v___x_3814_ =
                                                                            l_Lean_Expr_isApp(
                                                                                v___x_3807_,
                                                                            );
                                                                        if v___x_3814_ == 0 {
                                                                            lean_dec_ref(
                                                                                v___x_3807_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3799_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3739_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3733_,
                                                                            );
                                                                            v___x_3815_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                            return v___x_3815_;
                                                                        } else {
                                                                            v___x_3816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3807_);
                                                                            v___x_3817_ =
                                                                                l_Lean_Expr_isApp(
                                                                                    v___x_3816_,
                                                                                );
                                                                            if v___x_3817_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v___x_3816_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3799_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3739_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3733_,
                                                                                );
                                                                                v___x_3818_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                return v___x_3818_;
                                                                            } else {
                                                                                v___x_3819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3816_);
                                                                                v___x_3820_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16;
                                                                                v___x_3821_ = l_Lean_Expr_isConstOf(v___x_3819_, v___x_3820_);
                                                                                if v___x_3821_ == 0
                                                                                {
                                                                                    v___x_3822_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19;
                                                                                    v___x_3823_ = l_Lean_Expr_isConstOf(v___x_3819_, v___x_3822_);
                                                                                    if v___x_3823_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_3824_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22;
                                                                                        v___x_3825_ = l_Lean_Expr_isConstOf(v___x_3819_, v___x_3824_);
                                                                                        lean_dec_ref(v___x_3819_);
                                                                                        if v___x_3825_ == 0 {
lean_dec_ref(v_arg_3799_);
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
v___x_3826_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3826_;
} else {
v___x_3827_ = l_Lean_Meta_DefEq_isInstHAddInt(v_arg_3799_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if lean_obj_tag(v___x_3827_) == 0 {
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
v___x_3829_ = (lean_unbox(v_a_3828_) as u8);
lean_dec(v_a_3828_);
if v___x_3829_ == 0 {
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
v___x_3830_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3830_;
} else {
lean_dec_ref(v_e_3721_);
v___x_3831_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if lean_obj_tag(v___x_3831_) == 0 {
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if lean_obj_tag(v___x_3833_) == 0 {
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3842_ = (!lean_is_exclusive(v___x_3833_)) as u8;
if v_isSharedCheck_3842_ == 0 {
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3842_;
state = 10; continue;
} else {
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3842_;
state = 10; continue;
}
} else {
lean_dec(v_a_3832_);
return v___x_3833_;
}
} else {
lean_dec_ref(v_arg_3733_);
return v___x_3831_;
}
}
} else {
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
lean_dec_ref(v_e_3721_);
v_a_3843_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3850_ = (!lean_is_exclusive(v___x_3827_)) as u8;
if v_isSharedCheck_3850_ == 0 {
v___x_3845_ = v___x_3827_;
v_isShared_3846_ = v_isSharedCheck_3850_;
state = 12; continue;
} else {
lean_inc(v_a_3843_);
lean_dec(v___x_3827_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
state = 12; continue;
}
}
}
                                                                                    } else {
                                                                                        lean_dec_ref(v___x_3819_);
                                                                                        v___x_3851_ = l_Lean_Meta_DefEq_isInstHSubInt(v_arg_3799_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                        if lean_obj_tag(v___x_3851_) == 0 {
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = (lean_unbox(v_a_3852_) as u8);
lean_dec(v_a_3852_);
if v___x_3853_ == 0 {
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
v___x_3854_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3854_;
} else {
lean_dec_ref(v_e_3721_);
v___x_3855_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if lean_obj_tag(v___x_3855_) == 0 {
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3857_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if lean_obj_tag(v___x_3857_) == 0 {
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3866_ = (!lean_is_exclusive(v___x_3857_)) as u8;
if v_isSharedCheck_3866_ == 0 {
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3866_;
state = 14; continue;
} else {
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3866_;
state = 14; continue;
}
} else {
lean_dec(v_a_3856_);
return v___x_3857_;
}
} else {
lean_dec_ref(v_arg_3733_);
return v___x_3855_;
}
}
} else {
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
lean_dec_ref(v_e_3721_);
v_a_3867_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3874_ = (!lean_is_exclusive(v___x_3851_)) as u8;
if v_isSharedCheck_3874_ == 0 {
v___x_3869_ = v___x_3851_;
v_isShared_3870_ = v_isSharedCheck_3874_;
state = 16; continue;
} else {
lean_inc(v_a_3867_);
lean_dec(v___x_3851_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
state = 16; continue;
}
}
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v___x_3819_,
                                                                                    );
                                                                                    v___x_3875_ = l_Lean_Meta_DefEq_isInstHMulInt(v_arg_3799_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_3875_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
                                                                                        lean_inc(v_a_3876_);
                                                                                        lean_dec_ref_known(v___x_3875_, 1);
                                                                                        v___x_3877_ = (lean_unbox(v_a_3876_) as u8);
                                                                                        lean_dec(v_a_3876_);
                                                                                        if v___x_3877_ == 0 {
lean_dec_ref(v_arg_3739_);
lean_dec_ref(v_arg_3733_);
v___x_3878_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3878_;
} else {
v_b_3741_ = v_arg_3733_;
v___y_3742_ = v_a_3722_;
v___y_3743_ = v_a_3723_;
v___y_3744_ = v_a_3724_;
v___y_3745_ = v_a_3725_;
v___y_3746_ = v_a_3726_;
state = 1; continue;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_arg_3739_);
                                                                                        lean_dec_ref(v_arg_3733_);
                                                                                        lean_dec_ref(v_e_3721_);
                                                                                        v_a_3879_ = lean_ctor_get(v___x_3875_, 0);
                                                                                        v_isSharedCheck_3886_ = (!lean_is_exclusive(v___x_3875_)) as u8;
                                                                                        if v_isSharedCheck_3886_ == 0 {
v___x_3881_ = v___x_3875_;
v_isShared_3882_ = v_isSharedCheck_3886_;
state = 18; continue;
} else {
lean_inc(v_a_3879_);
lean_dec(v___x_3875_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
state = 18; continue;
}
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_3807_);
                                                                        v___x_3887_ = l_Lean_Meta_DefEq_isInstAddInt(v_arg_3799_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                        if lean_obj_tag(v___x_3887_)
                                                                            == 0
                                                                        {
                                                                            v_a_3888_ =
                                                                                lean_ctor_get(
                                                                                    v___x_3887_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_3888_);
                                                                            lean_dec_ref_known(
                                                                                v___x_3887_,
                                                                                1,
                                                                            );
                                                                            v___x_3889_ =
                                                                                (lean_unbox(
                                                                                    v_a_3888_,
                                                                                )
                                                                                    as u8);
                                                                            lean_dec(v_a_3888_);
                                                                            if v___x_3889_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_3739_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3733_,
                                                                                );
                                                                                v___x_3890_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                return v___x_3890_;
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_e_3721_,
                                                                                );
                                                                                v___x_3891_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                if lean_obj_tag(
                                                                                    v___x_3891_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
                                                                                    lean_inc(
                                                                                        v_a_3892_,
                                                                                    );
                                                                                    lean_dec_ref_known(v___x_3891_, 1);
                                                                                    v___x_3893_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_3893_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
                                                                                        v_isSharedCheck_3902_ = (!lean_is_exclusive(v___x_3893_)) as u8;
                                                                                        if v_isSharedCheck_3902_ == 0 {
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3902_;
state = 20; continue;
} else {
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3902_;
state = 20; continue;
}
                                                                                    } else {
                                                                                        lean_dec(v_a_3892_);
                                                                                        return v___x_3893_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_3733_,
                                                                                    );
                                                                                    return v___x_3891_;
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_3739_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3733_,
                                                                            );
                                                                            lean_dec_ref(v_e_3721_);
                                                                            v_a_3903_ =
                                                                                lean_ctor_get(
                                                                                    v___x_3887_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_3910_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_3887_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_3910_
                                                                                == 0
                                                                            {
                                                                                v___x_3905_ =
                                                                                    v___x_3887_;
                                                                                v_isShared_3906_ = v_isSharedCheck_3910_;
                                                                                state = 22;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_3903_);
                                                                                lean_dec(
                                                                                    v___x_3887_,
                                                                                );
                                                                                v___x_3905_ =
                                                                                    lean_box(0);
                                                                                v_isShared_3906_ = v_isSharedCheck_3910_;
                                                                                state = 22;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_3807_);
                                                                    v___x_3911_ = l_Lean_Meta_DefEq_isInstSubInt(v_arg_3799_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                    if lean_obj_tag(v___x_3911_)
                                                                        == 0
                                                                    {
                                                                        v_a_3912_ = lean_ctor_get(
                                                                            v___x_3911_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_3912_);
                                                                        lean_dec_ref_known(
                                                                            v___x_3911_,
                                                                            1,
                                                                        );
                                                                        v___x_3913_ =
                                                                            (lean_unbox(v_a_3912_)
                                                                                as u8);
                                                                        lean_dec(v_a_3912_);
                                                                        if v___x_3913_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_3739_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3733_,
                                                                            );
                                                                            v___x_3914_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                            return v___x_3914_;
                                                                        } else {
                                                                            lean_dec_ref(v_e_3721_);
                                                                            v___x_3915_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                            if lean_obj_tag(
                                                                                v___x_3915_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_3916_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_3915_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_a_3916_);
                                                                                lean_dec_ref_known(
                                                                                    v___x_3915_,
                                                                                    1,
                                                                                );
                                                                                v___x_3917_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                                if lean_obj_tag(
                                                                                    v___x_3917_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
                                                                                    v_isSharedCheck_3926_ = (!lean_is_exclusive(v___x_3917_)) as u8;
                                                                                    if v_isSharedCheck_3926_ == 0 {
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3926_;
state = 24; continue;
} else {
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
state = 24; continue;
}
                                                                                } else {
                                                                                    lean_dec(
                                                                                        v_a_3916_,
                                                                                    );
                                                                                    return v___x_3917_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_3733_,
                                                                                );
                                                                                return v___x_3915_;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_3739_);
                                                                        lean_dec_ref(v_arg_3733_);
                                                                        lean_dec_ref(v_e_3721_);
                                                                        v_a_3927_ = lean_ctor_get(
                                                                            v___x_3911_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_3934_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_3911_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_3934_
                                                                            == 0
                                                                        {
                                                                            v___x_3929_ =
                                                                                v___x_3911_;
                                                                            v_isShared_3930_ = v_isSharedCheck_3934_;
                                                                            state = 26;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_3927_);
                                                                            lean_dec(v___x_3911_);
                                                                            v___x_3929_ =
                                                                                lean_box(0);
                                                                            v_isShared_3930_ = v_isSharedCheck_3934_;
                                                                            state = 26;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_3807_);
                                                                v___x_3935_ =
                                                                    l_Lean_Meta_DefEq_isInstMulInt(
                                                                        v_arg_3799_,
                                                                        v_a_3723_,
                                                                        v_a_3724_,
                                                                        v_a_3725_,
                                                                        v_a_3726_,
                                                                    );
                                                                if lean_obj_tag(v___x_3935_) == 0 {
                                                                    v_a_3936_ = lean_ctor_get(
                                                                        v___x_3935_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_a_3936_);
                                                                    lean_dec_ref_known(
                                                                        v___x_3935_,
                                                                        1,
                                                                    );
                                                                    v___x_3937_ =
                                                                        (lean_unbox(v_a_3936_)
                                                                            as u8);
                                                                    lean_dec(v_a_3936_);
                                                                    if v___x_3937_ == 0 {
                                                                        lean_dec_ref(v_arg_3739_);
                                                                        lean_dec_ref(v_arg_3733_);
                                                                        v___x_3938_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                                        return v___x_3938_;
                                                                    } else {
                                                                        v_b_3741_ = v_arg_3733_;
                                                                        v___y_3742_ = v_a_3722_;
                                                                        v___y_3743_ = v_a_3723_;
                                                                        v___y_3744_ = v_a_3724_;
                                                                        v___y_3745_ = v_a_3725_;
                                                                        v___y_3746_ = v_a_3726_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_3739_);
                                                                    lean_dec_ref(v_arg_3733_);
                                                                    lean_dec_ref(v_e_3721_);
                                                                    v_a_3939_ = lean_ctor_get(
                                                                        v___x_3935_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_3946_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_3935_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_3946_ == 0 {
                                                                        v___x_3941_ = v___x_3935_;
                                                                        v_isShared_3942_ =
                                                                            v_isSharedCheck_3946_;
                                                                        state = 28;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_3939_);
                                                                        lean_dec(v___x_3935_);
                                                                        v___x_3941_ = lean_box(0);
                                                                        v_isShared_3942_ =
                                                                            v_isSharedCheck_3946_;
                                                                        state = 28;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_3800_);
                                                        lean_dec_ref(v_arg_3799_);
                                                        lean_dec_ref(v_arg_3739_);
                                                        lean_dec_ref(v_arg_3733_);
                                                        lean_inc_ref(v_e_3721_);
                                                        v___x_3947_ = l_Lean_Meta_getIntValue_x3f(
                                                            v_e_3721_, v_a_3723_, v_a_3724_,
                                                            v_a_3725_, v_a_3726_,
                                                        );
                                                        if lean_obj_tag(v___x_3947_) == 0 {
                                                            v_a_3948_ =
                                                                lean_ctor_get(v___x_3947_, 0);
                                                            v_isSharedCheck_3964_ =
                                                                (!lean_is_exclusive(v___x_3947_))
                                                                    as u8;
                                                            if v_isSharedCheck_3964_ == 0 {
                                                                v___x_3950_ = v___x_3947_;
                                                                v_isShared_3951_ =
                                                                    v_isSharedCheck_3964_;
                                                                state = 30;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3948_);
                                                                lean_dec(v___x_3947_);
                                                                v___x_3950_ = lean_box(0);
                                                                v_isShared_3951_ =
                                                                    v_isSharedCheck_3964_;
                                                                state = 30;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_e_3721_);
                                                            v_a_3965_ =
                                                                lean_ctor_get(v___x_3947_, 0);
                                                            v_isSharedCheck_3972_ =
                                                                (!lean_is_exclusive(v___x_3947_))
                                                                    as u8;
                                                            if v_isSharedCheck_3972_ == 0 {
                                                                v___x_3967_ = v___x_3947_;
                                                                v_isShared_3968_ =
                                                                    v_isSharedCheck_3972_;
                                                                state = 34;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3965_);
                                                                lean_dec(v___x_3947_);
                                                                v___x_3967_ = lean_box(0);
                                                                v_isShared_3968_ =
                                                                    v_isSharedCheck_3972_;
                                                                state = 34;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_3800_);
                                                    lean_dec_ref(v_arg_3799_);
                                                    v___x_3973_ = l_Lean_Meta_DefEq_isInstNegInt(
                                                        v_arg_3739_,
                                                        v_a_3723_,
                                                        v_a_3724_,
                                                        v_a_3725_,
                                                        v_a_3726_,
                                                    );
                                                    if lean_obj_tag(v___x_3973_) == 0 {
                                                        v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
                                                        lean_inc(v_a_3974_);
                                                        lean_dec_ref_known(v___x_3973_, 1);
                                                        v___x_3975_ = (lean_unbox(v_a_3974_) as u8);
                                                        lean_dec(v_a_3974_);
                                                        if v___x_3975_ == 0 {
                                                            lean_dec_ref(v_arg_3733_);
                                                            v___x_3976_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                            return v___x_3976_;
                                                        } else {
                                                            lean_dec_ref(v_e_3721_);
                                                            v___x_3977_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                            if lean_obj_tag(v___x_3977_) == 0 {
                                                                v_a_3978_ =
                                                                    lean_ctor_get(v___x_3977_, 0);
                                                                v_isSharedCheck_3986_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3977_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3986_ == 0 {
                                                                    v___x_3980_ = v___x_3977_;
                                                                    v_isShared_3981_ =
                                                                        v_isSharedCheck_3986_;
                                                                    state = 36;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3978_);
                                                                    lean_dec(v___x_3977_);
                                                                    v___x_3980_ = lean_box(0);
                                                                    v_isShared_3981_ =
                                                                        v_isSharedCheck_3986_;
                                                                    state = 36;
                                                                    continue;
                                                                }
                                                            } else {
                                                                return v___x_3977_;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_3733_);
                                                        lean_dec_ref(v_e_3721_);
                                                        v_a_3987_ = lean_ctor_get(v___x_3973_, 0);
                                                        v_isSharedCheck_3994_ =
                                                            (!lean_is_exclusive(v___x_3973_)) as u8;
                                                        if v_isSharedCheck_3994_ == 0 {
                                                            v___x_3989_ = v___x_3973_;
                                                            v_isShared_3990_ =
                                                                v_isSharedCheck_3994_;
                                                            state = 38;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3987_);
                                                            lean_dec(v___x_3973_);
                                                            v___x_3989_ = lean_box(0);
                                                            v_isShared_3990_ =
                                                                v_isSharedCheck_3994_;
                                                            state = 38;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3790_);
                                            lean_dec_ref(v_e_3721_);
                                            v___x_3995_ =
                                                l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                                    v_arg_3739_,
                                                    v_a_3722_,
                                                    v_a_3723_,
                                                    v_a_3724_,
                                                    v_a_3725_,
                                                    v_a_3726_,
                                                );
                                            if lean_obj_tag(v___x_3995_) == 0 {
                                                v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
                                                lean_inc(v_a_3996_);
                                                lean_dec_ref_known(v___x_3995_, 1);
                                                v___x_3997_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_3733_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
                                                if lean_obj_tag(v___x_3997_) == 0 {
                                                    v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
                                                    v_isSharedCheck_4006_ =
                                                        (!lean_is_exclusive(v___x_3997_)) as u8;
                                                    if v_isSharedCheck_4006_ == 0 {
                                                        v___x_4000_ = v___x_3997_;
                                                        v_isShared_4001_ = v_isSharedCheck_4006_;
                                                        state = 40;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3998_);
                                                        lean_dec(v___x_3997_);
                                                        v___x_4000_ = lean_box(0);
                                                        v_isShared_4001_ = v_isSharedCheck_4006_;
                                                        state = 40;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_a_3996_);
                                                    return v___x_3997_;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_3733_);
                                                return v___x_3995_;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3790_);
                                        lean_dec_ref(v_e_3721_);
                                        v___x_4007_ =
                                            l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                                v_arg_3739_,
                                                v_a_3722_,
                                                v_a_3723_,
                                                v_a_3724_,
                                                v_a_3725_,
                                                v_a_3726_,
                                            );
                                        if lean_obj_tag(v___x_4007_) == 0 {
                                            v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
                                            lean_inc(v_a_4008_);
                                            lean_dec_ref_known(v___x_4007_, 1);
                                            v___x_4009_ =
                                                l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                                    v_arg_3733_,
                                                    v_a_3722_,
                                                    v_a_3723_,
                                                    v_a_3724_,
                                                    v_a_3725_,
                                                    v_a_3726_,
                                                );
                                            if lean_obj_tag(v___x_4009_) == 0 {
                                                v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
                                                v_isSharedCheck_4018_ =
                                                    (!lean_is_exclusive(v___x_4009_)) as u8;
                                                if v_isSharedCheck_4018_ == 0 {
                                                    v___x_4012_ = v___x_4009_;
                                                    v_isShared_4013_ = v_isSharedCheck_4018_;
                                                    state = 42;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4010_);
                                                    lean_dec(v___x_4009_);
                                                    v___x_4012_ = lean_box(0);
                                                    v_isShared_4013_ = v_isSharedCheck_4018_;
                                                    state = 42;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_4008_);
                                                return v___x_4009_;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_3733_);
                                            return v___x_4007_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3790_);
                                    v_b_3741_ = v_arg_3733_;
                                    v___y_3742_ = v_a_3722_;
                                    v___y_3743_ = v_a_3723_;
                                    v___y_3744_ = v_a_3724_;
                                    v___y_3745_ = v_a_3725_;
                                    v___y_3746_ = v_a_3726_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3734_);
                            lean_dec_ref(v_e_3721_);
                            v___x_4019_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                v_arg_3733_,
                                v_a_3722_,
                                v_a_3723_,
                                v_a_3724_,
                                v_a_3725_,
                                v_a_3726_,
                            );
                            if lean_obj_tag(v___x_4019_) == 0 {
                                v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
                                v_isSharedCheck_4028_ = (!lean_is_exclusive(v___x_4019_)) as u8;
                                if v_isSharedCheck_4028_ == 0 {
                                    v___x_4022_ = v___x_4019_;
                                    v_isShared_4023_ = v_isSharedCheck_4028_;
                                    state = 44;
                                    continue;
                                } else {
                                    lean_inc(v_a_4020_);
                                    lean_dec(v___x_4019_);
                                    v___x_4022_ = lean_box(0);
                                    v_isShared_4023_ = v_isSharedCheck_4028_;
                                    state = 44;
                                    continue;
                                }
                            } else {
                                return v___x_4019_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3721_);
                    v_a_4029_ = lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_4036_ = (!lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_4036_ == 0 {
                        v___x_4031_ = v___x_3728_;
                        v_isShared_4032_ = v_isSharedCheck_4036_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_4029_);
                        lean_dec(v___x_3728_);
                        v___x_4031_ = lean_box(0);
                        v_isShared_4032_ = v_isSharedCheck_4036_;
                        state = 46;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_arg_3739_);
                v___x_3747_ = l_Lean_Meta_getIntValue_x3f(
                    v_arg_3739_,
                    v___y_3743_,
                    v___y_3744_,
                    v___y_3745_,
                    v___y_3746_,
                );
                if lean_obj_tag(v___x_3747_) == 0 {
                    v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
                    lean_inc(v_a_3748_);
                    lean_dec_ref_known(v___x_3747_, 1);
                    if lean_obj_tag(v_a_3748_) == 0 {
                        v___x_3749_ = l_Lean_Meta_getIntValue_x3f(
                            v_b_3741_,
                            v___y_3743_,
                            v___y_3744_,
                            v___y_3745_,
                            v___y_3746_,
                        );
                        if lean_obj_tag(v___x_3749_) == 0 {
                            v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
                            lean_inc(v_a_3750_);
                            lean_dec_ref_known(v___x_3749_, 1);
                            if lean_obj_tag(v_a_3750_) == 0 {
                                lean_dec_ref(v_arg_3739_);
                                v___x_3751_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                                    v_e_3721_,
                                    v___y_3742_,
                                    v___y_3743_,
                                    v___y_3744_,
                                    v___y_3745_,
                                    v___y_3746_,
                                );
                                return v___x_3751_;
                            } else {
                                lean_dec_ref(v_e_3721_);
                                v_val_3752_ = lean_ctor_get(v_a_3750_, 0);
                                lean_inc(v_val_3752_);
                                lean_dec_ref_known(v_a_3750_, 1);
                                v___x_3753_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                    v_arg_3739_,
                                    v___y_3742_,
                                    v___y_3743_,
                                    v___y_3744_,
                                    v___y_3745_,
                                    v___y_3746_,
                                );
                                if lean_obj_tag(v___x_3753_) == 0 {
                                    v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
                                    v_isSharedCheck_3762_ = (!lean_is_exclusive(v___x_3753_)) as u8;
                                    if v_isSharedCheck_3762_ == 0 {
                                        v___x_3756_ = v___x_3753_;
                                        v_isShared_3757_ = v_isSharedCheck_3762_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3754_);
                                        lean_dec(v___x_3753_);
                                        v___x_3756_ = lean_box(0);
                                        v_isShared_3757_ = v_isSharedCheck_3762_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_3752_);
                                    return v___x_3753_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_3739_);
                            lean_dec_ref(v_e_3721_);
                            v_a_3763_ = lean_ctor_get(v___x_3749_, 0);
                            v_isSharedCheck_3770_ = (!lean_is_exclusive(v___x_3749_)) as u8;
                            if v_isSharedCheck_3770_ == 0 {
                                v___x_3765_ = v___x_3749_;
                                v_isShared_3766_ = v_isSharedCheck_3770_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3763_);
                                lean_dec(v___x_3749_);
                                v___x_3765_ = lean_box(0);
                                v_isShared_3766_ = v_isSharedCheck_3770_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3739_);
                        lean_dec_ref(v_e_3721_);
                        v_val_3771_ = lean_ctor_get(v_a_3748_, 0);
                        lean_inc(v_val_3771_);
                        lean_dec_ref_known(v_a_3748_, 1);
                        v___x_3772_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                            v_b_3741_,
                            v___y_3742_,
                            v___y_3743_,
                            v___y_3744_,
                            v___y_3745_,
                            v___y_3746_,
                        );
                        if lean_obj_tag(v___x_3772_) == 0 {
                            v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
                            v_isSharedCheck_3781_ = (!lean_is_exclusive(v___x_3772_)) as u8;
                            if v_isSharedCheck_3781_ == 0 {
                                v___x_3775_ = v___x_3772_;
                                v_isShared_3776_ = v_isSharedCheck_3781_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3773_);
                                lean_dec(v___x_3772_);
                                v___x_3775_ = lean_box(0);
                                v_isShared_3776_ = v_isSharedCheck_3781_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_3771_);
                            return v___x_3772_;
                        }
                    }
                } else {
                    lean_dec_ref(v_b_3741_);
                    lean_dec_ref(v_arg_3739_);
                    lean_dec_ref(v_e_3721_);
                    v_a_3782_ = lean_ctor_get(v___x_3747_, 0);
                    v_isSharedCheck_3789_ = (!lean_is_exclusive(v___x_3747_)) as u8;
                    if v_isSharedCheck_3789_ == 0 {
                        v___x_3784_ = v___x_3747_;
                        v_isShared_3785_ = v_isSharedCheck_3789_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3782_);
                        lean_dec(v___x_3747_);
                        v___x_3784_ = lean_box(0);
                        v_isShared_3785_ = v_isSharedCheck_3789_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3758_ = lean_alloc_ctor(6, 2, (0) as u32);
                lean_ctor_set(v___x_3758_, 0, v_a_3754_);
                lean_ctor_set(v___x_3758_, 1, v_val_3752_);
                if v_isShared_3757_ == 0 {
                    lean_ctor_set(v___x_3756_, 0, v___x_3758_);
                    v___x_3760_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
                    v___x_3760_ = v_reuseFailAlloc_3761_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3760_;
            }
            4 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3768_;
            }
            6 => {
                v___x_3777_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3777_, 0, v_val_3771_);
                lean_ctor_set(v___x_3777_, 1, v_a_3773_);
                if v_isShared_3776_ == 0 {
                    lean_ctor_set(v___x_3775_, 0, v___x_3777_);
                    v___x_3779_ = v___x_3775_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
                    v___x_3779_ = v_reuseFailAlloc_3780_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3779_;
            }
            8 => {
                if v_isShared_3785_ == 0 {
                    v___x_3787_ = v___x_3784_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
                    v___x_3787_ = v_reuseFailAlloc_3788_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3787_;
            }
            10 => {
                v___x_3838_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3838_, 0, v_a_3832_);
                lean_ctor_set(v___x_3838_, 1, v_a_3834_);
                if v_isShared_3837_ == 0 {
                    lean_ctor_set(v___x_3836_, 0, v___x_3838_);
                    v___x_3840_ = v___x_3836_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3840_;
            }
            12 => {
                if v_isShared_3846_ == 0 {
                    v___x_3848_ = v___x_3845_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3848_;
            }
            14 => {
                v___x_3862_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_3862_, 0, v_a_3856_);
                lean_ctor_set(v___x_3862_, 1, v_a_3858_);
                if v_isShared_3861_ == 0 {
                    lean_ctor_set(v___x_3860_, 0, v___x_3862_);
                    v___x_3864_ = v___x_3860_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
                    v___x_3864_ = v_reuseFailAlloc_3865_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3864_;
            }
            16 => {
                if v_isShared_3870_ == 0 {
                    v___x_3872_ = v___x_3869_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
                    v___x_3872_ = v_reuseFailAlloc_3873_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3872_;
            }
            18 => {
                if v_isShared_3882_ == 0 {
                    v___x_3884_ = v___x_3881_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
                    v___x_3884_ = v_reuseFailAlloc_3885_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3884_;
            }
            20 => {
                v___x_3898_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v_a_3892_);
                lean_ctor_set(v___x_3898_, 1, v_a_3894_);
                if v_isShared_3897_ == 0 {
                    lean_ctor_set(v___x_3896_, 0, v___x_3898_);
                    v___x_3900_ = v___x_3896_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
                    v___x_3900_ = v_reuseFailAlloc_3901_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3900_;
            }
            22 => {
                if v_isShared_3906_ == 0 {
                    v___x_3908_ = v___x_3905_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3908_;
            }
            24 => {
                v___x_3922_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_3922_, 0, v_a_3916_);
                lean_ctor_set(v___x_3922_, 1, v_a_3918_);
                if v_isShared_3921_ == 0 {
                    lean_ctor_set(v___x_3920_, 0, v___x_3922_);
                    v___x_3924_ = v___x_3920_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3924_;
            }
            26 => {
                if v_isShared_3930_ == 0 {
                    v___x_3932_ = v___x_3929_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3932_;
            }
            28 => {
                if v_isShared_3942_ == 0 {
                    v___x_3944_ = v___x_3941_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3944_;
            }
            30 => {
                if lean_obj_tag(v_a_3948_) == 1 {
                    lean_dec_ref(v_e_3721_);
                    v_val_3952_ = lean_ctor_get(v_a_3948_, 0);
                    v_isSharedCheck_3962_ = (!lean_is_exclusive(v_a_3948_)) as u8;
                    if v_isSharedCheck_3962_ == 0 {
                        v___x_3954_ = v_a_3948_;
                        v_isShared_3955_ = v_isSharedCheck_3962_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_val_3952_);
                        lean_dec(v_a_3948_);
                        v___x_3954_ = lean_box(0);
                        v_isShared_3955_ = v_isSharedCheck_3962_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3950_);
                    lean_dec(v_a_3948_);
                    v___x_3963_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                        v_e_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_,
                    );
                    return v___x_3963_;
                }
            }
            31 => {
                if v_isShared_3955_ == 0 {
                    lean_ctor_set_tag(v___x_3954_, 0);
                    v___x_3957_ = v___x_3954_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_val_3952_);
                    v___x_3957_ = v_reuseFailAlloc_3961_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3951_ == 0 {
                    lean_ctor_set(v___x_3950_, 0, v___x_3957_);
                    v___x_3959_ = v___x_3950_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
                    v___x_3959_ = v_reuseFailAlloc_3960_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3959_;
            }
            34 => {
                if v_isShared_3968_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3970_;
            }
            36 => {
                v___x_3982_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_3982_, 0, v_a_3978_);
                if v_isShared_3981_ == 0 {
                    lean_ctor_set(v___x_3980_, 0, v___x_3982_);
                    v___x_3984_ = v___x_3980_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
                    v___x_3984_ = v_reuseFailAlloc_3985_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3984_;
            }
            38 => {
                if v_isShared_3990_ == 0 {
                    v___x_3992_ = v___x_3989_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3992_;
            }
            40 => {
                v___x_4002_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4002_, 0, v_a_3996_);
                lean_ctor_set(v___x_4002_, 1, v_a_3998_);
                if v_isShared_4001_ == 0 {
                    lean_ctor_set(v___x_4000_, 0, v___x_4002_);
                    v___x_4004_ = v___x_4000_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
                    v___x_4004_ = v_reuseFailAlloc_4005_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4004_;
            }
            42 => {
                v___x_4014_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_4014_, 0, v_a_4008_);
                lean_ctor_set(v___x_4014_, 1, v_a_4010_);
                if v_isShared_4013_ == 0 {
                    lean_ctor_set(v___x_4012_, 0, v___x_4014_);
                    v___x_4016_ = v___x_4012_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
                    v___x_4016_ = v_reuseFailAlloc_4017_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4016_;
            }
            44 => {
                v___x_4024_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_4024_, 0, v_a_4020_);
                if v_isShared_4023_ == 0 {
                    lean_ctor_set(v___x_4022_, 0, v___x_4024_);
                    v___x_4026_ = v___x_4022_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4026_;
            }
            46 => {
                if v_isShared_4032_ == 0 {
                    v___x_4034_ = v___x_4031_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
    mut v_e_4037_: *mut LeanObject,
    mut v_a_4038_: *mut LeanObject,
    mut v_a_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_4037_) {
                10 => {
                    v_expr_4044_ = lean_ctor_get(v_e_4037_, 1);
                    lean_inc_ref(v_expr_4044_);
                    lean_dec_ref_known(v_e_4037_, 2);
                    v_e_4037_ = v_expr_4044_;
                    state = 0;
                    continue;
                }
                5 => {
                    v___x_4046_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
                    return v___x_4046_;
                }
                2 => {
                    v___x_4047_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
                    return v___x_4047_;
                }
                _ => {
                    v___x_4048_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(
                        v_e_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_,
                    );
                    return v___x_4048_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(
    mut v_e_4049_: *mut LeanObject,
    mut v_a_4050_: *mut LeanObject,
    mut v_a_4051_: *mut LeanObject,
    mut v_a_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
    mut v_a_4054_: *mut LeanObject,
    mut v_a_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4056_: *mut LeanObject = core::ptr::null_mut();
    v_res_4056_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
        v_e_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_,
    );
    lean_dec(v_a_4054_);
    lean_dec_ref(v_a_4053_);
    lean_dec(v_a_4052_);
    lean_dec_ref(v_a_4051_);
    lean_dec(v_a_4050_);
    return v_res_4056_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(
    mut v_e_4057_: *mut LeanObject,
    mut v_a_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
    mut v_a_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4064_: *mut LeanObject = core::ptr::null_mut();
    v_res_4064_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
    lean_dec(v_a_4062_);
    lean_dec_ref(v_a_4061_);
    lean_dec(v_a_4060_);
    lean_dec_ref(v_a_4059_);
    lean_dec(v_a_4058_);
    return v_res_4064_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(
    mut v_e_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: u8 = 0;
    let mut v_arg_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v_arg_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v_arg_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4113_: u8 = 0;
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_a_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4145_: u8 = 0;
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v_a_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v_a_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4159_: u8 = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_a_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4075_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4068_, v_a_4071_);
                if lean_obj_tag(v___x_4075_) == 0 {
                    v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
                    v_isSharedCheck_4164_ = (!lean_is_exclusive(v___x_4075_)) as u8;
                    if v_isSharedCheck_4164_ == 0 {
                        v___x_4078_ = v___x_4075_;
                        v_isShared_4079_ = v_isSharedCheck_4164_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4076_);
                        lean_dec(v___x_4075_);
                        v___x_4078_ = lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4164_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4165_ = lean_ctor_get(v___x_4075_, 0);
                    v_isSharedCheck_4172_ = (!lean_is_exclusive(v___x_4075_)) as u8;
                    if v_isSharedCheck_4172_ == 0 {
                        v___x_4167_ = v___x_4075_;
                        v_isShared_4168_ = v_isSharedCheck_4172_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4165_);
                        lean_dec(v___x_4075_);
                        v___x_4167_ = lean_box(0);
                        v_isShared_4168_ = v_isSharedCheck_4172_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4085_ = l_Lean_Expr_cleanupAnnotations(v_a_4076_);
                v___x_4086_ = l_Lean_Expr_isApp(v___x_4085_);
                if v___x_4086_ == 0 {
                    lean_dec_ref(v___x_4085_);
                    state = 2;
                    continue;
                } else {
                    v_arg_4087_ = lean_ctor_get(v___x_4085_, 1);
                    lean_inc_ref(v_arg_4087_);
                    v___x_4088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4085_);
                    v___x_4089_ = l_Lean_Expr_isApp(v___x_4088_);
                    if v___x_4089_ == 0 {
                        lean_dec_ref(v___x_4088_);
                        lean_dec_ref(v_arg_4087_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_4090_ = lean_ctor_get(v___x_4088_, 1);
                        lean_inc_ref(v_arg_4090_);
                        v___x_4091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4088_);
                        v___x_4092_ = l_Lean_Expr_isApp(v___x_4091_);
                        if v___x_4092_ == 0 {
                            lean_dec_ref(v___x_4091_);
                            lean_dec_ref(v_arg_4090_);
                            lean_dec_ref(v_arg_4087_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_4093_ = lean_ctor_get(v___x_4091_, 1);
                            lean_inc_ref(v_arg_4093_);
                            v___x_4094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4091_);
                            v___x_4095_ =
                                l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1;
                            v___x_4096_ = l_Lean_Expr_isConstOf(v___x_4094_, v___x_4095_);
                            lean_dec_ref(v___x_4094_);
                            if v___x_4096_ == 0 {
                                lean_dec_ref(v_arg_4093_);
                                lean_dec_ref(v_arg_4090_);
                                lean_dec_ref(v_arg_4087_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4078_);
                                v___x_4097_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                    v_arg_4093_,
                                    v_a_4071_,
                                );
                                if lean_obj_tag(v___x_4097_) == 0 {
                                    v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
                                    v_isSharedCheck_4155_ = (!lean_is_exclusive(v___x_4097_)) as u8;
                                    if v_isSharedCheck_4155_ == 0 {
                                        v___x_4100_ = v___x_4097_;
                                        v_isShared_4101_ = v_isSharedCheck_4155_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4098_);
                                        lean_dec(v___x_4097_);
                                        v___x_4100_ = lean_box(0);
                                        v_isShared_4101_ = v_isSharedCheck_4155_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_4090_);
                                    lean_dec_ref(v_arg_4087_);
                                    v_a_4156_ = lean_ctor_get(v___x_4097_, 0);
                                    v_isSharedCheck_4163_ = (!lean_is_exclusive(v___x_4097_)) as u8;
                                    if v_isSharedCheck_4163_ == 0 {
                                        v___x_4158_ = v___x_4097_;
                                        v_isShared_4159_ = v_isSharedCheck_4163_;
                                        state = 17;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4156_);
                                        lean_dec(v___x_4097_);
                                        v___x_4158_ = lean_box(0);
                                        v_isShared_4159_ = v_isSharedCheck_4163_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4081_ = lean_box(0);
                if v_isShared_4079_ == 0 {
                    lean_ctor_set(v___x_4078_, 0, v___x_4081_);
                    v___x_4083_ = v___x_4078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4083_;
            }
            4 => {
                v___x_4102_ = l_Lean_Expr_cleanupAnnotations(v_a_4098_);
                v___x_4103_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
                v___x_4104_ = l_Lean_Expr_isConstOf(v___x_4102_, v___x_4103_);
                lean_dec_ref(v___x_4102_);
                if v___x_4104_ == 0 {
                    lean_dec_ref(v_arg_4090_);
                    lean_dec_ref(v_arg_4087_);
                    v___x_4105_ = lean_box(0);
                    if v_isShared_4101_ == 0 {
                        lean_ctor_set(v___x_4100_, 0, v___x_4105_);
                        v___x_4107_ = v___x_4100_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
                        v___x_4107_ = v_reuseFailAlloc_4108_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4100_);
                    v___x_4109_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                        v_arg_4090_,
                        v_a_4069_,
                        v_a_4070_,
                        v_a_4071_,
                        v_a_4072_,
                        v_a_4073_,
                    );
                    if lean_obj_tag(v___x_4109_) == 0 {
                        v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
                        v_isSharedCheck_4146_ = (!lean_is_exclusive(v___x_4109_)) as u8;
                        if v_isSharedCheck_4146_ == 0 {
                            v___x_4112_ = v___x_4109_;
                            v_isShared_4113_ = v_isSharedCheck_4146_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4110_);
                            lean_dec(v___x_4109_);
                            v___x_4112_ = lean_box(0);
                            v_isShared_4113_ = v_isSharedCheck_4146_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_4087_);
                        v_a_4147_ = lean_ctor_get(v___x_4109_, 0);
                        v_isSharedCheck_4154_ = (!lean_is_exclusive(v___x_4109_)) as u8;
                        if v_isSharedCheck_4154_ == 0 {
                            v___x_4149_ = v___x_4109_;
                            v_isShared_4150_ = v_isSharedCheck_4154_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_4147_);
                            lean_dec(v___x_4109_);
                            v___x_4149_ = lean_box(0);
                            v_isShared_4150_ = v_isSharedCheck_4154_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_4107_;
            }
            6 => {
                v___x_4114_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                    v_arg_4087_,
                    v_a_4069_,
                    v_a_4070_,
                    v_a_4071_,
                    v_a_4072_,
                    v_a_4073_,
                );
                if lean_obj_tag(v___x_4114_) == 0 {
                    v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
                    v_isSharedCheck_4137_ = (!lean_is_exclusive(v___x_4114_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4117_ = v___x_4114_;
                        v_isShared_4118_ = v_isSharedCheck_4137_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4115_);
                        lean_dec(v___x_4114_);
                        v___x_4117_ = lean_box(0);
                        v_isShared_4118_ = v_isSharedCheck_4137_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4112_);
                    lean_dec(v_a_4110_);
                    v_a_4138_ = lean_ctor_get(v___x_4114_, 0);
                    v_isSharedCheck_4145_ = (!lean_is_exclusive(v___x_4114_)) as u8;
                    if v_isSharedCheck_4145_ == 0 {
                        v___x_4140_ = v___x_4114_;
                        v_isShared_4141_ = v_isSharedCheck_4145_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4138_);
                        lean_dec(v___x_4114_);
                        v___x_4140_ = lean_box(0);
                        v_isShared_4141_ = v_isSharedCheck_4145_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => match lean_obj_tag(v_a_4110_) {
                1 => match lean_obj_tag(v_a_4115_) {
                    1 => {
                        lean_dec_ref_known(v_a_4115_, 1);
                        lean_dec_ref_known(v_a_4110_, 1);
                        lean_del_object(v___x_4117_);
                        v___x_4125_ = lean_box(0);
                        if v_isShared_4113_ == 0 {
                            lean_ctor_set(v___x_4112_, 0, v___x_4125_);
                            v___x_4127_ = v___x_4112_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
                            v___x_4127_ = v_reuseFailAlloc_4128_;
                            state = 10;
                            continue;
                        }
                    }
                    0 => {
                        lean_dec_ref_known(v_a_4115_, 1);
                        lean_dec_ref_known(v_a_4110_, 1);
                        lean_del_object(v___x_4117_);
                        v___x_4129_ = lean_box(0);
                        if v_isShared_4113_ == 0 {
                            lean_ctor_set(v___x_4112_, 0, v___x_4129_);
                            v___x_4131_ = v___x_4112_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                            v___x_4131_ = v_reuseFailAlloc_4132_;
                            state = 11;
                            continue;
                        }
                    }
                    _ => {
                        lean_del_object(v___x_4112_);
                        state = 8;
                        continue;
                    }
                },
                0 => {
                    if lean_obj_tag(v_a_4115_) == 1 {
                        lean_dec_ref_known(v_a_4115_, 1);
                        lean_dec_ref_known(v_a_4110_, 1);
                        lean_del_object(v___x_4117_);
                        v___x_4133_ = lean_box(0);
                        if v_isShared_4113_ == 0 {
                            lean_ctor_set(v___x_4112_, 0, v___x_4133_);
                            v___x_4135_ = v___x_4112_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
                            v___x_4135_ = v_reuseFailAlloc_4136_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4112_);
                        state = 8;
                        continue;
                    }
                }
                _ => {
                    lean_del_object(v___x_4112_);
                    state = 8;
                    continue;
                }
            },
            8 => {
                v___x_4120_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4120_, 0, v_a_4110_);
                lean_ctor_set(v___x_4120_, 1, v_a_4115_);
                v___x_4121_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4121_, 0, v___x_4120_);
                if v_isShared_4118_ == 0 {
                    lean_ctor_set(v___x_4117_, 0, v___x_4121_);
                    v___x_4123_ = v___x_4117_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4123_;
            }
            10 => {
                return v___x_4127_;
            }
            11 => {
                return v___x_4131_;
            }
            12 => {
                return v___x_4135_;
            }
            13 => {
                if v_isShared_4141_ == 0 {
                    v___x_4143_ = v___x_4140_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
                    v___x_4143_ = v_reuseFailAlloc_4144_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4143_;
            }
            15 => {
                if v_isShared_4150_ == 0 {
                    v___x_4152_ = v___x_4149_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
                    v___x_4152_ = v_reuseFailAlloc_4153_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4152_;
            }
            17 => {
                if v_isShared_4159_ == 0 {
                    v___x_4161_ = v___x_4158_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
                    v___x_4161_ = v_reuseFailAlloc_4162_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4161_;
            }
            19 => {
                if v_isShared_4168_ == 0 {
                    v___x_4170_ = v___x_4167_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
                    v___x_4170_ = v_reuseFailAlloc_4171_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(
    mut v_e_4173_: *mut LeanObject,
    mut v_a_4174_: *mut LeanObject,
    mut v_a_4175_: *mut LeanObject,
    mut v_a_4176_: *mut LeanObject,
    mut v_a_4177_: *mut LeanObject,
    mut v_a_4178_: *mut LeanObject,
    mut v_a_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4180_: *mut LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(
        v_e_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_,
    );
    lean_dec(v_a_4178_);
    lean_dec_ref(v_a_4177_);
    lean_dec(v_a_4176_);
    lean_dec_ref(v_a_4175_);
    lean_dec(v_a_4174_);
    return v_res_4180_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14() -> *mut LeanObject
{
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    v___x_4207_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
    v___x_4208_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4208_, 0, v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(
    mut v_e_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
    mut v_a_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v_arg_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: u8 = 0;
    let mut v_arg_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: u8 = 0;
    let mut v_arg_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4280_: u8 = 0;
    let mut v_a_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut v_a_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4322_: u8 = 0;
    let mut v_a_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4330_: u8 = 0;
    let mut v_a_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_isSharedCheck_4339_: u8 = 0;
    let mut v_a_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4343_: u8 = 0;
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4364_: u8 = 0;
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut v_a_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4386_: u8 = 0;
    let mut v_isSharedCheck_4387_: u8 = 0;
    let mut v_a_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v___x_4401_: u8 = 0;
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_a_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_a_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4452_: u8 = 0;
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_a_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut v_a_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4497_: u8 = 0;
    let mut v_a_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4501_: u8 = 0;
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v_a_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4216_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4209_, v_a_4212_);
                if lean_obj_tag(v___x_4216_) == 0 {
                    v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
                    v_isSharedCheck_4506_ = (!lean_is_exclusive(v___x_4216_)) as u8;
                    if v_isSharedCheck_4506_ == 0 {
                        v___x_4219_ = v___x_4216_;
                        v_isShared_4220_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4217_);
                        lean_dec(v___x_4216_);
                        v___x_4219_ = lean_box(0);
                        v_isShared_4220_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4507_ = lean_ctor_get(v___x_4216_, 0);
                    v_isSharedCheck_4514_ = (!lean_is_exclusive(v___x_4216_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4216_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 56;
                        continue;
                    } else {
                        lean_inc(v_a_4507_);
                        lean_dec(v___x_4216_);
                        v___x_4509_ = lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 56;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4226_ = l_Lean_Expr_cleanupAnnotations(v_a_4217_);
                v___x_4227_ = l_Lean_Expr_isApp(v___x_4226_);
                if v___x_4227_ == 0 {
                    lean_dec_ref(v___x_4226_);
                    state = 2;
                    continue;
                } else {
                    v_arg_4228_ = lean_ctor_get(v___x_4226_, 1);
                    lean_inc_ref(v_arg_4228_);
                    v___x_4229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4226_);
                    v___x_4230_ = l_Lean_Expr_isApp(v___x_4229_);
                    if v___x_4230_ == 0 {
                        lean_dec_ref(v___x_4229_);
                        lean_dec_ref(v_arg_4228_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_4231_ = lean_ctor_get(v___x_4229_, 1);
                        lean_inc_ref(v_arg_4231_);
                        v___x_4232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4229_);
                        v___x_4233_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1;
                        v___x_4234_ = l_Lean_Expr_isConstOf(v___x_4232_, v___x_4233_);
                        if v___x_4234_ == 0 {
                            v___x_4235_ =
                                l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3;
                            v___x_4236_ = l_Lean_Expr_isConstOf(v___x_4232_, v___x_4235_);
                            if v___x_4236_ == 0 {
                                v___x_4237_ = l_Lean_Expr_isApp(v___x_4232_);
                                if v___x_4237_ == 0 {
                                    lean_dec_ref(v___x_4232_);
                                    lean_dec_ref(v_arg_4231_);
                                    lean_dec_ref(v_arg_4228_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_4238_ = lean_ctor_get(v___x_4232_, 1);
                                    lean_inc_ref(v_arg_4238_);
                                    v___x_4239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4232_);
                                    v___x_4240_ = l_Lean_Expr_isApp(v___x_4239_);
                                    if v___x_4240_ == 0 {
                                        lean_dec_ref(v___x_4239_);
                                        lean_dec_ref(v_arg_4238_);
                                        lean_dec_ref(v_arg_4231_);
                                        lean_dec_ref(v_arg_4228_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_4241_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4239_);
                                        v___x_4242_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6;
                                        v___x_4243_ =
                                            l_Lean_Expr_isConstOf(v___x_4241_, v___x_4242_);
                                        if v___x_4243_ == 0 {
                                            v___x_4244_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9;
                                            v___x_4245_ =
                                                l_Lean_Expr_isConstOf(v___x_4241_, v___x_4244_);
                                            if v___x_4245_ == 0 {
                                                v___x_4246_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11;
                                                v___x_4247_ =
                                                    l_Lean_Expr_isConstOf(v___x_4241_, v___x_4246_);
                                                if v___x_4247_ == 0 {
                                                    v___x_4248_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13;
                                                    v___x_4249_ = l_Lean_Expr_isConstOf(
                                                        v___x_4241_,
                                                        v___x_4248_,
                                                    );
                                                    lean_dec_ref(v___x_4241_);
                                                    if v___x_4249_ == 0 {
                                                        lean_dec_ref(v_arg_4238_);
                                                        lean_dec_ref(v_arg_4231_);
                                                        lean_dec_ref(v_arg_4228_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        lean_del_object(v___x_4219_);
                                                        v___x_4250_ = l_Lean_Meta_DefEq_isInstLEInt(
                                                            v_arg_4238_,
                                                            v_a_4211_,
                                                            v_a_4212_,
                                                            v_a_4213_,
                                                            v_a_4214_,
                                                        );
                                                        if lean_obj_tag(v___x_4250_) == 0 {
                                                            v_a_4251_ =
                                                                lean_ctor_get(v___x_4250_, 0);
                                                            v_isSharedCheck_4289_ =
                                                                (!lean_is_exclusive(v___x_4250_))
                                                                    as u8;
                                                            if v_isSharedCheck_4289_ == 0 {
                                                                v___x_4253_ = v___x_4250_;
                                                                v_isShared_4254_ =
                                                                    v_isSharedCheck_4289_;
                                                                state = 4;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4251_);
                                                                lean_dec(v___x_4250_);
                                                                v___x_4253_ = lean_box(0);
                                                                v_isShared_4254_ =
                                                                    v_isSharedCheck_4289_;
                                                                state = 4;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_4231_);
                                                            lean_dec_ref(v_arg_4228_);
                                                            v_a_4290_ =
                                                                lean_ctor_get(v___x_4250_, 0);
                                                            v_isSharedCheck_4297_ =
                                                                (!lean_is_exclusive(v___x_4250_))
                                                                    as u8;
                                                            if v_isSharedCheck_4297_ == 0 {
                                                                v___x_4292_ = v___x_4250_;
                                                                v_isShared_4293_ =
                                                                    v_isSharedCheck_4297_;
                                                                state = 12;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4290_);
                                                                lean_dec(v___x_4250_);
                                                                v___x_4292_ = lean_box(0);
                                                                v_isShared_4293_ =
                                                                    v_isSharedCheck_4297_;
                                                                state = 12;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_4241_);
                                                    lean_del_object(v___x_4219_);
                                                    v___x_4298_ = l_Lean_Meta_DefEq_isInstLTInt(
                                                        v_arg_4238_,
                                                        v_a_4211_,
                                                        v_a_4212_,
                                                        v_a_4213_,
                                                        v_a_4214_,
                                                    );
                                                    if lean_obj_tag(v___x_4298_) == 0 {
                                                        v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
                                                        v_isSharedCheck_4339_ =
                                                            (!lean_is_exclusive(v___x_4298_)) as u8;
                                                        if v_isSharedCheck_4339_ == 0 {
                                                            v___x_4301_ = v___x_4298_;
                                                            v_isShared_4302_ =
                                                                v_isSharedCheck_4339_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4299_);
                                                            lean_dec(v___x_4298_);
                                                            v___x_4301_ = lean_box(0);
                                                            v_isShared_4302_ =
                                                                v_isSharedCheck_4339_;
                                                            state = 14;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_4231_);
                                                        lean_dec_ref(v_arg_4228_);
                                                        v_a_4340_ = lean_ctor_get(v___x_4298_, 0);
                                                        v_isSharedCheck_4347_ =
                                                            (!lean_is_exclusive(v___x_4298_)) as u8;
                                                        if v_isSharedCheck_4347_ == 0 {
                                                            v___x_4342_ = v___x_4298_;
                                                            v_isShared_4343_ =
                                                                v_isSharedCheck_4347_;
                                                            state = 22;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4340_);
                                                            lean_dec(v___x_4298_);
                                                            v___x_4342_ = lean_box(0);
                                                            v_isShared_4343_ =
                                                                v_isSharedCheck_4347_;
                                                            state = 22;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_4241_);
                                                lean_del_object(v___x_4219_);
                                                v___x_4348_ = l_Lean_Meta_DefEq_isInstLEInt(
                                                    v_arg_4238_,
                                                    v_a_4211_,
                                                    v_a_4212_,
                                                    v_a_4213_,
                                                    v_a_4214_,
                                                );
                                                if lean_obj_tag(v___x_4348_) == 0 {
                                                    v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
                                                    v_isSharedCheck_4387_ =
                                                        (!lean_is_exclusive(v___x_4348_)) as u8;
                                                    if v_isSharedCheck_4387_ == 0 {
                                                        v___x_4351_ = v___x_4348_;
                                                        v_isShared_4352_ = v_isSharedCheck_4387_;
                                                        state = 24;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4349_);
                                                        lean_dec(v___x_4348_);
                                                        v___x_4351_ = lean_box(0);
                                                        v_isShared_4352_ = v_isSharedCheck_4387_;
                                                        state = 24;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_4231_);
                                                    lean_dec_ref(v_arg_4228_);
                                                    v_a_4388_ = lean_ctor_get(v___x_4348_, 0);
                                                    v_isSharedCheck_4395_ =
                                                        (!lean_is_exclusive(v___x_4348_)) as u8;
                                                    if v_isSharedCheck_4395_ == 0 {
                                                        v___x_4390_ = v___x_4348_;
                                                        v_isShared_4391_ = v_isSharedCheck_4395_;
                                                        state = 32;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4388_);
                                                        lean_dec(v___x_4348_);
                                                        v___x_4390_ = lean_box(0);
                                                        v_isShared_4391_ = v_isSharedCheck_4395_;
                                                        state = 32;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_4241_);
                                            lean_del_object(v___x_4219_);
                                            v___x_4396_ = l_Lean_Meta_DefEq_isInstLTInt(
                                                v_arg_4238_,
                                                v_a_4211_,
                                                v_a_4212_,
                                                v_a_4213_,
                                                v_a_4214_,
                                            );
                                            if lean_obj_tag(v___x_4396_) == 0 {
                                                v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
                                                v_isSharedCheck_4437_ =
                                                    (!lean_is_exclusive(v___x_4396_)) as u8;
                                                if v_isSharedCheck_4437_ == 0 {
                                                    v___x_4399_ = v___x_4396_;
                                                    v_isShared_4400_ = v_isSharedCheck_4437_;
                                                    state = 34;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4397_);
                                                    lean_dec(v___x_4396_);
                                                    v___x_4399_ = lean_box(0);
                                                    v_isShared_4400_ = v_isSharedCheck_4437_;
                                                    state = 34;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_4231_);
                                                lean_dec_ref(v_arg_4228_);
                                                v_a_4438_ = lean_ctor_get(v___x_4396_, 0);
                                                v_isSharedCheck_4445_ =
                                                    (!lean_is_exclusive(v___x_4396_)) as u8;
                                                if v_isSharedCheck_4445_ == 0 {
                                                    v___x_4440_ = v___x_4396_;
                                                    v_isShared_4441_ = v_isSharedCheck_4445_;
                                                    state = 42;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4438_);
                                                    lean_dec(v___x_4396_);
                                                    v___x_4440_ = lean_box(0);
                                                    v_isShared_4441_ = v_isSharedCheck_4445_;
                                                    state = 42;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_4232_);
                                lean_del_object(v___x_4219_);
                                v___x_4446_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                    v_arg_4231_,
                                    v_a_4210_,
                                    v_a_4211_,
                                    v_a_4212_,
                                    v_a_4213_,
                                    v_a_4214_,
                                );
                                if lean_obj_tag(v___x_4446_) == 0 {
                                    v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
                                    lean_inc(v_a_4447_);
                                    lean_dec_ref_known(v___x_4446_, 1);
                                    v___x_4448_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                        v_arg_4228_,
                                        v_a_4210_,
                                        v_a_4211_,
                                        v_a_4212_,
                                        v_a_4213_,
                                        v_a_4214_,
                                    );
                                    if lean_obj_tag(v___x_4448_) == 0 {
                                        v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
                                        v_isSharedCheck_4458_ =
                                            (!lean_is_exclusive(v___x_4448_)) as u8;
                                        if v_isSharedCheck_4458_ == 0 {
                                            v___x_4451_ = v___x_4448_;
                                            v_isShared_4452_ = v_isSharedCheck_4458_;
                                            state = 44;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4449_);
                                            lean_dec(v___x_4448_);
                                            v___x_4451_ = lean_box(0);
                                            v_isShared_4452_ = v_isSharedCheck_4458_;
                                            state = 44;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_4447_);
                                        v_a_4459_ = lean_ctor_get(v___x_4448_, 0);
                                        v_isSharedCheck_4466_ =
                                            (!lean_is_exclusive(v___x_4448_)) as u8;
                                        if v_isSharedCheck_4466_ == 0 {
                                            v___x_4461_ = v___x_4448_;
                                            v_isShared_4462_ = v_isSharedCheck_4466_;
                                            state = 46;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4459_);
                                            lean_dec(v___x_4448_);
                                            v___x_4461_ = lean_box(0);
                                            v_isShared_4462_ = v_isSharedCheck_4466_;
                                            state = 46;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_arg_4228_);
                                    v_a_4467_ = lean_ctor_get(v___x_4446_, 0);
                                    v_isSharedCheck_4474_ = (!lean_is_exclusive(v___x_4446_)) as u8;
                                    if v_isSharedCheck_4474_ == 0 {
                                        v___x_4469_ = v___x_4446_;
                                        v_isShared_4470_ = v_isSharedCheck_4474_;
                                        state = 48;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4467_);
                                        lean_dec(v___x_4446_);
                                        v___x_4469_ = lean_box(0);
                                        v_isShared_4470_ = v_isSharedCheck_4474_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4232_);
                            lean_del_object(v___x_4219_);
                            v___x_4475_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                v_arg_4231_,
                                v_a_4210_,
                                v_a_4211_,
                                v_a_4212_,
                                v_a_4213_,
                                v_a_4214_,
                            );
                            if lean_obj_tag(v___x_4475_) == 0 {
                                v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
                                lean_inc(v_a_4476_);
                                lean_dec_ref_known(v___x_4475_, 1);
                                v___x_4477_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                                    v_arg_4228_,
                                    v_a_4210_,
                                    v_a_4211_,
                                    v_a_4212_,
                                    v_a_4213_,
                                    v_a_4214_,
                                );
                                if lean_obj_tag(v___x_4477_) == 0 {
                                    v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
                                    v_isSharedCheck_4489_ = (!lean_is_exclusive(v___x_4477_)) as u8;
                                    if v_isSharedCheck_4489_ == 0 {
                                        v___x_4480_ = v___x_4477_;
                                        v_isShared_4481_ = v_isSharedCheck_4489_;
                                        state = 50;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4478_);
                                        lean_dec(v___x_4477_);
                                        v___x_4480_ = lean_box(0);
                                        v_isShared_4481_ = v_isSharedCheck_4489_;
                                        state = 50;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4476_);
                                    v_a_4490_ = lean_ctor_get(v___x_4477_, 0);
                                    v_isSharedCheck_4497_ = (!lean_is_exclusive(v___x_4477_)) as u8;
                                    if v_isSharedCheck_4497_ == 0 {
                                        v___x_4492_ = v___x_4477_;
                                        v_isShared_4493_ = v_isSharedCheck_4497_;
                                        state = 52;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4490_);
                                        lean_dec(v___x_4477_);
                                        v___x_4492_ = lean_box(0);
                                        v_isShared_4493_ = v_isSharedCheck_4497_;
                                        state = 52;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_arg_4228_);
                                v_a_4498_ = lean_ctor_get(v___x_4475_, 0);
                                v_isSharedCheck_4505_ = (!lean_is_exclusive(v___x_4475_)) as u8;
                                if v_isSharedCheck_4505_ == 0 {
                                    v___x_4500_ = v___x_4475_;
                                    v_isShared_4501_ = v_isSharedCheck_4505_;
                                    state = 54;
                                    continue;
                                } else {
                                    lean_inc(v_a_4498_);
                                    lean_dec(v___x_4475_);
                                    v___x_4500_ = lean_box(0);
                                    v_isShared_4501_ = v_isSharedCheck_4505_;
                                    state = 54;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4222_ = lean_box(0);
                if v_isShared_4220_ == 0 {
                    lean_ctor_set(v___x_4219_, 0, v___x_4222_);
                    v___x_4224_ = v___x_4219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
                    v___x_4224_ = v_reuseFailAlloc_4225_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4224_;
            }
            4 => {
                v___x_4255_ = (lean_unbox(v_a_4251_) as u8);
                lean_dec(v_a_4251_);
                if v___x_4255_ == 0 {
                    lean_dec_ref(v_arg_4231_);
                    lean_dec_ref(v_arg_4228_);
                    v___x_4256_ = lean_box(0);
                    if v_isShared_4254_ == 0 {
                        lean_ctor_set(v___x_4253_, 0, v___x_4256_);
                        v___x_4258_ = v___x_4253_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
                        v___x_4258_ = v_reuseFailAlloc_4259_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4253_);
                    v___x_4260_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                        v_arg_4231_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                        v_a_4214_,
                    );
                    if lean_obj_tag(v___x_4260_) == 0 {
                        v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
                        lean_inc(v_a_4261_);
                        lean_dec_ref_known(v___x_4260_, 1);
                        v___x_4262_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                            v_arg_4228_,
                            v_a_4210_,
                            v_a_4211_,
                            v_a_4212_,
                            v_a_4213_,
                            v_a_4214_,
                        );
                        if lean_obj_tag(v___x_4262_) == 0 {
                            v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
                            v_isSharedCheck_4272_ = (!lean_is_exclusive(v___x_4262_)) as u8;
                            if v_isSharedCheck_4272_ == 0 {
                                v___x_4265_ = v___x_4262_;
                                v_isShared_4266_ = v_isSharedCheck_4272_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4263_);
                                lean_dec(v___x_4262_);
                                v___x_4265_ = lean_box(0);
                                v_isShared_4266_ = v_isSharedCheck_4272_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4261_);
                            v_a_4273_ = lean_ctor_get(v___x_4262_, 0);
                            v_isSharedCheck_4280_ = (!lean_is_exclusive(v___x_4262_)) as u8;
                            if v_isSharedCheck_4280_ == 0 {
                                v___x_4275_ = v___x_4262_;
                                v_isShared_4276_ = v_isSharedCheck_4280_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4273_);
                                lean_dec(v___x_4262_);
                                v___x_4275_ = lean_box(0);
                                v_isShared_4276_ = v_isSharedCheck_4280_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_4228_);
                        v_a_4281_ = lean_ctor_get(v___x_4260_, 0);
                        v_isSharedCheck_4288_ = (!lean_is_exclusive(v___x_4260_)) as u8;
                        if v_isSharedCheck_4288_ == 0 {
                            v___x_4283_ = v___x_4260_;
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4281_);
                            lean_dec(v___x_4260_);
                            v___x_4283_ = lean_box(0);
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_4258_;
            }
            6 => {
                v___x_4267_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4267_, 0, v_a_4261_);
                lean_ctor_set(v___x_4267_, 1, v_a_4263_);
                v___x_4268_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4268_, 0, v___x_4267_);
                if v_isShared_4266_ == 0 {
                    lean_ctor_set(v___x_4265_, 0, v___x_4268_);
                    v___x_4270_ = v___x_4265_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
                    v___x_4270_ = v_reuseFailAlloc_4271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4270_;
            }
            8 => {
                if v_isShared_4276_ == 0 {
                    v___x_4278_ = v___x_4275_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
                    v___x_4278_ = v_reuseFailAlloc_4279_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4278_;
            }
            10 => {
                if v_isShared_4284_ == 0 {
                    v___x_4286_ = v___x_4283_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
                    v___x_4286_ = v_reuseFailAlloc_4287_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4286_;
            }
            12 => {
                if v_isShared_4293_ == 0 {
                    v___x_4295_ = v___x_4292_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
                    v___x_4295_ = v_reuseFailAlloc_4296_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4295_;
            }
            14 => {
                v___x_4303_ = (lean_unbox(v_a_4299_) as u8);
                lean_dec(v_a_4299_);
                if v___x_4303_ == 0 {
                    lean_dec_ref(v_arg_4231_);
                    lean_dec_ref(v_arg_4228_);
                    v___x_4304_ = lean_box(0);
                    if v_isShared_4302_ == 0 {
                        lean_ctor_set(v___x_4301_, 0, v___x_4304_);
                        v___x_4306_ = v___x_4301_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4301_);
                    v___x_4308_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                        v_arg_4231_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                        v_a_4214_,
                    );
                    if lean_obj_tag(v___x_4308_) == 0 {
                        v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
                        lean_inc(v_a_4309_);
                        lean_dec_ref_known(v___x_4308_, 1);
                        v___x_4310_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                            v_arg_4228_,
                            v_a_4210_,
                            v_a_4211_,
                            v_a_4212_,
                            v_a_4213_,
                            v_a_4214_,
                        );
                        if lean_obj_tag(v___x_4310_) == 0 {
                            v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
                            v_isSharedCheck_4322_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                            if v_isSharedCheck_4322_ == 0 {
                                v___x_4313_ = v___x_4310_;
                                v_isShared_4314_ = v_isSharedCheck_4322_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_4311_);
                                lean_dec(v___x_4310_);
                                v___x_4313_ = lean_box(0);
                                v_isShared_4314_ = v_isSharedCheck_4322_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4309_);
                            v_a_4323_ = lean_ctor_get(v___x_4310_, 0);
                            v_isSharedCheck_4330_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                            if v_isSharedCheck_4330_ == 0 {
                                v___x_4325_ = v___x_4310_;
                                v_isShared_4326_ = v_isSharedCheck_4330_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4323_);
                                lean_dec(v___x_4310_);
                                v___x_4325_ = lean_box(0);
                                v_isShared_4326_ = v_isSharedCheck_4330_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_4228_);
                        v_a_4331_ = lean_ctor_get(v___x_4308_, 0);
                        v_isSharedCheck_4338_ = (!lean_is_exclusive(v___x_4308_)) as u8;
                        if v_isSharedCheck_4338_ == 0 {
                            v___x_4333_ = v___x_4308_;
                            v_isShared_4334_ = v_isSharedCheck_4338_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_4331_);
                            lean_dec(v___x_4308_);
                            v___x_4333_ = lean_box(0);
                            v_isShared_4334_ = v_isSharedCheck_4338_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            15 => {
                return v___x_4306_;
            }
            16 => {
                v___x_4315_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14,
                );
                v___x_4316_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4316_, 0, v_a_4309_);
                lean_ctor_set(v___x_4316_, 1, v___x_4315_);
                v___x_4317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4317_, 0, v___x_4316_);
                lean_ctor_set(v___x_4317_, 1, v_a_4311_);
                v___x_4318_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4318_, 0, v___x_4317_);
                if v_isShared_4314_ == 0 {
                    lean_ctor_set(v___x_4313_, 0, v___x_4318_);
                    v___x_4320_ = v___x_4313_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
                    v___x_4320_ = v_reuseFailAlloc_4321_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4320_;
            }
            18 => {
                if v_isShared_4326_ == 0 {
                    v___x_4328_ = v___x_4325_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
                    v___x_4328_ = v_reuseFailAlloc_4329_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4328_;
            }
            20 => {
                if v_isShared_4334_ == 0 {
                    v___x_4336_ = v___x_4333_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4336_;
            }
            22 => {
                if v_isShared_4343_ == 0 {
                    v___x_4345_ = v___x_4342_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
                    v___x_4345_ = v_reuseFailAlloc_4346_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4345_;
            }
            24 => {
                v___x_4353_ = (lean_unbox(v_a_4349_) as u8);
                lean_dec(v_a_4349_);
                if v___x_4353_ == 0 {
                    lean_dec_ref(v_arg_4231_);
                    lean_dec_ref(v_arg_4228_);
                    v___x_4354_ = lean_box(0);
                    if v_isShared_4352_ == 0 {
                        lean_ctor_set(v___x_4351_, 0, v___x_4354_);
                        v___x_4356_ = v___x_4351_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
                        v___x_4356_ = v_reuseFailAlloc_4357_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4351_);
                    v___x_4358_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                        v_arg_4228_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                        v_a_4214_,
                    );
                    if lean_obj_tag(v___x_4358_) == 0 {
                        v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
                        lean_inc(v_a_4359_);
                        lean_dec_ref_known(v___x_4358_, 1);
                        v___x_4360_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                            v_arg_4231_,
                            v_a_4210_,
                            v_a_4211_,
                            v_a_4212_,
                            v_a_4213_,
                            v_a_4214_,
                        );
                        if lean_obj_tag(v___x_4360_) == 0 {
                            v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
                            v_isSharedCheck_4370_ = (!lean_is_exclusive(v___x_4360_)) as u8;
                            if v_isSharedCheck_4370_ == 0 {
                                v___x_4363_ = v___x_4360_;
                                v_isShared_4364_ = v_isSharedCheck_4370_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_4361_);
                                lean_dec(v___x_4360_);
                                v___x_4363_ = lean_box(0);
                                v_isShared_4364_ = v_isSharedCheck_4370_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4359_);
                            v_a_4371_ = lean_ctor_get(v___x_4360_, 0);
                            v_isSharedCheck_4378_ = (!lean_is_exclusive(v___x_4360_)) as u8;
                            if v_isSharedCheck_4378_ == 0 {
                                v___x_4373_ = v___x_4360_;
                                v_isShared_4374_ = v_isSharedCheck_4378_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_4371_);
                                lean_dec(v___x_4360_);
                                v___x_4373_ = lean_box(0);
                                v_isShared_4374_ = v_isSharedCheck_4378_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_4231_);
                        v_a_4379_ = lean_ctor_get(v___x_4358_, 0);
                        v_isSharedCheck_4386_ = (!lean_is_exclusive(v___x_4358_)) as u8;
                        if v_isSharedCheck_4386_ == 0 {
                            v___x_4381_ = v___x_4358_;
                            v_isShared_4382_ = v_isSharedCheck_4386_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_4379_);
                            lean_dec(v___x_4358_);
                            v___x_4381_ = lean_box(0);
                            v_isShared_4382_ = v_isSharedCheck_4386_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_4356_;
            }
            26 => {
                v___x_4365_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4365_, 0, v_a_4359_);
                lean_ctor_set(v___x_4365_, 1, v_a_4361_);
                v___x_4366_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4366_, 0, v___x_4365_);
                if v_isShared_4364_ == 0 {
                    lean_ctor_set(v___x_4363_, 0, v___x_4366_);
                    v___x_4368_ = v___x_4363_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
                    v___x_4368_ = v_reuseFailAlloc_4369_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4368_;
            }
            28 => {
                if v_isShared_4374_ == 0 {
                    v___x_4376_ = v___x_4373_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
                    v___x_4376_ = v_reuseFailAlloc_4377_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4376_;
            }
            30 => {
                if v_isShared_4382_ == 0 {
                    v___x_4384_ = v___x_4381_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
                    v___x_4384_ = v_reuseFailAlloc_4385_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4384_;
            }
            32 => {
                if v_isShared_4391_ == 0 {
                    v___x_4393_ = v___x_4390_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4394_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4393_;
            }
            34 => {
                v___x_4401_ = (lean_unbox(v_a_4397_) as u8);
                lean_dec(v_a_4397_);
                if v___x_4401_ == 0 {
                    lean_dec_ref(v_arg_4231_);
                    lean_dec_ref(v_arg_4228_);
                    v___x_4402_ = lean_box(0);
                    if v_isShared_4400_ == 0 {
                        lean_ctor_set(v___x_4399_, 0, v___x_4402_);
                        v___x_4404_ = v___x_4399_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
                        v___x_4404_ = v_reuseFailAlloc_4405_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4399_);
                    v___x_4406_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                        v_arg_4228_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                        v_a_4214_,
                    );
                    if lean_obj_tag(v___x_4406_) == 0 {
                        v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
                        lean_inc(v_a_4407_);
                        lean_dec_ref_known(v___x_4406_, 1);
                        v___x_4408_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                            v_arg_4231_,
                            v_a_4210_,
                            v_a_4211_,
                            v_a_4212_,
                            v_a_4213_,
                            v_a_4214_,
                        );
                        if lean_obj_tag(v___x_4408_) == 0 {
                            v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
                            v_isSharedCheck_4420_ = (!lean_is_exclusive(v___x_4408_)) as u8;
                            if v_isSharedCheck_4420_ == 0 {
                                v___x_4411_ = v___x_4408_;
                                v_isShared_4412_ = v_isSharedCheck_4420_;
                                state = 36;
                                continue;
                            } else {
                                lean_inc(v_a_4409_);
                                lean_dec(v___x_4408_);
                                v___x_4411_ = lean_box(0);
                                v_isShared_4412_ = v_isSharedCheck_4420_;
                                state = 36;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4407_);
                            v_a_4421_ = lean_ctor_get(v___x_4408_, 0);
                            v_isSharedCheck_4428_ = (!lean_is_exclusive(v___x_4408_)) as u8;
                            if v_isSharedCheck_4428_ == 0 {
                                v___x_4423_ = v___x_4408_;
                                v_isShared_4424_ = v_isSharedCheck_4428_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_4421_);
                                lean_dec(v___x_4408_);
                                v___x_4423_ = lean_box(0);
                                v_isShared_4424_ = v_isSharedCheck_4428_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_4231_);
                        v_a_4429_ = lean_ctor_get(v___x_4406_, 0);
                        v_isSharedCheck_4436_ = (!lean_is_exclusive(v___x_4406_)) as u8;
                        if v_isSharedCheck_4436_ == 0 {
                            v___x_4431_ = v___x_4406_;
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 40;
                            continue;
                        } else {
                            lean_inc(v_a_4429_);
                            lean_dec(v___x_4406_);
                            v___x_4431_ = lean_box(0);
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            35 => {
                return v___x_4404_;
            }
            36 => {
                v___x_4413_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14,
                );
                v___x_4414_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4414_, 0, v_a_4407_);
                lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4415_, 0, v___x_4414_);
                lean_ctor_set(v___x_4415_, 1, v_a_4409_);
                v___x_4416_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4416_, 0, v___x_4415_);
                if v_isShared_4412_ == 0 {
                    lean_ctor_set(v___x_4411_, 0, v___x_4416_);
                    v___x_4418_ = v___x_4411_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
                    v___x_4418_ = v_reuseFailAlloc_4419_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4418_;
            }
            38 => {
                if v_isShared_4424_ == 0 {
                    v___x_4426_ = v___x_4423_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
                    v___x_4426_ = v_reuseFailAlloc_4427_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4426_;
            }
            40 => {
                if v_isShared_4432_ == 0 {
                    v___x_4434_ = v___x_4431_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
                    v___x_4434_ = v_reuseFailAlloc_4435_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4434_;
            }
            42 => {
                if v_isShared_4441_ == 0 {
                    v___x_4443_ = v___x_4440_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
                    v___x_4443_ = v_reuseFailAlloc_4444_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4443_;
            }
            44 => {
                v___x_4453_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4453_, 0, v_a_4447_);
                lean_ctor_set(v___x_4453_, 1, v_a_4449_);
                v___x_4454_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4454_, 0, v___x_4453_);
                if v_isShared_4452_ == 0 {
                    lean_ctor_set(v___x_4451_, 0, v___x_4454_);
                    v___x_4456_ = v___x_4451_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4456_;
            }
            46 => {
                if v_isShared_4462_ == 0 {
                    v___x_4464_ = v___x_4461_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4464_;
            }
            48 => {
                if v_isShared_4470_ == 0 {
                    v___x_4472_ = v___x_4469_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4472_;
            }
            50 => {
                v___x_4482_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14,
                );
                v___x_4483_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4483_, 0, v_a_4476_);
                lean_ctor_set(v___x_4483_, 1, v___x_4482_);
                v___x_4484_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4484_, 0, v___x_4483_);
                lean_ctor_set(v___x_4484_, 1, v_a_4478_);
                v___x_4485_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4485_, 0, v___x_4484_);
                if v_isShared_4481_ == 0 {
                    lean_ctor_set(v___x_4480_, 0, v___x_4485_);
                    v___x_4487_ = v___x_4480_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_4487_;
            }
            52 => {
                if v_isShared_4493_ == 0 {
                    v___x_4495_ = v___x_4492_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
                    v___x_4495_ = v_reuseFailAlloc_4496_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4495_;
            }
            54 => {
                if v_isShared_4501_ == 0 {
                    v___x_4503_ = v___x_4500_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
                    v___x_4503_ = v_reuseFailAlloc_4504_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_4503_;
            }
            56 => {
                if v_isShared_4510_ == 0 {
                    v___x_4512_ = v___x_4509_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(
    mut v_e_4515_: *mut LeanObject,
    mut v_a_4516_: *mut LeanObject,
    mut v_a_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4522_: *mut LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(
        v_e_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_,
    );
    lean_dec(v_a_4520_);
    lean_dec_ref(v_a_4519_);
    lean_dec(v_a_4518_);
    lean_dec_ref(v_a_4517_);
    lean_dec(v_a_4516_);
    return v_res_4522_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(
    mut v_e_4528_: *mut LeanObject,
    mut v_a_4529_: *mut LeanObject,
    mut v_a_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: u8 = 0;
    let mut v_arg_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v_arg_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: u8 = 0;
    let mut v_arg_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v_val_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4590_: u8 = 0;
    let mut v_a_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_isSharedCheck_4599_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_a_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v_a_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut v_a_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4535_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4528_, v_a_4531_);
                if lean_obj_tag(v___x_4535_) == 0 {
                    v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
                    v_isSharedCheck_4622_ = (!lean_is_exclusive(v___x_4535_)) as u8;
                    if v_isSharedCheck_4622_ == 0 {
                        v___x_4538_ = v___x_4535_;
                        v_isShared_4539_ = v_isSharedCheck_4622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4536_);
                        lean_dec(v___x_4535_);
                        v___x_4538_ = lean_box(0);
                        v_isShared_4539_ = v_isSharedCheck_4622_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4623_ = lean_ctor_get(v___x_4535_, 0);
                    v_isSharedCheck_4630_ = (!lean_is_exclusive(v___x_4535_)) as u8;
                    if v_isSharedCheck_4630_ == 0 {
                        v___x_4625_ = v___x_4535_;
                        v_isShared_4626_ = v_isSharedCheck_4630_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_4623_);
                        lean_dec(v___x_4535_);
                        v___x_4625_ = lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4630_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4545_ = l_Lean_Expr_cleanupAnnotations(v_a_4536_);
                v___x_4546_ = l_Lean_Expr_isApp(v___x_4545_);
                if v___x_4546_ == 0 {
                    lean_dec_ref(v___x_4545_);
                    state = 2;
                    continue;
                } else {
                    v_arg_4547_ = lean_ctor_get(v___x_4545_, 1);
                    lean_inc_ref(v_arg_4547_);
                    v___x_4548_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4545_);
                    v___x_4549_ = l_Lean_Expr_isApp(v___x_4548_);
                    if v___x_4549_ == 0 {
                        lean_dec_ref(v___x_4548_);
                        lean_dec_ref(v_arg_4547_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_4550_ = lean_ctor_get(v___x_4548_, 1);
                        lean_inc_ref(v_arg_4550_);
                        v___x_4551_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4548_);
                        v___x_4552_ = l_Lean_Expr_isApp(v___x_4551_);
                        if v___x_4552_ == 0 {
                            lean_dec_ref(v___x_4551_);
                            lean_dec_ref(v_arg_4550_);
                            lean_dec_ref(v_arg_4547_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_4553_ = lean_ctor_get(v___x_4551_, 1);
                            lean_inc_ref(v_arg_4553_);
                            v___x_4554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4551_);
                            v___x_4555_ = l_Lean_Expr_isApp(v___x_4554_);
                            if v___x_4555_ == 0 {
                                lean_dec_ref(v___x_4554_);
                                lean_dec_ref(v_arg_4553_);
                                lean_dec_ref(v_arg_4550_);
                                lean_dec_ref(v_arg_4547_);
                                state = 2;
                                continue;
                            } else {
                                v___x_4556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4554_);
                                v___x_4557_ =
                                    l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2;
                                v___x_4558_ = l_Lean_Expr_isConstOf(v___x_4556_, v___x_4557_);
                                lean_dec_ref(v___x_4556_);
                                if v___x_4558_ == 0 {
                                    lean_dec_ref(v_arg_4553_);
                                    lean_dec_ref(v_arg_4550_);
                                    lean_dec_ref(v_arg_4547_);
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_4538_);
                                    v___x_4559_ = l_Lean_Meta_DefEq_isInstDvdInt(
                                        v_arg_4553_,
                                        v_a_4530_,
                                        v_a_4531_,
                                        v_a_4532_,
                                        v_a_4533_,
                                    );
                                    if lean_obj_tag(v___x_4559_) == 0 {
                                        v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
                                        v_isSharedCheck_4613_ =
                                            (!lean_is_exclusive(v___x_4559_)) as u8;
                                        if v_isSharedCheck_4613_ == 0 {
                                            v___x_4562_ = v___x_4559_;
                                            v_isShared_4563_ = v_isSharedCheck_4613_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4560_);
                                            lean_dec(v___x_4559_);
                                            v___x_4562_ = lean_box(0);
                                            v_isShared_4563_ = v_isSharedCheck_4613_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_4550_);
                                        lean_dec_ref(v_arg_4547_);
                                        v_a_4614_ = lean_ctor_get(v___x_4559_, 0);
                                        v_isSharedCheck_4621_ =
                                            (!lean_is_exclusive(v___x_4559_)) as u8;
                                        if v_isSharedCheck_4621_ == 0 {
                                            v___x_4616_ = v___x_4559_;
                                            v_isShared_4617_ = v_isSharedCheck_4621_;
                                            state = 16;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4614_);
                                            lean_dec(v___x_4559_);
                                            v___x_4616_ = lean_box(0);
                                            v_isShared_4617_ = v_isSharedCheck_4621_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4541_ = lean_box(0);
                if v_isShared_4539_ == 0 {
                    lean_ctor_set(v___x_4538_, 0, v___x_4541_);
                    v___x_4543_ = v___x_4538_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4543_;
            }
            4 => {
                v___x_4564_ = (lean_unbox(v_a_4560_) as u8);
                lean_dec(v_a_4560_);
                if v___x_4564_ == 0 {
                    lean_dec_ref(v_arg_4550_);
                    lean_dec_ref(v_arg_4547_);
                    v___x_4565_ = lean_box(0);
                    if v_isShared_4563_ == 0 {
                        lean_ctor_set(v___x_4562_, 0, v___x_4565_);
                        v___x_4567_ = v___x_4562_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
                        v___x_4567_ = v_reuseFailAlloc_4568_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4562_);
                    v___x_4569_ = l_Lean_Meta_getIntValue_x3f(
                        v_arg_4550_,
                        v_a_4530_,
                        v_a_4531_,
                        v_a_4532_,
                        v_a_4533_,
                    );
                    if lean_obj_tag(v___x_4569_) == 0 {
                        v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
                        v_isSharedCheck_4604_ = (!lean_is_exclusive(v___x_4569_)) as u8;
                        if v_isSharedCheck_4604_ == 0 {
                            v___x_4572_ = v___x_4569_;
                            v_isShared_4573_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4570_);
                            lean_dec(v___x_4569_);
                            v___x_4572_ = lean_box(0);
                            v_isShared_4573_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_4547_);
                        v_a_4605_ = lean_ctor_get(v___x_4569_, 0);
                        v_isSharedCheck_4612_ = (!lean_is_exclusive(v___x_4569_)) as u8;
                        if v_isSharedCheck_4612_ == 0 {
                            v___x_4607_ = v___x_4569_;
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4605_);
                            lean_dec(v___x_4569_);
                            v___x_4607_ = lean_box(0);
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_4567_;
            }
            6 => {
                if lean_obj_tag(v_a_4570_) == 1 {
                    lean_del_object(v___x_4572_);
                    v_val_4574_ = lean_ctor_get(v_a_4570_, 0);
                    v_isSharedCheck_4599_ = (!lean_is_exclusive(v_a_4570_)) as u8;
                    if v_isSharedCheck_4599_ == 0 {
                        v___x_4576_ = v_a_4570_;
                        v_isShared_4577_ = v_isSharedCheck_4599_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_4574_);
                        lean_dec(v_a_4570_);
                        v___x_4576_ = lean_box(0);
                        v_isShared_4577_ = v_isSharedCheck_4599_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4570_);
                    lean_dec_ref(v_arg_4547_);
                    v___x_4600_ = lean_box(0);
                    if v_isShared_4573_ == 0 {
                        lean_ctor_set(v___x_4572_, 0, v___x_4600_);
                        v___x_4602_ = v___x_4572_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
                        v___x_4602_ = v_reuseFailAlloc_4603_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4578_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(
                    v_arg_4547_,
                    v_a_4529_,
                    v_a_4530_,
                    v_a_4531_,
                    v_a_4532_,
                    v_a_4533_,
                );
                if lean_obj_tag(v___x_4578_) == 0 {
                    v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4590_ = (!lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4590_ == 0 {
                        v___x_4581_ = v___x_4578_;
                        v_isShared_4582_ = v_isSharedCheck_4590_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4579_);
                        lean_dec(v___x_4578_);
                        v___x_4581_ = lean_box(0);
                        v_isShared_4582_ = v_isSharedCheck_4590_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4576_);
                    lean_dec(v_val_4574_);
                    v_a_4591_ = lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4598_ = (!lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4598_ == 0 {
                        v___x_4593_ = v___x_4578_;
                        v_isShared_4594_ = v_isSharedCheck_4598_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4591_);
                        lean_dec(v___x_4578_);
                        v___x_4593_ = lean_box(0);
                        v_isShared_4594_ = v_isSharedCheck_4598_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4583_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4583_, 0, v_val_4574_);
                lean_ctor_set(v___x_4583_, 1, v_a_4579_);
                if v_isShared_4577_ == 0 {
                    lean_ctor_set(v___x_4576_, 0, v___x_4583_);
                    v___x_4585_ = v___x_4576_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4583_);
                    v___x_4585_ = v_reuseFailAlloc_4589_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4582_ == 0 {
                    lean_ctor_set(v___x_4581_, 0, v___x_4585_);
                    v___x_4587_ = v___x_4581_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
                    v___x_4587_ = v_reuseFailAlloc_4588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4587_;
            }
            11 => {
                if v_isShared_4594_ == 0 {
                    v___x_4596_ = v___x_4593_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
                    v___x_4596_ = v_reuseFailAlloc_4597_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4596_;
            }
            13 => {
                return v___x_4602_;
            }
            14 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4610_;
            }
            16 => {
                if v_isShared_4617_ == 0 {
                    v___x_4619_ = v___x_4616_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4619_;
            }
            18 => {
                if v_isShared_4626_ == 0 {
                    v___x_4628_ = v___x_4625_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
                    v___x_4628_ = v_reuseFailAlloc_4629_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(
    mut v_e_4631_: *mut LeanObject,
    mut v_a_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4638_: *mut LeanObject = core::ptr::null_mut();
    v_res_4638_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(
        v_e_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_,
    );
    lean_dec(v_a_4636_);
    lean_dec_ref(v_a_4635_);
    lean_dec(v_a_4634_);
    lean_dec_ref(v_a_4633_);
    lean_dec(v_a_4632_);
    return v_res_4638_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0() -> *mut LeanObject
{
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    v___x_4639_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4639_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1() -> *mut LeanObject
{
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    v___x_4640_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0,
    );
    v___x_4641_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4641_, 0, v___x_4640_);
    return v___x_4641_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3() -> *mut LeanObject
{
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2;
    v___x_4645_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1,
    );
    v___x_4646_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4646_, 0, v___x_4645_);
    lean_ctor_set(v___x_4646_, 1, v___x_4644_);
    return v___x_4646_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
    mut v_x_4647_: *mut LeanObject,
    mut v_a_4648_: *mut LeanObject,
    mut v_a_4649_: *mut LeanObject,
    mut v_a_4650_: *mut LeanObject,
    mut v_a_4651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4659_: u8 = 0;
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_unused_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_a_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4653_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3,
                );
                v___x_4654_ = lean_st_mk_ref(v___x_4653_);
                lean_inc(v_a_4651_);
                lean_inc_ref(v_a_4650_);
                lean_inc(v_a_4649_);
                lean_inc_ref(v_a_4648_);
                lean_inc(v___x_4654_);
                v___x_4655_ = lean_apply_6(
                    v_x_4647_,
                    v___x_4654_,
                    v_a_4648_,
                    v_a_4649_,
                    v_a_4650_,
                    v_a_4651_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4655_) == 0 {
                    v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
                    v_isSharedCheck_4673_ = (!lean_is_exclusive(v___x_4655_)) as u8;
                    if v_isSharedCheck_4673_ == 0 {
                        v___x_4658_ = v___x_4655_;
                        v_isShared_4659_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4656_);
                        lean_dec(v___x_4655_);
                        v___x_4658_ = lean_box(0);
                        v_isShared_4659_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4654_);
                    v_a_4674_ = lean_ctor_get(v___x_4655_, 0);
                    v_isSharedCheck_4681_ = (!lean_is_exclusive(v___x_4655_)) as u8;
                    if v_isSharedCheck_4681_ == 0 {
                        v___x_4676_ = v___x_4655_;
                        v_isShared_4677_ = v_isSharedCheck_4681_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4674_);
                        lean_dec(v___x_4655_);
                        v___x_4676_ = lean_box(0);
                        v_isShared_4677_ = v_isSharedCheck_4681_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4660_ = lean_st_ref_get(v___x_4654_);
                lean_dec(v___x_4654_);
                v_vars_4661_ = lean_ctor_get(v___x_4660_, 1);
                v_isSharedCheck_4671_ = (!lean_is_exclusive(v___x_4660_)) as u8;
                if v_isSharedCheck_4671_ == 0 {
                    v_unused_4672_ = lean_ctor_get(v___x_4660_, 0);
                    lean_dec(v_unused_4672_);
                    v___x_4663_ = v___x_4660_;
                    v_isShared_4664_ = v_isSharedCheck_4671_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_vars_4661_);
                    lean_dec(v___x_4660_);
                    v___x_4663_ = lean_box(0);
                    v_isShared_4664_ = v_isSharedCheck_4671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4664_ == 0 {
                    lean_ctor_set(v___x_4663_, 0, v_a_4656_);
                    v___x_4666_ = v___x_4663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4656_);
                    lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_vars_4661_);
                    v___x_4666_ = v_reuseFailAlloc_4670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4659_ == 0 {
                    lean_ctor_set(v___x_4658_, 0, v___x_4666_);
                    v___x_4668_ = v___x_4658_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4666_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4668_;
            }
            5 => {
                if v_isShared_4677_ == 0 {
                    v___x_4679_ = v___x_4676_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
                    v___x_4679_ = v_reuseFailAlloc_4680_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(
    mut v_x_4682_: *mut LeanObject,
    mut v_a_4683_: *mut LeanObject,
    mut v_a_4684_: *mut LeanObject,
    mut v_a_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
    mut v_a_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4688_: *mut LeanObject = core::ptr::null_mut();
    v_res_4688_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
        v_x_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_,
    );
    lean_dec(v_a_4686_);
    lean_dec_ref(v_a_4685_);
    lean_dec(v_a_4684_);
    lean_dec_ref(v_a_4683_);
    return v_res_4688_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_run(
    mut v_00_u03b1_4689_: *mut LeanObject,
    mut v_x_4690_: *mut LeanObject,
    mut v_a_4691_: *mut LeanObject,
    mut v_a_4692_: *mut LeanObject,
    mut v_a_4693_: *mut LeanObject,
    mut v_a_4694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
        v_x_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_,
    );
    return v___x_4696_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(
    mut v_00_u03b1_4697_: *mut LeanObject,
    mut v_x_4698_: *mut LeanObject,
    mut v_a_4699_: *mut LeanObject,
    mut v_a_4700_: *mut LeanObject,
    mut v_a_4701_: *mut LeanObject,
    mut v_a_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4704_: *mut LeanObject = core::ptr::null_mut();
    v_res_4704_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(
        v_00_u03b1_4697_,
        v_x_4698_,
        v_a_4699_,
        v_a_4700_,
        v_a_4701_,
        v_a_4702_,
    );
    lean_dec(v_a_4702_);
    lean_dec_ref(v_a_4701_);
    lean_dec(v_a_4700_);
    lean_dec_ref(v_a_4699_);
    return v_res_4704_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toLinearExpr(
    mut v_e_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
    mut v_a_4708_: *mut LeanObject,
    mut v_a_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: u8 = 0;
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4735_: u8 = 0;
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_unused_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4711_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_4711_, 0, v_e_4705_);
                v___x_4712_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
                    v___x_4711_,
                    v_a_4706_,
                    v_a_4707_,
                    v_a_4708_,
                    v_a_4709_,
                );
                if lean_obj_tag(v___x_4712_) == 0 {
                    v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
                    lean_inc(v_a_4713_);
                    v_fst_4714_ = lean_ctor_get(v_a_4713_, 0);
                    lean_inc(v_fst_4714_);
                    v_snd_4715_ = lean_ctor_get(v_a_4713_, 1);
                    lean_inc(v_snd_4715_);
                    lean_dec(v_a_4713_);
                    v___x_4716_ = lean_array_get_size(v_snd_4715_);
                    v___x_4717_ = lean_unsigned_to_nat(1);
                    v___x_4718_ = lean_nat_dec_eq(v___x_4716_, v___x_4717_);
                    if v___x_4718_ == 0 {
                        v_isSharedCheck_4736_ = (!lean_is_exclusive(v___x_4712_)) as u8;
                        if v_isSharedCheck_4736_ == 0 {
                            v_unused_4737_ = lean_ctor_get(v___x_4712_, 0);
                            lean_dec(v_unused_4737_);
                            v___x_4720_ = v___x_4712_;
                            v_isShared_4721_ = v_isSharedCheck_4736_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4712_);
                            v___x_4720_ = lean_box(0);
                            v_isShared_4721_ = v_isSharedCheck_4736_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4715_);
                        lean_dec(v_fst_4714_);
                        return v___x_4712_;
                    }
                } else {
                    return v___x_4712_;
                }
            }
            1 => {
                v___x_4722_ = l_Lean_sortExprs(v_snd_4715_, v___x_4718_);
                lean_dec(v_snd_4715_);
                v_fst_4723_ = lean_ctor_get(v___x_4722_, 0);
                v_snd_4724_ = lean_ctor_get(v___x_4722_, 1);
                v_isSharedCheck_4735_ = (!lean_is_exclusive(v___x_4722_)) as u8;
                if v_isSharedCheck_4735_ == 0 {
                    v___x_4726_ = v___x_4722_;
                    v_isShared_4727_ = v_isSharedCheck_4735_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4724_);
                    lean_inc(v_fst_4723_);
                    lean_dec(v___x_4722_);
                    v___x_4726_ = lean_box(0);
                    v_isShared_4727_ = v_isSharedCheck_4735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4728_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4724_, v_fst_4714_);
                lean_dec(v_snd_4724_);
                if v_isShared_4727_ == 0 {
                    lean_ctor_set(v___x_4726_, 1, v_fst_4723_);
                    lean_ctor_set(v___x_4726_, 0, v___x_4728_);
                    v___x_4730_ = v___x_4726_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_fst_4723_);
                    v___x_4730_ = v_reuseFailAlloc_4734_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4721_ == 0 {
                    lean_ctor_set(v___x_4720_, 0, v___x_4730_);
                    v___x_4732_ = v___x_4720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
                    v___x_4732_ = v_reuseFailAlloc_4733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(
    mut v_e_4738_: *mut LeanObject,
    mut v_a_4739_: *mut LeanObject,
    mut v_a_4740_: *mut LeanObject,
    mut v_a_4741_: *mut LeanObject,
    mut v_a_4742_: *mut LeanObject,
    mut v_a_4743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4744_: *mut LeanObject = core::ptr::null_mut();
    v_res_4744_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(
        v_e_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_,
    );
    lean_dec(v_a_4742_);
    lean_dec_ref(v_a_4741_);
    lean_dec(v_a_4740_);
    lean_dec_ref(v_a_4739_);
    return v_res_4744_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(
    mut v_e_4745_: *mut LeanObject,
    mut v_k_4746_: *mut LeanObject,
    mut v_a_4747_: *mut LeanObject,
    mut v_a_4748_: *mut LeanObject,
    mut v_a_4749_: *mut LeanObject,
    mut v_a_4750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4757_: u8 = 0;
    let mut v_fst_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v_snd_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4766_: u8 = 0;
    let mut v_fst_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4771_: u8 = 0;
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4795_: u8 = 0;
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_unused_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4811_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut v_a_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4820_: u8 = 0;
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4752_ = lean_apply_1(v_k_4746_, v_e_4745_);
                v___x_4753_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
                    v___x_4752_,
                    v_a_4747_,
                    v_a_4748_,
                    v_a_4749_,
                    v_a_4750_,
                );
                if lean_obj_tag(v___x_4753_) == 0 {
                    v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
                    v_isSharedCheck_4816_ = (!lean_is_exclusive(v___x_4753_)) as u8;
                    if v_isSharedCheck_4816_ == 0 {
                        v___x_4756_ = v___x_4753_;
                        v_isShared_4757_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4754_);
                        lean_dec(v___x_4753_);
                        v___x_4756_ = lean_box(0);
                        v_isShared_4757_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4817_ = lean_ctor_get(v___x_4753_, 0);
                    v_isSharedCheck_4824_ = (!lean_is_exclusive(v___x_4753_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v___x_4819_ = v___x_4753_;
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4817_);
                        lean_dec(v___x_4753_);
                        v___x_4819_ = lean_box(0);
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4758_ = lean_ctor_get(v_a_4754_, 0);
                lean_inc(v_fst_4758_);
                if lean_obj_tag(v_fst_4758_) == 1 {
                    v_val_4759_ = lean_ctor_get(v_fst_4758_, 0);
                    v_isSharedCheck_4811_ = (!lean_is_exclusive(v_fst_4758_)) as u8;
                    if v_isSharedCheck_4811_ == 0 {
                        v___x_4761_ = v_fst_4758_;
                        v_isShared_4762_ = v_isSharedCheck_4811_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4759_);
                        lean_dec(v_fst_4758_);
                        v___x_4761_ = lean_box(0);
                        v_isShared_4762_ = v_isSharedCheck_4811_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_4758_);
                    lean_dec(v_a_4754_);
                    v___x_4812_ = lean_box(0);
                    if v_isShared_4757_ == 0 {
                        lean_ctor_set(v___x_4756_, 0, v___x_4812_);
                        v___x_4814_ = v___x_4756_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
                        v___x_4814_ = v_reuseFailAlloc_4815_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_4763_ = lean_ctor_get(v_a_4754_, 1);
                v_isSharedCheck_4809_ = (!lean_is_exclusive(v_a_4754_)) as u8;
                if v_isSharedCheck_4809_ == 0 {
                    v_unused_4810_ = lean_ctor_get(v_a_4754_, 0);
                    lean_dec(v_unused_4810_);
                    v___x_4765_ = v_a_4754_;
                    v_isShared_4766_ = v_isSharedCheck_4809_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4763_);
                    lean_dec(v_a_4754_);
                    v___x_4765_ = lean_box(0);
                    v_isShared_4766_ = v_isSharedCheck_4809_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4767_ = lean_ctor_get(v_val_4759_, 0);
                v_snd_4768_ = lean_ctor_get(v_val_4759_, 1);
                v_isSharedCheck_4808_ = (!lean_is_exclusive(v_val_4759_)) as u8;
                if v_isSharedCheck_4808_ == 0 {
                    v___x_4770_ = v_val_4759_;
                    v_isShared_4771_ = v_isSharedCheck_4808_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_4768_);
                    lean_inc(v_fst_4767_);
                    lean_dec(v_val_4759_);
                    v___x_4770_ = lean_box(0);
                    v_isShared_4771_ = v_isSharedCheck_4808_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4772_ = lean_array_get_size(v_snd_4763_);
                v___x_4773_ = lean_unsigned_to_nat(1);
                v___x_4774_ = lean_nat_dec_le(v___x_4772_, v___x_4773_);
                if v___x_4774_ == 0 {
                    lean_del_object(v___x_4765_);
                    v___x_4775_ = l_Lean_sortExprs(v_snd_4763_, v___x_4774_);
                    lean_dec(v_snd_4763_);
                    v_fst_4776_ = lean_ctor_get(v___x_4775_, 0);
                    v_snd_4777_ = lean_ctor_get(v___x_4775_, 1);
                    v_isSharedCheck_4795_ = (!lean_is_exclusive(v___x_4775_)) as u8;
                    if v_isSharedCheck_4795_ == 0 {
                        v___x_4779_ = v___x_4775_;
                        v_isShared_4780_ = v_isSharedCheck_4795_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4777_);
                        lean_inc(v_fst_4776_);
                        lean_dec(v___x_4775_);
                        v___x_4779_ = lean_box(0);
                        v_isShared_4780_ = v_isSharedCheck_4795_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4771_ == 0 {
                        lean_ctor_set(v___x_4770_, 1, v_snd_4763_);
                        lean_ctor_set(v___x_4770_, 0, v_snd_4768_);
                        v___x_4797_ = v___x_4770_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_snd_4768_);
                        lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_snd_4763_);
                        v___x_4797_ = v_reuseFailAlloc_4807_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4781_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4777_, v_fst_4767_);
                v___x_4782_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4777_, v_snd_4768_);
                lean_dec(v_snd_4777_);
                if v_isShared_4780_ == 0 {
                    lean_ctor_set(v___x_4779_, 1, v_fst_4776_);
                    lean_ctor_set(v___x_4779_, 0, v___x_4782_);
                    v___x_4784_ = v___x_4779_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4782_);
                    lean_ctor_set(v_reuseFailAlloc_4794_, 1, v_fst_4776_);
                    v___x_4784_ = v_reuseFailAlloc_4794_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4771_ == 0 {
                    lean_ctor_set(v___x_4770_, 1, v___x_4784_);
                    lean_ctor_set(v___x_4770_, 0, v___x_4781_);
                    v___x_4786_ = v___x_4770_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4781_);
                    lean_ctor_set(v_reuseFailAlloc_4793_, 1, v___x_4784_);
                    v___x_4786_ = v_reuseFailAlloc_4793_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4762_ == 0 {
                    lean_ctor_set(v___x_4761_, 0, v___x_4786_);
                    v___x_4788_ = v___x_4761_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4786_);
                    v___x_4788_ = v_reuseFailAlloc_4792_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4757_ == 0 {
                    lean_ctor_set(v___x_4756_, 0, v___x_4788_);
                    v___x_4790_ = v___x_4756_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
                    v___x_4790_ = v_reuseFailAlloc_4791_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4790_;
            }
            10 => {
                if v_isShared_4766_ == 0 {
                    lean_ctor_set(v___x_4765_, 1, v___x_4797_);
                    lean_ctor_set(v___x_4765_, 0, v_fst_4767_);
                    v___x_4799_ = v___x_4765_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_fst_4767_);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 1, v___x_4797_);
                    v___x_4799_ = v_reuseFailAlloc_4806_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4762_ == 0 {
                    lean_ctor_set(v___x_4761_, 0, v___x_4799_);
                    v___x_4801_ = v___x_4761_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4799_);
                    v___x_4801_ = v_reuseFailAlloc_4805_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4757_ == 0 {
                    lean_ctor_set(v___x_4756_, 0, v___x_4801_);
                    v___x_4803_ = v___x_4756_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4803_;
            }
            14 => {
                return v___x_4814_;
            }
            15 => {
                if v_isShared_4820_ == 0 {
                    v___x_4822_ = v___x_4819_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
                    v___x_4822_ = v_reuseFailAlloc_4823_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(
    mut v_e_4825_: *mut LeanObject,
    mut v_k_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
    mut v_a_4831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4832_: *mut LeanObject = core::ptr::null_mut();
    v_res_4832_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(
            v_e_4825_, v_k_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_,
        );
    lean_dec(v_a_4830_);
    lean_dec_ref(v_a_4829_);
    lean_dec(v_a_4828_);
    lean_dec_ref(v_a_4827_);
    return v_res_4832_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(
    mut v_e_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
    mut v_a_4836_: *mut LeanObject,
    mut v_a_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v_fst_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4849_: u8 = 0;
    let mut v_snd_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v_fst_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4882_: u8 = 0;
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut v_unused_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4898_: u8 = 0;
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4907_: u8 = 0;
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4839_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_4839_, 0, v_e_4833_);
                v___x_4840_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
                    v___x_4839_,
                    v_a_4834_,
                    v_a_4835_,
                    v_a_4836_,
                    v_a_4837_,
                );
                if lean_obj_tag(v___x_4840_) == 0 {
                    v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
                    v_isSharedCheck_4903_ = (!lean_is_exclusive(v___x_4840_)) as u8;
                    if v_isSharedCheck_4903_ == 0 {
                        v___x_4843_ = v___x_4840_;
                        v_isShared_4844_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4841_);
                        lean_dec(v___x_4840_);
                        v___x_4843_ = lean_box(0);
                        v_isShared_4844_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4904_ = lean_ctor_get(v___x_4840_, 0);
                    v_isSharedCheck_4911_ = (!lean_is_exclusive(v___x_4840_)) as u8;
                    if v_isSharedCheck_4911_ == 0 {
                        v___x_4906_ = v___x_4840_;
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4904_);
                        lean_dec(v___x_4840_);
                        v___x_4906_ = lean_box(0);
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4845_ = lean_ctor_get(v_a_4841_, 0);
                lean_inc(v_fst_4845_);
                if lean_obj_tag(v_fst_4845_) == 1 {
                    v_val_4846_ = lean_ctor_get(v_fst_4845_, 0);
                    v_isSharedCheck_4898_ = (!lean_is_exclusive(v_fst_4845_)) as u8;
                    if v_isSharedCheck_4898_ == 0 {
                        v___x_4848_ = v_fst_4845_;
                        v_isShared_4849_ = v_isSharedCheck_4898_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4846_);
                        lean_dec(v_fst_4845_);
                        v___x_4848_ = lean_box(0);
                        v_isShared_4849_ = v_isSharedCheck_4898_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_4845_);
                    lean_dec(v_a_4841_);
                    v___x_4899_ = lean_box(0);
                    if v_isShared_4844_ == 0 {
                        lean_ctor_set(v___x_4843_, 0, v___x_4899_);
                        v___x_4901_ = v___x_4843_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
                        v___x_4901_ = v_reuseFailAlloc_4902_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_4850_ = lean_ctor_get(v_a_4841_, 1);
                v_isSharedCheck_4896_ = (!lean_is_exclusive(v_a_4841_)) as u8;
                if v_isSharedCheck_4896_ == 0 {
                    v_unused_4897_ = lean_ctor_get(v_a_4841_, 0);
                    lean_dec(v_unused_4897_);
                    v___x_4852_ = v_a_4841_;
                    v_isShared_4853_ = v_isSharedCheck_4896_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4850_);
                    lean_dec(v_a_4841_);
                    v___x_4852_ = lean_box(0);
                    v_isShared_4853_ = v_isSharedCheck_4896_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4854_ = lean_ctor_get(v_val_4846_, 0);
                v_snd_4855_ = lean_ctor_get(v_val_4846_, 1);
                v_isSharedCheck_4895_ = (!lean_is_exclusive(v_val_4846_)) as u8;
                if v_isSharedCheck_4895_ == 0 {
                    v___x_4857_ = v_val_4846_;
                    v_isShared_4858_ = v_isSharedCheck_4895_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_4855_);
                    lean_inc(v_fst_4854_);
                    lean_dec(v_val_4846_);
                    v___x_4857_ = lean_box(0);
                    v_isShared_4858_ = v_isSharedCheck_4895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4859_ = lean_array_get_size(v_snd_4850_);
                v___x_4860_ = lean_unsigned_to_nat(1);
                v___x_4861_ = lean_nat_dec_le(v___x_4859_, v___x_4860_);
                if v___x_4861_ == 0 {
                    lean_del_object(v___x_4852_);
                    v___x_4862_ = l_Lean_sortExprs(v_snd_4850_, v___x_4861_);
                    lean_dec(v_snd_4850_);
                    v_fst_4863_ = lean_ctor_get(v___x_4862_, 0);
                    v_snd_4864_ = lean_ctor_get(v___x_4862_, 1);
                    v_isSharedCheck_4882_ = (!lean_is_exclusive(v___x_4862_)) as u8;
                    if v_isSharedCheck_4882_ == 0 {
                        v___x_4866_ = v___x_4862_;
                        v_isShared_4867_ = v_isSharedCheck_4882_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4864_);
                        lean_inc(v_fst_4863_);
                        lean_dec(v___x_4862_);
                        v___x_4866_ = lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4882_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4858_ == 0 {
                        lean_ctor_set(v___x_4857_, 1, v_snd_4850_);
                        lean_ctor_set(v___x_4857_, 0, v_snd_4855_);
                        v___x_4884_ = v___x_4857_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_snd_4855_);
                        lean_ctor_set(v_reuseFailAlloc_4894_, 1, v_snd_4850_);
                        v___x_4884_ = v_reuseFailAlloc_4894_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4868_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4864_, v_fst_4854_);
                v___x_4869_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4864_, v_snd_4855_);
                lean_dec(v_snd_4864_);
                if v_isShared_4867_ == 0 {
                    lean_ctor_set(v___x_4866_, 1, v_fst_4863_);
                    lean_ctor_set(v___x_4866_, 0, v___x_4869_);
                    v___x_4871_ = v___x_4866_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4869_);
                    lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_fst_4863_);
                    v___x_4871_ = v_reuseFailAlloc_4881_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4858_ == 0 {
                    lean_ctor_set(v___x_4857_, 1, v___x_4871_);
                    lean_ctor_set(v___x_4857_, 0, v___x_4868_);
                    v___x_4873_ = v___x_4857_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4868_);
                    lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4871_);
                    v___x_4873_ = v_reuseFailAlloc_4880_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4849_ == 0 {
                    lean_ctor_set(v___x_4848_, 0, v___x_4873_);
                    v___x_4875_ = v___x_4848_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4879_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4844_ == 0 {
                    lean_ctor_set(v___x_4843_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4843_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4877_;
            }
            10 => {
                if v_isShared_4853_ == 0 {
                    lean_ctor_set(v___x_4852_, 1, v___x_4884_);
                    lean_ctor_set(v___x_4852_, 0, v_fst_4854_);
                    v___x_4886_ = v___x_4852_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_fst_4854_);
                    lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4884_);
                    v___x_4886_ = v_reuseFailAlloc_4893_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4849_ == 0 {
                    lean_ctor_set(v___x_4848_, 0, v___x_4886_);
                    v___x_4888_ = v___x_4848_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4886_);
                    v___x_4888_ = v_reuseFailAlloc_4892_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4844_ == 0 {
                    lean_ctor_set(v___x_4843_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4843_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4890_;
            }
            14 => {
                return v___x_4901_;
            }
            15 => {
                if v_isShared_4907_ == 0 {
                    v___x_4909_ = v___x_4906_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(
    mut v_e_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4918_: *mut LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(
        v_e_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_,
    );
    lean_dec(v_a_4916_);
    lean_dec_ref(v_a_4915_);
    lean_dec(v_a_4914_);
    lean_dec_ref(v_a_4913_);
    return v_res_4918_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(
    mut v_e_4919_: *mut LeanObject,
    mut v_a_4920_: *mut LeanObject,
    mut v_a_4921_: *mut LeanObject,
    mut v_a_4922_: *mut LeanObject,
    mut v_a_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4930_: u8 = 0;
    let mut v_fst_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v_snd_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v_fst_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_unused_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v_a_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4925_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_4925_, 0, v_e_4919_);
                v___x_4926_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
                    v___x_4925_,
                    v_a_4920_,
                    v_a_4921_,
                    v_a_4922_,
                    v_a_4923_,
                );
                if lean_obj_tag(v___x_4926_) == 0 {
                    v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
                    v_isSharedCheck_4989_ = (!lean_is_exclusive(v___x_4926_)) as u8;
                    if v_isSharedCheck_4989_ == 0 {
                        v___x_4929_ = v___x_4926_;
                        v_isShared_4930_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4927_);
                        lean_dec(v___x_4926_);
                        v___x_4929_ = lean_box(0);
                        v_isShared_4930_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4990_ = lean_ctor_get(v___x_4926_, 0);
                    v_isSharedCheck_4997_ = (!lean_is_exclusive(v___x_4926_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4992_ = v___x_4926_;
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4990_);
                        lean_dec(v___x_4926_);
                        v___x_4992_ = lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4931_ = lean_ctor_get(v_a_4927_, 0);
                lean_inc(v_fst_4931_);
                if lean_obj_tag(v_fst_4931_) == 1 {
                    v_val_4932_ = lean_ctor_get(v_fst_4931_, 0);
                    v_isSharedCheck_4984_ = (!lean_is_exclusive(v_fst_4931_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4934_ = v_fst_4931_;
                        v_isShared_4935_ = v_isSharedCheck_4984_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4932_);
                        lean_dec(v_fst_4931_);
                        v___x_4934_ = lean_box(0);
                        v_isShared_4935_ = v_isSharedCheck_4984_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_4931_);
                    lean_dec(v_a_4927_);
                    v___x_4985_ = lean_box(0);
                    if v_isShared_4930_ == 0 {
                        lean_ctor_set(v___x_4929_, 0, v___x_4985_);
                        v___x_4987_ = v___x_4929_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
                        v___x_4987_ = v_reuseFailAlloc_4988_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_4936_ = lean_ctor_get(v_a_4927_, 1);
                v_isSharedCheck_4982_ = (!lean_is_exclusive(v_a_4927_)) as u8;
                if v_isSharedCheck_4982_ == 0 {
                    v_unused_4983_ = lean_ctor_get(v_a_4927_, 0);
                    lean_dec(v_unused_4983_);
                    v___x_4938_ = v_a_4927_;
                    v_isShared_4939_ = v_isSharedCheck_4982_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4936_);
                    lean_dec(v_a_4927_);
                    v___x_4938_ = lean_box(0);
                    v_isShared_4939_ = v_isSharedCheck_4982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4940_ = lean_ctor_get(v_val_4932_, 0);
                v_snd_4941_ = lean_ctor_get(v_val_4932_, 1);
                v_isSharedCheck_4981_ = (!lean_is_exclusive(v_val_4932_)) as u8;
                if v_isSharedCheck_4981_ == 0 {
                    v___x_4943_ = v_val_4932_;
                    v_isShared_4944_ = v_isSharedCheck_4981_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_4941_);
                    lean_inc(v_fst_4940_);
                    lean_dec(v_val_4932_);
                    v___x_4943_ = lean_box(0);
                    v_isShared_4944_ = v_isSharedCheck_4981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4945_ = lean_array_get_size(v_snd_4936_);
                v___x_4946_ = lean_unsigned_to_nat(1);
                v___x_4947_ = lean_nat_dec_le(v___x_4945_, v___x_4946_);
                if v___x_4947_ == 0 {
                    lean_del_object(v___x_4938_);
                    v___x_4948_ = l_Lean_sortExprs(v_snd_4936_, v___x_4947_);
                    lean_dec(v_snd_4936_);
                    v_fst_4949_ = lean_ctor_get(v___x_4948_, 0);
                    v_snd_4950_ = lean_ctor_get(v___x_4948_, 1);
                    v_isSharedCheck_4968_ = (!lean_is_exclusive(v___x_4948_)) as u8;
                    if v_isSharedCheck_4968_ == 0 {
                        v___x_4952_ = v___x_4948_;
                        v_isShared_4953_ = v_isSharedCheck_4968_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4950_);
                        lean_inc(v_fst_4949_);
                        lean_dec(v___x_4948_);
                        v___x_4952_ = lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4968_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4944_ == 0 {
                        lean_ctor_set(v___x_4943_, 1, v_snd_4936_);
                        lean_ctor_set(v___x_4943_, 0, v_snd_4941_);
                        v___x_4970_ = v___x_4943_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_snd_4941_);
                        lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_snd_4936_);
                        v___x_4970_ = v_reuseFailAlloc_4980_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4954_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4950_, v_fst_4940_);
                v___x_4955_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_4950_, v_snd_4941_);
                lean_dec(v_snd_4950_);
                if v_isShared_4953_ == 0 {
                    lean_ctor_set(v___x_4952_, 1, v_fst_4949_);
                    lean_ctor_set(v___x_4952_, 0, v___x_4955_);
                    v___x_4957_ = v___x_4952_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4955_);
                    lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_fst_4949_);
                    v___x_4957_ = v_reuseFailAlloc_4967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4944_ == 0 {
                    lean_ctor_set(v___x_4943_, 1, v___x_4957_);
                    lean_ctor_set(v___x_4943_, 0, v___x_4954_);
                    v___x_4959_ = v___x_4943_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4954_);
                    lean_ctor_set(v_reuseFailAlloc_4966_, 1, v___x_4957_);
                    v___x_4959_ = v_reuseFailAlloc_4966_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4935_ == 0 {
                    lean_ctor_set(v___x_4934_, 0, v___x_4959_);
                    v___x_4961_ = v___x_4934_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4959_);
                    v___x_4961_ = v_reuseFailAlloc_4965_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4930_ == 0 {
                    lean_ctor_set(v___x_4929_, 0, v___x_4961_);
                    v___x_4963_ = v___x_4929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4963_;
            }
            10 => {
                if v_isShared_4939_ == 0 {
                    lean_ctor_set(v___x_4938_, 1, v___x_4970_);
                    lean_ctor_set(v___x_4938_, 0, v_fst_4940_);
                    v___x_4972_ = v___x_4938_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_fst_4940_);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4970_);
                    v___x_4972_ = v_reuseFailAlloc_4979_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4935_ == 0 {
                    lean_ctor_set(v___x_4934_, 0, v___x_4972_);
                    v___x_4974_ = v___x_4934_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4972_);
                    v___x_4974_ = v_reuseFailAlloc_4978_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4930_ == 0 {
                    lean_ctor_set(v___x_4929_, 0, v___x_4974_);
                    v___x_4976_ = v___x_4929_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4974_);
                    v___x_4976_ = v_reuseFailAlloc_4977_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4976_;
            }
            14 => {
                return v___x_4987_;
            }
            15 => {
                if v_isShared_4993_ == 0 {
                    v___x_4995_ = v___x_4992_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(
    mut v_e_4998_: *mut LeanObject,
    mut v_a_4999_: *mut LeanObject,
    mut v_a_5000_: *mut LeanObject,
    mut v_a_5001_: *mut LeanObject,
    mut v_a_5002_: *mut LeanObject,
    mut v_a_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5004_: *mut LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(
        v_e_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_,
    );
    lean_dec(v_a_5002_);
    lean_dec_ref(v_a_5001_);
    lean_dec(v_a_5000_);
    lean_dec_ref(v_a_4999_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(
    mut v_e_5005_: *mut LeanObject,
    mut v_a_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v_fst_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v_snd_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5025_: u8 = 0;
    let mut v_fst_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5030_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5039_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5053_: u8 = 0;
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5066_: u8 = 0;
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut v_unused_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut v_a_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5011_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_5011_, 0, v_e_5005_);
                v___x_5012_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(
                    v___x_5011_,
                    v_a_5006_,
                    v_a_5007_,
                    v_a_5008_,
                    v_a_5009_,
                );
                if lean_obj_tag(v___x_5012_) == 0 {
                    v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
                    v_isSharedCheck_5074_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                    if v_isSharedCheck_5074_ == 0 {
                        v___x_5015_ = v___x_5012_;
                        v_isShared_5016_ = v_isSharedCheck_5074_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5013_);
                        lean_dec(v___x_5012_);
                        v___x_5015_ = lean_box(0);
                        v_isShared_5016_ = v_isSharedCheck_5074_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5075_ = lean_ctor_get(v___x_5012_, 0);
                    v_isSharedCheck_5082_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                    if v_isSharedCheck_5082_ == 0 {
                        v___x_5077_ = v___x_5012_;
                        v_isShared_5078_ = v_isSharedCheck_5082_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5075_);
                        lean_dec(v___x_5012_);
                        v___x_5077_ = lean_box(0);
                        v_isShared_5078_ = v_isSharedCheck_5082_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5017_ = lean_ctor_get(v_a_5013_, 0);
                lean_inc(v_fst_5017_);
                if lean_obj_tag(v_fst_5017_) == 1 {
                    v_val_5018_ = lean_ctor_get(v_fst_5017_, 0);
                    v_isSharedCheck_5069_ = (!lean_is_exclusive(v_fst_5017_)) as u8;
                    if v_isSharedCheck_5069_ == 0 {
                        v___x_5020_ = v_fst_5017_;
                        v_isShared_5021_ = v_isSharedCheck_5069_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_5018_);
                        lean_dec(v_fst_5017_);
                        v___x_5020_ = lean_box(0);
                        v_isShared_5021_ = v_isSharedCheck_5069_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5017_);
                    lean_dec(v_a_5013_);
                    v___x_5070_ = lean_box(0);
                    if v_isShared_5016_ == 0 {
                        lean_ctor_set(v___x_5015_, 0, v___x_5070_);
                        v___x_5072_ = v___x_5015_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
                        v___x_5072_ = v_reuseFailAlloc_5073_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5022_ = lean_ctor_get(v_a_5013_, 1);
                v_isSharedCheck_5067_ = (!lean_is_exclusive(v_a_5013_)) as u8;
                if v_isSharedCheck_5067_ == 0 {
                    v_unused_5068_ = lean_ctor_get(v_a_5013_, 0);
                    lean_dec(v_unused_5068_);
                    v___x_5024_ = v_a_5013_;
                    v_isShared_5025_ = v_isSharedCheck_5067_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_5022_);
                    lean_dec(v_a_5013_);
                    v___x_5024_ = lean_box(0);
                    v_isShared_5025_ = v_isSharedCheck_5067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_5026_ = lean_ctor_get(v_val_5018_, 0);
                v_snd_5027_ = lean_ctor_get(v_val_5018_, 1);
                v_isSharedCheck_5066_ = (!lean_is_exclusive(v_val_5018_)) as u8;
                if v_isSharedCheck_5066_ == 0 {
                    v___x_5029_ = v_val_5018_;
                    v_isShared_5030_ = v_isSharedCheck_5066_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_5027_);
                    lean_inc(v_fst_5026_);
                    lean_dec(v_val_5018_);
                    v___x_5029_ = lean_box(0);
                    v_isShared_5030_ = v_isSharedCheck_5066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5031_ = lean_array_get_size(v_snd_5022_);
                v___x_5032_ = lean_unsigned_to_nat(1);
                v___x_5033_ = lean_nat_dec_le(v___x_5031_, v___x_5032_);
                if v___x_5033_ == 0 {
                    lean_del_object(v___x_5024_);
                    v___x_5034_ = l_Lean_sortExprs(v_snd_5022_, v___x_5033_);
                    lean_dec(v_snd_5022_);
                    v_fst_5035_ = lean_ctor_get(v___x_5034_, 0);
                    v_snd_5036_ = lean_ctor_get(v___x_5034_, 1);
                    v_isSharedCheck_5053_ = (!lean_is_exclusive(v___x_5034_)) as u8;
                    if v_isSharedCheck_5053_ == 0 {
                        v___x_5038_ = v___x_5034_;
                        v_isShared_5039_ = v_isSharedCheck_5053_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_5036_);
                        lean_inc(v_fst_5035_);
                        lean_dec(v___x_5034_);
                        v___x_5038_ = lean_box(0);
                        v_isShared_5039_ = v_isSharedCheck_5053_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_5030_ == 0 {
                        lean_ctor_set(v___x_5029_, 1, v_snd_5022_);
                        lean_ctor_set(v___x_5029_, 0, v_snd_5027_);
                        v___x_5055_ = v___x_5029_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_snd_5027_);
                        lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_snd_5022_);
                        v___x_5055_ = v_reuseFailAlloc_5065_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5040_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_5036_, v_snd_5027_);
                lean_dec(v_snd_5036_);
                if v_isShared_5039_ == 0 {
                    lean_ctor_set(v___x_5038_, 1, v_fst_5035_);
                    lean_ctor_set(v___x_5038_, 0, v___x_5040_);
                    v___x_5042_ = v___x_5038_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5040_);
                    lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_fst_5035_);
                    v___x_5042_ = v_reuseFailAlloc_5052_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5030_ == 0 {
                    lean_ctor_set(v___x_5029_, 1, v___x_5042_);
                    v___x_5044_ = v___x_5029_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_fst_5026_);
                    lean_ctor_set(v_reuseFailAlloc_5051_, 1, v___x_5042_);
                    v___x_5044_ = v_reuseFailAlloc_5051_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5021_ == 0 {
                    lean_ctor_set(v___x_5020_, 0, v___x_5044_);
                    v___x_5046_ = v___x_5020_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5044_);
                    v___x_5046_ = v_reuseFailAlloc_5050_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5016_ == 0 {
                    lean_ctor_set(v___x_5015_, 0, v___x_5046_);
                    v___x_5048_ = v___x_5015_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
                    v___x_5048_ = v_reuseFailAlloc_5049_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5048_;
            }
            10 => {
                if v_isShared_5025_ == 0 {
                    lean_ctor_set(v___x_5024_, 1, v___x_5055_);
                    lean_ctor_set(v___x_5024_, 0, v_fst_5026_);
                    v___x_5057_ = v___x_5024_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_fst_5026_);
                    lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5055_);
                    v___x_5057_ = v_reuseFailAlloc_5064_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5021_ == 0 {
                    lean_ctor_set(v___x_5020_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5020_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5057_);
                    v___x_5059_ = v_reuseFailAlloc_5063_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5016_ == 0 {
                    lean_ctor_set(v___x_5015_, 0, v___x_5059_);
                    v___x_5061_ = v___x_5015_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5059_);
                    v___x_5061_ = v_reuseFailAlloc_5062_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5061_;
            }
            14 => {
                return v___x_5072_;
            }
            15 => {
                if v_isShared_5078_ == 0 {
                    v___x_5080_ = v___x_5077_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
                    v___x_5080_ = v_reuseFailAlloc_5081_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(
    mut v_e_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5089_: *mut LeanObject = core::ptr::null_mut();
    v_res_5089_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(
        v_e_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_,
    );
    lean_dec(v_a_5087_);
    lean_dec_ref(v_a_5086_);
    lean_dec(v_a_5085_);
    lean_dec_ref(v_a_5084_);
    return v_res_5089_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(
    mut v___y_5090_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_5090_);
    return v___y_5090_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(
    mut v___y_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5092_: *mut LeanObject = core::ptr::null_mut();
    v_res_5092_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(v___y_5091_);
    lean_dec_ref(v___y_5091_);
    return v_res_5092_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1() -> *mut LeanObject {
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    v___x_5094_ = lean_box(0);
    v___x_5095_ = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
    v___x_5096_ = l_Lean_mkConst(v___x_5095_, v___x_5094_);
    return v___x_5096_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2() -> *mut LeanObject {
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    v___x_5097_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
    v___x_5098_ = l_Lean_mkIntLit(v___x_5097_);
    return v___x_5098_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3() -> *mut LeanObject {
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    v___x_5099_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2,
    );
    v___x_5100_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5100_, 0, v___x_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toContextExpr(
    mut v_ctx_5101_: *mut LeanObject,
    mut v_a_5102_: *mut LeanObject,
    mut v_a_5103_: *mut LeanObject,
    mut v_a_5104_: *mut LeanObject,
    mut v_a_5105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: u8 = 0;
    v___x_5107_ = lean_unsigned_to_nat(0);
    v___x_5108_ = lean_array_get_size(v_ctx_5101_);
    v___x_5109_ = lean_nat_dec_lt(v___x_5107_, v___x_5108_);
    if v___x_5109_ == 0 {
        let mut v___f_5110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ctx_5101_);
        v___f_5110_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
        v___x_5111_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1,
        );
        v___x_5112_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once),
            _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3,
        );
        v___x_5113_ = l_Lean_RArray_toExpr___redArg(
            v___x_5111_,
            v___f_5110_,
            v___x_5112_,
            v_a_5102_,
            v_a_5103_,
            v_a_5104_,
            v_a_5105_,
        );
        return v___x_5113_;
    } else {
        let mut v___f_5114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
        v___f_5114_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
        v___x_5115_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1,
        );
        v___x_5116_ = l_Lean_RArray_ofArray___redArg(v_ctx_5101_);
        v___x_5117_ = l_Lean_RArray_toExpr___redArg(
            v___x_5115_,
            v___f_5114_,
            v___x_5116_,
            v_a_5102_,
            v_a_5103_,
            v_a_5104_,
            v_a_5105_,
        );
        return v___x_5117_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(
    mut v_ctx_5118_: *mut LeanObject,
    mut v_a_5119_: *mut LeanObject,
    mut v_a_5120_: *mut LeanObject,
    mut v_a_5121_: *mut LeanObject,
    mut v_a_5122_: *mut LeanObject,
    mut v_a_5123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5124_: *mut LeanObject = core::ptr::null_mut();
    v_res_5124_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
        v_ctx_5118_,
        v_a_5119_,
        v_a_5120_,
        v_a_5121_,
        v_a_5122_,
    );
    lean_dec(v_a_5122_);
    lean_dec_ref(v_a_5121_);
    lean_dec(v_a_5120_);
    lean_dec_ref(v_a_5119_);
    return v_res_5124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SortExprs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KExprMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Simp_Arith_Int_instToExprPoly = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly();
    lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly);
    l_Lean_Meta_Simp_Arith_Int_instToExprExpr = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr();
    lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SortExprs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_KExprMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
}
