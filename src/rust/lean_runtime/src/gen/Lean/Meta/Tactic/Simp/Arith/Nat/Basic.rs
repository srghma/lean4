// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: Lean.Util.SortExprs Lean.Meta.KExprMap Lean.Data.RArray Lean.Meta.NatInstTesters Lean.Meta.Offset Init.Data.Nat.Linear
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, l_Nat_Linear_Expr_inc, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
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
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkInstOfNatNat, l_Lean_mkNatAdd, l_Lean_mkNatEq,
    l_Lean_mkNatLE, l_Lean_mkNatLit, l_Lean_mkNatMul,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEqI,
};
use crate::r#gen::Lean::Meta::KExprMap::{
    initialize_Lean_Meta_KExprMap, l_Lean_Meta_KExprMap_find_x3f___redArg,
    l_Lean_Meta_KExprMap_insert___redArg, runtime_initialize_Lean_Meta_KExprMap,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_DefEq_isInstAddNat,
    l_Lean_Meta_DefEq_isInstHAddNat, l_Lean_Meta_DefEq_isInstHMulNat,
    l_Lean_Meta_DefEq_isInstLENat, l_Lean_Meta_DefEq_isInstLTNat, l_Lean_Meta_DefEq_isInstMulNat,
    l_Lean_Meta_Structural_isInstOfNatNat___redArg, runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Offset::{
    initialize_Lean_Meta_Offset, l_Lean_Meta_evalNat, runtime_initialize_Lean_Meta_Offset,
};
use crate::r#gen::Lean::Util::SortExprs::{
    initialize_Lean_Util_SortExprs, l_Lean_sortExprs, runtime_initialize_Lean_Util_SortExprs,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 110, 117, 109, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value
            ) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value
            ) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value: LeanStringObject<
    21,
> = LeanStringObject {
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108, 76,
        0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value: LeanStringObject<
    21,
> = LeanStringObject {
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108, 82,
        0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 104, 115, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 104, 115, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value
) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value
) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value)
        as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value) as *mut LeanObject;
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value) as *mut LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value) as *mut LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value)
                as *mut LeanObject,
            7684849496198239688 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value)
                as *mut LeanObject,
            18175190525027609149 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value)
                as *mut LeanObject,
            14196997771537767481 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value)
                as *mut LeanObject,
            4793823359960896323 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value)
                as *mut LeanObject,
            15046034327177700902 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value: LeanStringObject<10> =
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
        m_data: [69, 120, 112, 114, 67, 110, 115, 116, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value: LeanStringObject<3> =
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
        m_data: [109, 107, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
                as *mut LeanObject,
            7629568945124732217 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value)
                as *mut LeanObject,
            15767036023735109173 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value: LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
                as *mut LeanObject,
            7629568945124732217 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value: LeanStringObject<5> =
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
        m_data: [122, 101, 114, 111, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value) as *mut LeanObject,16112798088292836701 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut LeanObject,14305945245784925820 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value) as *mut LeanObject,17073733886952259026 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value) as *mut LeanObject,4707481103260653979 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut LeanObject,11383192766313517692 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value) as *mut LeanObject,17313347264508353403 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value) as *mut LeanObject,6683391611519377970 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
            as *mut LeanObject,
        17284123358135039274 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
            as *mut LeanObject,
        10778933377320331970 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value)
            as *mut LeanObject,
        2272833755566510320 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value)
            as *mut LeanObject,
        9426339939459091439 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value)
            as *mut LeanObject,
        1755019837031360842 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value
        ) as *mut LeanObject,
        5555145617058846791 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value
        ) as *mut LeanObject,
        17878876274162330439 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
            as *mut LeanObject,
        11833570877100518198 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value
        ) as *mut LeanObject,
        8347582161988589016 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
            as *mut LeanObject,
        7316284823769321069 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(
    mut v_a_1825_: *mut LeanObject,
    mut v_x_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1826_) == 0 {
                    v___x_1827_ = lean_box(0);
                    return v___x_1827_;
                } else {
                    v_key_1828_ = lean_ctor_get(v_x_1826_, 0);
                    v_value_1829_ = lean_ctor_get(v_x_1826_, 1);
                    v_tail_1830_ = lean_ctor_get(v_x_1826_, 2);
                    v___x_1831_ = lean_nat_dec_eq(v_key_1828_, v_a_1825_);
                    if v___x_1831_ == 0 {
                        v_x_1826_ = v_tail_1830_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1829_);
                        v___x_1833_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1833_, 0, v_value_1829_);
                        return v___x_1833_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1834_: *mut LeanObject,
    mut v_x_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1836_: *mut LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1834_, v_x_1835_);
    lean_dec(v_x_1835_);
    lean_dec(v_a_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(
    mut v_m_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u64 = 0;
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v_fold_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v___x_1847_: u64 = 0;
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1839_ = lean_ctor_get(v_m_1837_, 1);
    v___x_1840_ = lean_array_get_size(v_buckets_1839_);
    v___x_1841_ = lean_uint64_of_nat(v_a_1838_);
    v___x_1842_ = 32u64;
    v___x_1843_ = lean_uint64_shift_right(v___x_1841_, v___x_1842_);
    v_fold_1844_ = lean_uint64_xor(v___x_1841_, v___x_1843_);
    v___x_1845_ = 16u64;
    v___x_1846_ = lean_uint64_shift_right(v_fold_1844_, v___x_1845_);
    v___x_1847_ = lean_uint64_xor(v_fold_1844_, v___x_1846_);
    v___x_1848_ = lean_uint64_to_usize(v___x_1847_);
    v___x_1849_ = lean_usize_of_nat(v___x_1840_);
    v___x_1850_ = 1usize;
    v___x_1851_ = lean_usize_sub(v___x_1849_, v___x_1850_);
    v___x_1852_ = lean_usize_land(v___x_1848_, v___x_1851_);
    v___x_1853_ = lean_array_uget_borrowed(v_buckets_1839_, v___x_1852_);
    v___x_1854_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1838_, v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(
    mut v_m_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_1855_, v_a_1856_);
    lean_dec(v_a_1856_);
    lean_dec_ref(v_m_1855_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
    mut v_perm_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_val_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_unused_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_k_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_a_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_1859_) {
                0 => {
                    return v_a_1859_;
                }
                1 => {
                    v_i_1860_ = lean_ctor_get(v_a_1859_, 0);
                    v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_1858_, v_i_1860_);
                    if lean_obj_tag(v___x_1861_) == 0 {
                        return v_a_1859_;
                    } else {
                        v_isSharedCheck_1869_ = (!lean_is_exclusive(v_a_1859_)) as u8;
                        if v_isSharedCheck_1869_ == 0 {
                            v_unused_1870_ = lean_ctor_get(v_a_1859_, 0);
                            lean_dec(v_unused_1870_);
                            v___x_1863_ = v_a_1859_;
                            v_isShared_1864_ = v_isSharedCheck_1869_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1859_);
                            v___x_1863_ = lean_box(0);
                            v_isShared_1864_ = v_isSharedCheck_1869_;
                            state = 1;
                            continue;
                        }
                    }
                }
                2 => {
                    v_a_1871_ = lean_ctor_get(v_a_1859_, 0);
                    v_b_1872_ = lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1881_ = (!lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1881_ == 0 {
                        v___x_1874_ = v_a_1859_;
                        v_isShared_1875_ = v_isSharedCheck_1881_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_b_1872_);
                        lean_inc(v_a_1871_);
                        lean_dec(v_a_1859_);
                        v___x_1874_ = lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1881_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_k_1882_ = lean_ctor_get(v_a_1859_, 0);
                    v_a_1883_ = lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1891_ = (!lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1891_ == 0 {
                        v___x_1885_ = v_a_1859_;
                        v_isShared_1886_ = v_isSharedCheck_1891_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1883_);
                        lean_inc(v_k_1882_);
                        lean_dec(v_a_1859_);
                        v___x_1885_ = lean_box(0);
                        v_isShared_1886_ = v_isSharedCheck_1891_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_a_1892_ = lean_ctor_get(v_a_1859_, 0);
                    v_k_1893_ = lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1901_ = (!lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1895_ = v_a_1859_;
                        v_isShared_1896_ = v_isSharedCheck_1901_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_k_1893_);
                        lean_inc(v_a_1892_);
                        lean_dec(v_a_1859_);
                        v___x_1895_ = lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1901_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_val_1865_ = lean_ctor_get(v___x_1861_, 0);
                lean_inc(v_val_1865_);
                lean_dec_ref_known(v___x_1861_, 1);
                if v_isShared_1864_ == 0 {
                    lean_ctor_set(v___x_1863_, 0, v_val_1865_);
                    v___x_1867_ = v___x_1863_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_val_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1867_;
            }
            3 => {
                v___x_1876_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1871_);
                v___x_1877_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_b_1872_);
                if v_isShared_1875_ == 0 {
                    lean_ctor_set(v___x_1874_, 1, v___x_1877_);
                    lean_ctor_set(v___x_1874_, 0, v___x_1876_);
                    v___x_1879_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1879_;
            }
            5 => {
                v___x_1887_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1883_);
                if v_isShared_1886_ == 0 {
                    lean_ctor_set(v___x_1885_, 1, v___x_1887_);
                    v___x_1889_ = v___x_1885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_k_1882_);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1887_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1889_;
            }
            7 => {
                v___x_1897_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1892_);
                if v_isShared_1896_ == 0 {
                    lean_ctor_set(v___x_1895_, 0, v___x_1897_);
                    v___x_1899_ = v___x_1895_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_k_1893_);
                    v___x_1899_ = v_reuseFailAlloc_1900_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(
    mut v_perm_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1904_: *mut LeanObject = core::ptr::null_mut();
    v_res_1904_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
        v_perm_1902_,
        v_a_1903_,
    );
    lean_dec_ref(v_perm_1902_);
    return v_res_1904_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(
    mut v_00_u03b2_1905_: *mut LeanObject,
    mut v_m_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_1906_, v_a_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(
    mut v_00_u03b2_1909_: *mut LeanObject,
    mut v_m_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1912_: *mut LeanObject = core::ptr::null_mut();
    v_res_1912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_1909_, v_m_1910_, v_a_1911_);
    lean_dec(v_a_1911_);
    lean_dec_ref(v_m_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(
    mut v_00_u03b2_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
    mut v_x_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1914_, v_x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
    mut v_x_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_1917_, v_a_1918_, v_x_1919_);
    lean_dec(v_x_1919_);
    lean_dec(v_a_1918_);
    return v_res_1920_;
}
pub unsafe fn l_Nat_Linear_Expr_applyPerm(
    mut v_perm_1921_: *mut LeanObject,
    mut v_e_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    v___x_1923_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
        v_perm_1921_,
        v_e_1922_,
    );
    return v___x_1923_;
}
pub unsafe fn l_Nat_Linear_Expr_applyPerm___boxed(
    mut v_perm_1924_: *mut LeanObject,
    mut v_e_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1926_: *mut LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Nat_Linear_Expr_applyPerm(v_perm_1924_, v_e_1925_);
    lean_dec_ref(v_perm_1924_);
    return v_res_1926_;
}
pub unsafe fn l_Nat_Linear_ExprCnstr_applyPerm(
    mut v_perm_1927_: *mut LeanObject,
    mut v_x_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_1929_: u8 = 0;
    let mut v_lhs_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1929_ = lean_ctor_get_uint8(
                    v_x_1928_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_lhs_1930_ = lean_ctor_get(v_x_1928_, 0);
                v_rhs_1931_ = lean_ctor_get(v_x_1928_, 1);
                v_isSharedCheck_1940_ = (!lean_is_exclusive(v_x_1928_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v___x_1933_ = v_x_1928_;
                    v_isShared_1934_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rhs_1931_);
                    lean_inc(v_lhs_1930_);
                    lean_dec(v_x_1928_);
                    v___x_1933_ = lean_box(0);
                    v_isShared_1934_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1935_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1927_, v_lhs_1930_);
                v___x_1936_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1927_, v_rhs_1931_);
                if v_isShared_1934_ == 0 {
                    lean_ctor_set(v___x_1933_, 1, v___x_1936_);
                    lean_ctor_set(v___x_1933_, 0, v___x_1935_);
                    v___x_1938_ = v___x_1933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1935_);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1936_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1939_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_eq_1929_,
                    );
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_ExprCnstr_applyPerm___boxed(
    mut v_perm_1941_: *mut LeanObject,
    mut v_x_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1943_: *mut LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Nat_Linear_ExprCnstr_applyPerm(v_perm_1941_, v_x_1942_);
    lean_dec_ref(v_perm_1941_);
    return v_res_1943_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3()
-> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_unsigned_to_nat(2);
    v___x_1951_ = lean_nat_to_int(v___x_1950_);
    return v___x_1951_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4()
-> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = lean_unsigned_to_nat(1);
    v___x_1953_ = lean_nat_to_int(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(
    mut v_x_1978_: *mut LeanObject,
    mut v_prec_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___y_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_i_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___y_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_a_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_k_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_a_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1978_) {
                0 => {
                    v_v_1980_ = lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_2000_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2000_ == 0 {
                        v___x_1982_ = v_x_1978_;
                        v_isShared_1983_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_1980_);
                        lean_dec(v_x_1978_);
                        v___x_1982_ = lean_box(0);
                        v_isShared_1983_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_2001_ = lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_2021_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2021_ == 0 {
                        v___x_2003_ = v_x_1978_;
                        v_isShared_2004_ = v_isSharedCheck_2021_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_i_2001_);
                        lean_dec(v_x_1978_);
                        v___x_2003_ = lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2021_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_a_2022_ = lean_ctor_get(v_x_1978_, 0);
                    v_b_2023_ = lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2025_ = v_x_1978_;
                        v_isShared_2026_ = v_isSharedCheck_2046_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_b_2023_);
                        lean_inc(v_a_2022_);
                        lean_dec(v_x_1978_);
                        v___x_2025_ = lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2046_;
                        state = 7;
                        continue;
                    }
                }
                3 => {
                    v_k_2047_ = lean_ctor_get(v_x_1978_, 0);
                    v_a_2048_ = lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2072_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2072_ == 0 {
                        v___x_2050_ = v_x_1978_;
                        v_isShared_2051_ = v_isSharedCheck_2072_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2048_);
                        lean_inc(v_k_2047_);
                        lean_dec(v_x_1978_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2072_;
                        state = 10;
                        continue;
                    }
                }
                _ => {
                    v_a_2073_ = lean_ctor_get(v_x_1978_, 0);
                    v_k_2074_ = lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2098_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_2076_ = v_x_1978_;
                        v_isShared_2077_ = v_isSharedCheck_2098_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_k_2074_);
                        lean_inc(v_a_2073_);
                        lean_dec(v_x_1978_);
                        v___x_2076_ = lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2098_;
                        state = 13;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1996_ = lean_unsigned_to_nat(1024);
                v___x_1997_ = lean_nat_dec_le(v___x_1996_, v_prec_1979_);
                if v___x_1997_ == 0 {
                    v___x_1998_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_1985_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v___x_1999_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_1985_ = v___x_1999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1986_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2;
                v___x_1987_ = l_Nat_reprFast(v_v_1980_);
                if v_isShared_1983_ == 0 {
                    lean_ctor_set_tag(v___x_1982_, 3);
                    lean_ctor_set(v___x_1982_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1987_);
                    v___x_1989_ = v_reuseFailAlloc_1995_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1990_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1990_, 0, v___x_1986_);
                lean_ctor_set(v___x_1990_, 1, v___x_1989_);
                lean_inc(v___y_1985_);
                v___x_1991_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1991_, 0, v___y_1985_);
                lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                v___x_1992_ = 0;
                v___x_1993_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1993_, 0, v___x_1991_);
                lean_ctor_set_uint8(
                    v___x_1993_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1992_,
                );
                v___x_1994_ = l_Repr_addAppParen(v___x_1993_, v_prec_1979_);
                return v___x_1994_;
            }
            4 => {
                v___x_2017_ = lean_unsigned_to_nat(1024);
                v___x_2018_ = lean_nat_dec_le(v___x_2017_, v_prec_1979_);
                if v___x_2018_ == 0 {
                    v___x_2019_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2006_ = v___x_2019_;
                    state = 5;
                    continue;
                } else {
                    v___x_2020_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2006_ = v___x_2020_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2007_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7;
                v___x_2008_ = l_Nat_reprFast(v_i_2001_);
                if v_isShared_2004_ == 0 {
                    lean_ctor_set_tag(v___x_2003_, 3);
                    lean_ctor_set(v___x_2003_, 0, v___x_2008_);
                    v___x_2010_ = v___x_2003_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
                    v___x_2010_ = v_reuseFailAlloc_2016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2011_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2011_, 0, v___x_2007_);
                lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                lean_inc(v___y_2006_);
                v___x_2012_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2012_, 0, v___y_2006_);
                lean_ctor_set(v___x_2012_, 1, v___x_2011_);
                v___x_2013_ = 0;
                v___x_2014_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                lean_ctor_set_uint8(
                    v___x_2014_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2013_,
                );
                v___x_2015_ = l_Repr_addAppParen(v___x_2014_, v_prec_1979_);
                return v___x_2015_;
            }
            7 => {
                v___x_2027_ = lean_unsigned_to_nat(1024);
                v___x_2043_ = lean_nat_dec_le(v___x_2027_, v_prec_1979_);
                if v___x_2043_ == 0 {
                    v___x_2044_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2029_ = v___x_2044_;
                    state = 8;
                    continue;
                } else {
                    v___x_2045_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2029_ = v___x_2045_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2030_ = lean_box(1);
                v___x_2031_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10;
                v___x_2032_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2022_, v___x_2027_);
                if v_isShared_2026_ == 0 {
                    lean_ctor_set_tag(v___x_2025_, 5);
                    lean_ctor_set(v___x_2025_, 1, v___x_2032_);
                    lean_ctor_set(v___x_2025_, 0, v___x_2031_);
                    v___x_2034_ = v___x_2025_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2031_);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2032_);
                    v___x_2034_ = v_reuseFailAlloc_2042_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2035_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2035_, 0, v___x_2034_);
                lean_ctor_set(v___x_2035_, 1, v___x_2030_);
                v___x_2036_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_b_2023_, v___x_2027_);
                v___x_2037_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2037_, 0, v___x_2035_);
                lean_ctor_set(v___x_2037_, 1, v___x_2036_);
                lean_inc(v___y_2029_);
                v___x_2038_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2038_, 0, v___y_2029_);
                lean_ctor_set(v___x_2038_, 1, v___x_2037_);
                v___x_2039_ = 0;
                v___x_2040_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2040_, 0, v___x_2038_);
                lean_ctor_set_uint8(
                    v___x_2040_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2039_,
                );
                v___x_2041_ = l_Repr_addAppParen(v___x_2040_, v_prec_1979_);
                return v___x_2041_;
            }
            10 => {
                v___x_2052_ = lean_unsigned_to_nat(1024);
                v___x_2069_ = lean_nat_dec_le(v___x_2052_, v_prec_1979_);
                if v___x_2069_ == 0 {
                    v___x_2070_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2054_ = v___x_2070_;
                    state = 11;
                    continue;
                } else {
                    v___x_2071_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2054_ = v___x_2071_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2055_ = lean_box(1);
                v___x_2056_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13;
                v___x_2057_ = l_Nat_reprFast(v_k_2047_);
                v___x_2058_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2058_, 0, v___x_2057_);
                if v_isShared_2051_ == 0 {
                    lean_ctor_set_tag(v___x_2050_, 5);
                    lean_ctor_set(v___x_2050_, 1, v___x_2058_);
                    lean_ctor_set(v___x_2050_, 0, v___x_2056_);
                    v___x_2060_ = v___x_2050_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2056_);
                    lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2058_);
                    v___x_2060_ = v_reuseFailAlloc_2068_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2061_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                lean_ctor_set(v___x_2061_, 1, v___x_2055_);
                v___x_2062_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2048_, v___x_2052_);
                v___x_2063_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                lean_inc(v___y_2054_);
                v___x_2064_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2064_, 0, v___y_2054_);
                lean_ctor_set(v___x_2064_, 1, v___x_2063_);
                v___x_2065_ = 0;
                v___x_2066_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                lean_ctor_set_uint8(
                    v___x_2066_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2065_,
                );
                v___x_2067_ = l_Repr_addAppParen(v___x_2066_, v_prec_1979_);
                return v___x_2067_;
            }
            13 => {
                v___x_2078_ = lean_unsigned_to_nat(1024);
                v___x_2095_ = lean_nat_dec_le(v___x_2078_, v_prec_1979_);
                if v___x_2095_ == 0 {
                    v___x_2096_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2080_ = v___x_2096_;
                    state = 14;
                    continue;
                } else {
                    v___x_2097_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2080_ = v___x_2097_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2081_ = lean_box(1);
                v___x_2082_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16;
                v___x_2083_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2073_, v___x_2078_);
                if v_isShared_2077_ == 0 {
                    lean_ctor_set_tag(v___x_2076_, 5);
                    lean_ctor_set(v___x_2076_, 1, v___x_2083_);
                    lean_ctor_set(v___x_2076_, 0, v___x_2082_);
                    v___x_2085_ = v___x_2076_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2082_);
                    lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2083_);
                    v___x_2085_ = v_reuseFailAlloc_2094_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2086_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                lean_ctor_set(v___x_2086_, 1, v___x_2081_);
                v___x_2087_ = l_Nat_reprFast(v_k_2074_);
                v___x_2088_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                v___x_2089_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2089_, 0, v___x_2086_);
                lean_ctor_set(v___x_2089_, 1, v___x_2088_);
                lean_inc(v___y_2080_);
                v___x_2090_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2090_, 0, v___y_2080_);
                lean_ctor_set(v___x_2090_, 1, v___x_2089_);
                v___x_2091_ = 0;
                v___x_2092_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2092_, 0, v___x_2090_);
                lean_ctor_set_uint8(
                    v___x_2092_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2091_,
                );
                v___x_2093_ = l_Repr_addAppParen(v___x_2092_, v_prec_1979_);
                return v___x_2093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(
    mut v_x_2099_: *mut LeanObject,
    mut v_prec_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2101_: *mut LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_x_2099_, v_prec_2100_);
    lean_dec(v_prec_2100_);
    return v_res_2101_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(
    mut v_a_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = lean_nat_to_int(v_a_2104_);
    return v___x_2105_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    v___x_2119_ = lean_unsigned_to_nat(6);
    v___x_2120_ = lean_nat_to_int(v___x_2119_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2127_ = lean_unsigned_to_nat(7);
    v___x_2128_ = lean_nat_to_int(v___x_2127_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    v___x_2133_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0;
    v___x_2134_ = lean_string_length(v___x_2133_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    v___x_2135_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16,
    );
    v___x_2136_ = lean_nat_to_int(v___x_2135_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(
    mut v_x_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_2142_: u8 = 0;
    let mut v_lhs_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v_eq_2142_ = lean_ctor_get_uint8(
        v_x_2141_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_lhs_2143_ = lean_ctor_get(v_x_2141_, 0);
    lean_inc_ref(v_lhs_2143_);
    v_rhs_2144_ = lean_ctor_get(v_x_2141_, 1);
    lean_inc_ref(v_rhs_2144_);
    lean_dec_ref(v_x_2141_);
    v___x_2145_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
    v___x_2146_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
    v___x_2147_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7,
    );
    v___x_2148_ = lean_unsigned_to_nat(0);
    v___x_2149_ = l_Bool_repr___redArg(v_eq_2142_);
    v___x_2150_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2150_, 0, v___x_2147_);
    lean_ctor_set(v___x_2150_, 1, v___x_2149_);
    v___x_2151_ = 0;
    v___x_2152_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2152_, 0, v___x_2150_);
    lean_ctor_set_uint8(
        v___x_2152_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2153_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2153_, 0, v___x_2146_);
    lean_ctor_set(v___x_2153_, 1, v___x_2152_);
    v___x_2154_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
    v___x_2155_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2155_, 0, v___x_2153_);
    lean_ctor_set(v___x_2155_, 1, v___x_2154_);
    v___x_2156_ = lean_box(1);
    v___x_2157_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2157_, 0, v___x_2155_);
    lean_ctor_set(v___x_2157_, 1, v___x_2156_);
    v___x_2158_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
    v___x_2159_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2159_, 0, v___x_2157_);
    lean_ctor_set(v___x_2159_, 1, v___x_2158_);
    v___x_2160_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2160_, 0, v___x_2159_);
    lean_ctor_set(v___x_2160_, 1, v___x_2145_);
    v___x_2161_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12,
    );
    v___x_2162_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_lhs_2143_, v___x_2148_);
    v___x_2163_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2163_, 0, v___x_2161_);
    lean_ctor_set(v___x_2163_, 1, v___x_2162_);
    v___x_2164_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2164_, 0, v___x_2163_);
    lean_ctor_set_uint8(
        v___x_2164_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2165_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2165_, 0, v___x_2160_);
    lean_ctor_set(v___x_2165_, 1, v___x_2164_);
    v___x_2166_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    lean_ctor_set(v___x_2166_, 1, v___x_2154_);
    v___x_2167_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2167_, 0, v___x_2166_);
    lean_ctor_set(v___x_2167_, 1, v___x_2156_);
    v___x_2168_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
    v___x_2169_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2169_, 0, v___x_2167_);
    lean_ctor_set(v___x_2169_, 1, v___x_2168_);
    v___x_2170_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2170_, 0, v___x_2169_);
    lean_ctor_set(v___x_2170_, 1, v___x_2145_);
    v___x_2171_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_rhs_2144_, v___x_2148_);
    v___x_2172_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2172_, 0, v___x_2161_);
    lean_ctor_set(v___x_2172_, 1, v___x_2171_);
    v___x_2173_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2174_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2174_, 0, v___x_2170_);
    lean_ctor_set(v___x_2174_, 1, v___x_2173_);
    v___x_2175_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17,
    );
    v___x_2176_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
    v___x_2177_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    lean_ctor_set(v___x_2177_, 1, v___x_2174_);
    v___x_2178_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
    v___x_2179_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2179_, 0, v___x_2177_);
    lean_ctor_set(v___x_2179_, 1, v___x_2178_);
    v___x_2180_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2180_, 0, v___x_2175_);
    lean_ctor_set(v___x_2180_, 1, v___x_2179_);
    v___x_2181_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    lean_ctor_set_uint8(
        v___x_2181_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    return v___x_2181_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(
    mut v_x_2182_: *mut LeanObject,
    mut v_prec_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(v_x_2182_);
    return v___x_2184_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(
    mut v_x_2185_: *mut LeanObject,
    mut v_prec_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(v_x_2185_, v_prec_2186_);
    lean_dec(v_prec_2186_);
    return v_res_2187_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_2190_: *mut LeanObject,
    mut v_x_2191_: *mut LeanObject,
    mut v_x_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2192_) == 0 {
                    lean_dec(v_x_2190_);
                    return v_x_2191_;
                } else {
                    v_head_2193_ = lean_ctor_get(v_x_2192_, 0);
                    v_tail_2194_ = lean_ctor_get(v_x_2192_, 1);
                    v_isSharedCheck_2203_ = (!lean_is_exclusive(v_x_2192_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2196_ = v_x_2192_;
                        v_isShared_2197_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2194_);
                        lean_inc(v_head_2193_);
                        lean_dec(v_x_2192_);
                        v___x_2196_ = lean_box(0);
                        v_isShared_2197_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2190_);
                if v_isShared_2197_ == 0 {
                    lean_ctor_set_tag(v___x_2196_, 5);
                    lean_ctor_set(v___x_2196_, 1, v_x_2190_);
                    lean_ctor_set(v___x_2196_, 0, v_x_2191_);
                    v___x_2199_ = v___x_2196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_x_2191_);
                    lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_x_2190_);
                    v___x_2199_ = v_reuseFailAlloc_2202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2200_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                lean_ctor_set(v___x_2200_, 1, v_head_2193_);
                v_x_2191_ = v___x_2200_;
                v_x_2192_ = v_tail_2194_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(
    mut v_x_2204_: *mut LeanObject,
    mut v_x_2205_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2204_) == 0 {
        let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2205_);
        v___x_2206_ = lean_box(0);
        return v___x_2206_;
    } else {
        let mut v_tail_2207_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2207_ = lean_ctor_get(v_x_2204_, 1);
        if lean_obj_tag(v_tail_2207_) == 0 {
            let mut v_head_2208_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2205_);
            v_head_2208_ = lean_ctor_get(v_x_2204_, 0);
            lean_inc(v_head_2208_);
            lean_dec_ref_known(v_x_2204_, 2);
            return v_head_2208_;
        } else {
            let mut v_head_2209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2207_);
            v_head_2209_ = lean_ctor_get(v_x_2204_, 0);
            lean_inc(v_head_2209_);
            lean_dec_ref_known(v_x_2204_, 2);
            v___x_2210_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(v_x_2205_, v_head_2209_, v_tail_2207_);
            return v___x_2210_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    v___x_2216_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2217_ = lean_string_length(v___x_2216_);
    return v___x_2217_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3);
    v___x_2219_ = lean_nat_to_int(v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(
    mut v_x_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2225_ = lean_ctor_get(v_x_2224_, 0);
                v_snd_2226_ = lean_ctor_get(v_x_2224_, 1);
                v_isSharedCheck_2250_ = (!lean_is_exclusive(v_x_2224_)) as u8;
                if v_isSharedCheck_2250_ == 0 {
                    v___x_2228_ = v_x_2224_;
                    v_isShared_2229_ = v_isSharedCheck_2250_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2226_);
                    lean_inc(v_fst_2225_);
                    lean_dec(v_x_2224_);
                    v___x_2228_ = lean_box(0);
                    v_isShared_2229_ = v_isSharedCheck_2250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2230_ = l_Nat_reprFast(v_fst_2225_);
                v___x_2231_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2231_, 0, v___x_2230_);
                v___x_2232_ = lean_box(0);
                if v_isShared_2229_ == 0 {
                    lean_ctor_set_tag(v___x_2228_, 1);
                    lean_ctor_set(v___x_2228_, 1, v___x_2232_);
                    lean_ctor_set(v___x_2228_, 0, v___x_2231_);
                    v___x_2234_ = v___x_2228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2231_);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2232_);
                    v___x_2234_ = v_reuseFailAlloc_2249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = l_Nat_reprFast(v_snd_2226_);
                v___x_2236_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                v___x_2237_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2237_, 0, v___x_2236_);
                lean_ctor_set(v___x_2237_, 1, v___x_2234_);
                v___x_2238_ = l_List_reverse___redArg(v___x_2237_);
                v___x_2239_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
                v___x_2240_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(v___x_2238_, v___x_2239_);
                v___x_2241_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4);
                v___x_2242_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5;
                v___x_2243_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2243_, 0, v___x_2242_);
                lean_ctor_set(v___x_2243_, 1, v___x_2240_);
                v___x_2244_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6;
                v___x_2245_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2245_, 0, v___x_2243_);
                lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                v___x_2246_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2246_, 0, v___x_2241_);
                lean_ctor_set(v___x_2246_, 1, v___x_2245_);
                v___x_2247_ = 0;
                v___x_2248_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2248_, 0, v___x_2246_);
                lean_ctor_set_uint8(
                    v___x_2248_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2247_,
                );
                return v___x_2248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(
    mut v_x_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
    mut v_x_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2253_) == 0 {
                    lean_dec(v_x_2251_);
                    return v_x_2252_;
                } else {
                    v_head_2254_ = lean_ctor_get(v_x_2253_, 0);
                    v_tail_2255_ = lean_ctor_get(v_x_2253_, 1);
                    v_isSharedCheck_2265_ = (!lean_is_exclusive(v_x_2253_)) as u8;
                    if v_isSharedCheck_2265_ == 0 {
                        v___x_2257_ = v_x_2253_;
                        v_isShared_2258_ = v_isSharedCheck_2265_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2255_);
                        lean_inc(v_head_2254_);
                        lean_dec(v_x_2253_);
                        v___x_2257_ = lean_box(0);
                        v_isShared_2258_ = v_isSharedCheck_2265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2251_);
                if v_isShared_2258_ == 0 {
                    lean_ctor_set_tag(v___x_2257_, 5);
                    lean_ctor_set(v___x_2257_, 1, v_x_2251_);
                    lean_ctor_set(v___x_2257_, 0, v_x_2252_);
                    v___x_2260_ = v___x_2257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_x_2252_);
                    lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_x_2251_);
                    v___x_2260_ = v_reuseFailAlloc_2264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2261_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2254_);
                v___x_2262_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2262_, 0, v___x_2260_);
                lean_ctor_set(v___x_2262_, 1, v___x_2261_);
                v_x_2252_ = v___x_2262_;
                v_x_2253_ = v_tail_2255_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(
    mut v_x_2266_: *mut LeanObject,
    mut v_x_2267_: *mut LeanObject,
    mut v_x_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2273_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2268_) == 0 {
                    lean_dec(v_x_2266_);
                    return v_x_2267_;
                } else {
                    v_head_2269_ = lean_ctor_get(v_x_2268_, 0);
                    v_tail_2270_ = lean_ctor_get(v_x_2268_, 1);
                    v_isSharedCheck_2280_ = (!lean_is_exclusive(v_x_2268_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2272_ = v_x_2268_;
                        v_isShared_2273_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2270_);
                        lean_inc(v_head_2269_);
                        lean_dec(v_x_2268_);
                        v___x_2272_ = lean_box(0);
                        v_isShared_2273_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2266_);
                if v_isShared_2273_ == 0 {
                    lean_ctor_set_tag(v___x_2272_, 5);
                    lean_ctor_set(v___x_2272_, 1, v_x_2266_);
                    lean_ctor_set(v___x_2272_, 0, v_x_2267_);
                    v___x_2275_ = v___x_2272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_x_2267_);
                    lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_x_2266_);
                    v___x_2275_ = v_reuseFailAlloc_2279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2276_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2269_);
                v___x_2277_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2277_, 0, v___x_2275_);
                lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(v_x_2266_, v___x_2277_, v_tail_2270_);
                return v___x_2278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(
    mut v_x_2281_: *mut LeanObject,
    mut v_x_2282_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2281_) == 0 {
        let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2282_);
        v___x_2283_ = lean_box(0);
        return v___x_2283_;
    } else {
        let mut v_tail_2284_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2284_ = lean_ctor_get(v_x_2281_, 1);
        if lean_obj_tag(v_tail_2284_) == 0 {
            let mut v_head_2285_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2282_);
            v_head_2285_ = lean_ctor_get(v_x_2281_, 0);
            lean_inc(v_head_2285_);
            lean_dec_ref_known(v_x_2281_, 2);
            v___x_2286_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2285_);
            return v___x_2286_;
        } else {
            let mut v_head_2287_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2284_);
            v_head_2287_ = lean_ctor_get(v_x_2281_, 0);
            lean_inc(v_head_2287_);
            lean_dec_ref_known(v_x_2281_, 2);
            v___x_2288_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2287_);
            v___x_2289_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(v_x_2282_, v___x_2288_, v_tail_2284_);
            return v___x_2289_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_2295_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2;
    v___x_2296_ = lean_string_length(v___x_2295_);
    return v___x_2296_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2297_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4);
    v___x_2298_ = lean_nat_to_int(v___x_2297_);
    return v___x_2298_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
    mut v_a_2303_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_2303_) == 0 {
        let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
        v___x_2304_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1;
        return v___x_2304_;
    } else {
        let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: u8 = 0;
        let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
        v___x_2305_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
        v___x_2306_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(v_a_2303_, v___x_2305_);
        v___x_2307_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once), _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5);
        v___x_2308_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6;
        v___x_2309_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2309_, 0, v___x_2308_);
        lean_ctor_set(v___x_2309_, 1, v___x_2306_);
        v___x_2310_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7;
        v___x_2311_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2311_, 0, v___x_2309_);
        lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        v___x_2312_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2312_, 0, v___x_2307_);
        lean_ctor_set(v___x_2312_, 1, v___x_2311_);
        v___x_2313_ = 0;
        v___x_2314_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_2314_, 0, v___x_2312_);
        lean_ctor_set_uint8(
            v___x_2314_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_2313_,
        );
        return v___x_2314_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(
    mut v_x_2315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_2316_: u8 = 0;
    let mut v_lhs_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v_eq_2316_ = lean_ctor_get_uint8(
        v_x_2315_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_lhs_2317_ = lean_ctor_get(v_x_2315_, 0);
    lean_inc(v_lhs_2317_);
    v_rhs_2318_ = lean_ctor_get(v_x_2315_, 1);
    lean_inc(v_rhs_2318_);
    lean_dec_ref(v_x_2315_);
    v___x_2319_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
    v___x_2320_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
    v___x_2321_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7,
    );
    v___x_2322_ = l_Bool_repr___redArg(v_eq_2316_);
    v___x_2323_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2323_, 0, v___x_2321_);
    lean_ctor_set(v___x_2323_, 1, v___x_2322_);
    v___x_2324_ = 0;
    v___x_2325_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2325_, 0, v___x_2323_);
    lean_ctor_set_uint8(
        v___x_2325_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2326_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2326_, 0, v___x_2320_);
    lean_ctor_set(v___x_2326_, 1, v___x_2325_);
    v___x_2327_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
    v___x_2328_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2328_, 0, v___x_2326_);
    lean_ctor_set(v___x_2328_, 1, v___x_2327_);
    v___x_2329_ = lean_box(1);
    v___x_2330_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2330_, 0, v___x_2328_);
    lean_ctor_set(v___x_2330_, 1, v___x_2329_);
    v___x_2331_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
    v___x_2332_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2332_, 0, v___x_2330_);
    lean_ctor_set(v___x_2332_, 1, v___x_2331_);
    v___x_2333_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    lean_ctor_set(v___x_2333_, 1, v___x_2319_);
    v___x_2334_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12,
    );
    v___x_2335_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_lhs_2317_,
        );
    v___x_2336_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2336_, 0, v___x_2334_);
    lean_ctor_set(v___x_2336_, 1, v___x_2335_);
    v___x_2337_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    lean_ctor_set_uint8(
        v___x_2337_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2338_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2338_, 0, v___x_2333_);
    lean_ctor_set(v___x_2338_, 1, v___x_2337_);
    v___x_2339_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2339_, 0, v___x_2338_);
    lean_ctor_set(v___x_2339_, 1, v___x_2327_);
    v___x_2340_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2340_, 0, v___x_2339_);
    lean_ctor_set(v___x_2340_, 1, v___x_2329_);
    v___x_2341_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
    v___x_2342_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2342_, 0, v___x_2340_);
    lean_ctor_set(v___x_2342_, 1, v___x_2341_);
    v___x_2343_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2343_, 0, v___x_2342_);
    lean_ctor_set(v___x_2343_, 1, v___x_2319_);
    v___x_2344_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_rhs_2318_,
        );
    v___x_2345_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2345_, 0, v___x_2334_);
    lean_ctor_set(v___x_2345_, 1, v___x_2344_);
    v___x_2346_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2346_, 0, v___x_2345_);
    lean_ctor_set_uint8(
        v___x_2346_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2347_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2347_, 0, v___x_2343_);
    lean_ctor_set(v___x_2347_, 1, v___x_2346_);
    v___x_2348_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17,
    );
    v___x_2349_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
    v___x_2350_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    lean_ctor_set(v___x_2350_, 1, v___x_2347_);
    v___x_2351_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
    v___x_2352_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2352_, 0, v___x_2350_);
    lean_ctor_set(v___x_2352_, 1, v___x_2351_);
    v___x_2353_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2353_, 0, v___x_2348_);
    lean_ctor_set(v___x_2353_, 1, v___x_2352_);
    v___x_2354_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    lean_ctor_set_uint8(
        v___x_2354_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    return v___x_2354_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(
    mut v_x_2355_: *mut LeanObject,
    mut v_prec_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2357_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(v_x_2355_);
    return v___x_2357_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(
    mut v_x_2358_: *mut LeanObject,
    mut v_prec_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(v_x_2358_, v_prec_2359_);
    lean_dec(v_prec_2359_);
    return v_res_2360_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(
    mut v_a_2361_: *mut LeanObject,
    mut v_n_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    v___x_2363_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_a_2361_,
        );
    return v___x_2363_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(
    mut v_a_2364_: *mut LeanObject,
    mut v_n_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_res_2366_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(
            v_a_2364_, v_n_2365_,
        );
    lean_dec(v_n_2365_);
    return v_res_2366_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(
    mut v_x_2367_: *mut LeanObject,
    mut v_x_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_x_2367_);
    return v___x_2369_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(
    mut v_x_2370_: *mut LeanObject,
    mut v_x_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2372_: *mut LeanObject = core::ptr::null_mut();
    v_res_2372_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(v_x_2370_, v_x_2371_);
    lean_dec(v_x_2371_);
    return v_res_2372_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5() -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = lean_box(0);
    v___x_2385_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4;
    v___x_2386_ = l_Lean_mkConst(v___x_2385_, v___x_2384_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8() -> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    v___x_2393_ = lean_box(0);
    v___x_2394_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7;
    v___x_2395_ = l_Lean_mkConst(v___x_2394_, v___x_2393_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11() -> *mut LeanObject {
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_2402_ = lean_box(0);
    v___x_2403_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10;
    v___x_2404_ = l_Lean_mkConst(v___x_2403_, v___x_2402_);
    return v___x_2404_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14() -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = lean_box(0);
    v___x_2412_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13;
    v___x_2413_ = l_Lean_mkConst(v___x_2412_, v___x_2411_);
    return v___x_2413_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17() -> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    v___x_2420_ = lean_box(0);
    v___x_2421_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16;
    v___x_2422_ = l_Lean_mkConst(v___x_2421_, v___x_2420_);
    return v___x_2422_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(
    mut v_e_2423_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_2423_) {
        0 => {
            let mut v_v_2424_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
            v_v_2424_ = lean_ctor_get(v_e_2423_, 0);
            lean_inc(v_v_2424_);
            lean_dec_ref_known(v_e_2423_, 1);
            v___x_2425_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5,
            );
            v___x_2426_ = l_Lean_mkNatLit(v_v_2424_);
            v___x_2427_ = l_Lean_Expr_app___override(v___x_2425_, v___x_2426_);
            return v___x_2427_;
        }
        1 => {
            let mut v_i_2428_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
            v_i_2428_ = lean_ctor_get(v_e_2423_, 0);
            lean_inc(v_i_2428_);
            lean_dec_ref_known(v_e_2423_, 1);
            v___x_2429_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8,
            );
            v___x_2430_ = l_Lean_mkNatLit(v_i_2428_);
            v___x_2431_ = l_Lean_Expr_app___override(v___x_2429_, v___x_2430_);
            return v___x_2431_;
        }
        2 => {
            let mut v_a_2432_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_2433_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
            v_a_2432_ = lean_ctor_get(v_e_2423_, 0);
            lean_inc_ref(v_a_2432_);
            v_b_2433_ = lean_ctor_get(v_e_2423_, 1);
            lean_inc_ref(v_b_2433_);
            lean_dec_ref_known(v_e_2423_, 2);
            v___x_2434_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11,
            );
            v___x_2435_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2432_);
            v___x_2436_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_b_2433_);
            v___x_2437_ = l_Lean_mkAppB(v___x_2434_, v___x_2435_, v___x_2436_);
            return v___x_2437_;
        }
        3 => {
            let mut v_k_2438_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
            v_k_2438_ = lean_ctor_get(v_e_2423_, 0);
            lean_inc(v_k_2438_);
            v_a_2439_ = lean_ctor_get(v_e_2423_, 1);
            lean_inc_ref(v_a_2439_);
            lean_dec_ref_known(v_e_2423_, 2);
            v___x_2440_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14,
            );
            v___x_2441_ = l_Lean_mkNatLit(v_k_2438_);
            v___x_2442_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2439_);
            v___x_2443_ = l_Lean_mkAppB(v___x_2440_, v___x_2441_, v___x_2442_);
            return v___x_2443_;
        }
        _ => {
            let mut v_a_2444_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
            v_a_2444_ = lean_ctor_get(v_e_2423_, 0);
            lean_inc_ref(v_a_2444_);
            v_k_2445_ = lean_ctor_get(v_e_2423_, 1);
            lean_inc(v_k_2445_);
            lean_dec_ref_known(v_e_2423_, 2);
            v___x_2446_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17,
            );
            v___x_2447_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2444_);
            v___x_2448_ = l_Lean_mkNatLit(v_k_2445_);
            v___x_2449_ = l_Lean_mkAppB(v___x_2446_, v___x_2447_, v___x_2448_);
            return v___x_2449_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2() -> *mut LeanObject
{
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = lean_box(0);
    v___x_2456_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
    v___x_2457_ = l_Lean_mkConst(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3() -> *mut LeanObject
{
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2458_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2,
    );
    v___f_2459_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
    v___x_2460_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2460_, 0, v___f_2459_);
    lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr() -> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    v___x_2461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3,
    );
    return v___x_2461_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3() -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = lean_box(0);
    v___x_2470_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2;
    v___x_2471_ = l_Lean_mkConst(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7() -> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_box(0);
    v___x_2478_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6;
    v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10() -> *mut LeanObject
{
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = lean_box(0);
    v___x_2485_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9;
    v___x_2486_ = l_Lean_mkConst(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(
    mut v_c_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_2488_: u8 = 0;
    let mut v_lhs_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_2488_ = lean_ctor_get_uint8(
                    v_c_2487_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_lhs_2489_ = lean_ctor_get(v_c_2487_, 0);
                lean_inc_ref(v_lhs_2489_);
                v_rhs_2490_ = lean_ctor_get(v_c_2487_, 1);
                lean_inc_ref(v_rhs_2490_);
                lean_dec_ref(v_c_2487_);
                v___x_2491_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3,
                );
                if v_eq_2488_ == 0 {
                    v___x_2497_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7,
                    );
                    v___y_2493_ = v___x_2497_;
                    state = 1;
                    continue;
                } else {
                    v___x_2498_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10,
                    );
                    v___y_2493_ = v___x_2498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2494_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_lhs_2489_);
                v___x_2495_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_rhs_2490_);
                lean_inc_ref(v___y_2493_);
                v___x_2496_ = l_Lean_mkApp3(v___x_2491_, v___y_2493_, v___x_2494_, v___x_2495_);
                return v___x_2496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2() -> *mut LeanObject
{
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    v___x_2504_ = lean_box(0);
    v___x_2505_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
    v___x_2506_ = l_Lean_mkConst(v___x_2505_, v___x_2504_);
    return v___x_2506_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3() -> *mut LeanObject
{
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    v___x_2507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2,
    );
    v___f_2508_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
    v___x_2509_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2509_, 0, v___f_2508_);
    lean_ctor_set(v___x_2509_, 1, v___x_2507_);
    return v___x_2509_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr() -> *mut LeanObject {
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    v___x_2510_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3,
    );
    return v___x_2510_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
    mut v_ctx_2511_: *mut LeanObject,
    mut v_e_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_i_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_k_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_a_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2512_) {
                0 => {
                    v_v_2514_ = lean_ctor_get(v_e_2512_, 0);
                    v_isSharedCheck_2522_ = (!lean_is_exclusive(v_e_2512_)) as u8;
                    if v_isSharedCheck_2522_ == 0 {
                        v___x_2516_ = v_e_2512_;
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2514_);
                        lean_dec(v_e_2512_);
                        v___x_2516_ = lean_box(0);
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_2523_ = lean_ctor_get(v_e_2512_, 0);
                    v_isSharedCheck_2532_ = (!lean_is_exclusive(v_e_2512_)) as u8;
                    if v_isSharedCheck_2532_ == 0 {
                        v___x_2525_ = v_e_2512_;
                        v_isShared_2526_ = v_isSharedCheck_2532_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_i_2523_);
                        lean_dec(v_e_2512_);
                        v___x_2525_ = lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2532_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_2533_ = lean_ctor_get(v_e_2512_, 0);
                    lean_inc_ref(v_a_2533_);
                    v_b_2534_ = lean_ctor_get(v_e_2512_, 1);
                    lean_inc_ref(v_b_2534_);
                    lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2535_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2533_,
                    );
                    v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
                    lean_inc(v_a_2536_);
                    lean_dec_ref(v___x_2535_);
                    v___x_2537_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_b_2534_,
                    );
                    v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
                    v_isSharedCheck_2546_ = (!lean_is_exclusive(v___x_2537_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v___x_2540_ = v___x_2537_;
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2538_);
                        lean_dec(v___x_2537_);
                        v___x_2540_ = lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_k_2547_ = lean_ctor_get(v_e_2512_, 0);
                    lean_inc(v_k_2547_);
                    v_a_2548_ = lean_ctor_get(v_e_2512_, 1);
                    lean_inc_ref(v_a_2548_);
                    lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2549_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2548_,
                    );
                    v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2559_ = (!lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2552_ = v___x_2549_;
                        v_isShared_2553_ = v_isSharedCheck_2559_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2550_);
                        lean_dec(v___x_2549_);
                        v___x_2552_ = lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2559_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_a_2560_ = lean_ctor_get(v_e_2512_, 0);
                    lean_inc_ref(v_a_2560_);
                    v_k_2561_ = lean_ctor_get(v_e_2512_, 1);
                    lean_inc(v_k_2561_);
                    lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2562_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2560_,
                    );
                    v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
                    v_isSharedCheck_2572_ = (!lean_is_exclusive(v___x_2562_)) as u8;
                    if v_isSharedCheck_2572_ == 0 {
                        v___x_2565_ = v___x_2562_;
                        v_isShared_2566_ = v_isSharedCheck_2572_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2563_);
                        lean_dec(v___x_2562_);
                        v___x_2565_ = lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2572_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2518_ = l_Lean_mkNatLit(v_v_2514_);
                if v_isShared_2517_ == 0 {
                    lean_ctor_set(v___x_2516_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2520_;
            }
            3 => {
                v___x_2527_ = l_Lean_instInhabitedExpr;
                v___x_2528_ = lean_array_get_borrowed(v___x_2527_, v_ctx_2511_, v_i_2523_);
                lean_dec(v_i_2523_);
                lean_inc(v___x_2528_);
                if v_isShared_2526_ == 0 {
                    lean_ctor_set_tag(v___x_2525_, 0);
                    lean_ctor_set(v___x_2525_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2530_;
            }
            5 => {
                v___x_2542_ = l_Lean_mkNatAdd(v_a_2536_, v_a_2538_);
                if v_isShared_2541_ == 0 {
                    lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2544_ = v___x_2540_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2544_;
            }
            7 => {
                v___x_2554_ = l_Lean_mkNatLit(v_k_2547_);
                v___x_2555_ = l_Lean_mkNatMul(v___x_2554_, v_a_2550_);
                if v_isShared_2553_ == 0 {
                    lean_ctor_set(v___x_2552_, 0, v___x_2555_);
                    v___x_2557_ = v___x_2552_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2557_;
            }
            9 => {
                v___x_2567_ = l_Lean_mkNatLit(v_k_2561_);
                v___x_2568_ = l_Lean_mkNatMul(v_a_2563_, v___x_2567_);
                if v_isShared_2566_ == 0 {
                    lean_ctor_set(v___x_2565_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2565_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2571_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(
    mut v_ctx_2573_: *mut LeanObject,
    mut v_e_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2576_: *mut LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_2573_, v_e_2574_);
    lean_dec_ref(v_ctx_2573_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(
    mut v_ctx_2577_: *mut LeanObject,
    mut v_e_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_2577_, v_e_2578_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(
    mut v_ctx_2585_: *mut LeanObject,
    mut v_e_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2592_: *mut LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(
        v_ctx_2585_,
        v_e_2586_,
        v_a_2587_,
        v_a_2588_,
        v_a_2589_,
        v_a_2590_,
    );
    lean_dec(v_a_2590_);
    lean_dec_ref(v_a_2589_);
    lean_dec(v_a_2588_);
    lean_dec_ref(v_a_2587_);
    lean_dec_ref(v_ctx_2585_);
    return v_res_2592_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(
    mut v_ctx_2593_: *mut LeanObject,
    mut v_c_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_2596_: u8 = 0;
    let mut v_lhs_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut v_lhs_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_2596_ = lean_ctor_get_uint8(
                    v_c_2594_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_eq_2596_ == 0 {
                    v_lhs_2597_ = lean_ctor_get(v_c_2594_, 0);
                    lean_inc_ref(v_lhs_2597_);
                    v_rhs_2598_ = lean_ctor_get(v_c_2594_, 1);
                    lean_inc_ref(v_rhs_2598_);
                    lean_dec_ref(v_c_2594_);
                    v___x_2599_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_lhs_2597_,
                    );
                    v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
                    lean_inc(v_a_2600_);
                    lean_dec_ref(v___x_2599_);
                    v___x_2601_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_rhs_2598_,
                    );
                    v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
                    v_isSharedCheck_2610_ = (!lean_is_exclusive(v___x_2601_)) as u8;
                    if v_isSharedCheck_2610_ == 0 {
                        v___x_2604_ = v___x_2601_;
                        v_isShared_2605_ = v_isSharedCheck_2610_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2602_);
                        lean_dec(v___x_2601_);
                        v___x_2604_ = lean_box(0);
                        v_isShared_2605_ = v_isSharedCheck_2610_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_2611_ = lean_ctor_get(v_c_2594_, 0);
                    lean_inc_ref(v_lhs_2611_);
                    v_rhs_2612_ = lean_ctor_get(v_c_2594_, 1);
                    lean_inc_ref(v_rhs_2612_);
                    lean_dec_ref(v_c_2594_);
                    v___x_2613_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_lhs_2611_,
                    );
                    v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
                    lean_inc(v_a_2614_);
                    lean_dec_ref(v___x_2613_);
                    v___x_2615_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_rhs_2612_,
                    );
                    v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
                    v_isSharedCheck_2624_ = (!lean_is_exclusive(v___x_2615_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2618_ = v___x_2615_;
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2616_);
                        lean_dec(v___x_2615_);
                        v___x_2618_ = lean_box(0);
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2606_ = l_Lean_mkNatLE(v_a_2600_, v_a_2602_);
                if v_isShared_2605_ == 0 {
                    lean_ctor_set(v___x_2604_, 0, v___x_2606_);
                    v___x_2608_ = v___x_2604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
                    v___x_2608_ = v_reuseFailAlloc_2609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2608_;
            }
            3 => {
                v___x_2620_ = l_Lean_mkNatEq(v_a_2614_, v_a_2616_);
                if v_isShared_2619_ == 0 {
                    lean_ctor_set(v___x_2618_, 0, v___x_2620_);
                    v___x_2622_ = v___x_2618_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(
    mut v_ctx_2625_: *mut LeanObject,
    mut v_c_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2628_: *mut LeanObject = core::ptr::null_mut();
    v_res_2628_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_2625_, v_c_2626_);
    lean_dec_ref(v_ctx_2625_);
    return v_res_2628_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(
    mut v_ctx_2629_: *mut LeanObject,
    mut v_c_2630_: *mut LeanObject,
    mut v_a_2631_: *mut LeanObject,
    mut v_a_2632_: *mut LeanObject,
    mut v_a_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_2629_, v_c_2630_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(
    mut v_ctx_2637_: *mut LeanObject,
    mut v_c_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2644_: *mut LeanObject = core::ptr::null_mut();
    v_res_2644_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(
        v_ctx_2637_,
        v_c_2638_,
        v_a_2639_,
        v_a_2640_,
        v_a_2641_,
        v_a_2642_,
    );
    lean_dec(v_a_2642_);
    lean_dec_ref(v_a_2641_);
    lean_dec(v_a_2640_);
    lean_dec_ref(v_a_2639_);
    lean_dec_ref(v_ctx_2637_);
    return v_res_2644_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
    mut v_e_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v_val_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_a_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_a_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_st_ref_get(v_a_2646_);
                v_varMap_2653_ = lean_ctor_get(v___x_2652_, 0);
                lean_inc_ref(v_varMap_2653_);
                lean_dec(v___x_2652_);
                lean_inc_ref(v_e_2645_);
                v___x_2654_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
                    v_varMap_2653_,
                    v_e_2645_,
                    v_a_2647_,
                    v_a_2648_,
                    v_a_2649_,
                    v_a_2650_,
                );
                lean_dec_ref(v_varMap_2653_);
                if lean_obj_tag(v___x_2654_) == 0 {
                    v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
                    v_isSharedCheck_2703_ = (!lean_is_exclusive(v___x_2654_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2657_ = v___x_2654_;
                        v_isShared_2658_ = v_isSharedCheck_2703_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2655_);
                        lean_dec(v___x_2654_);
                        v___x_2657_ = lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2703_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2645_);
                    v_a_2704_ = lean_ctor_get(v___x_2654_, 0);
                    v_isSharedCheck_2711_ = (!lean_is_exclusive(v___x_2654_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2706_ = v___x_2654_;
                        v_isShared_2707_ = v_isSharedCheck_2711_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2704_);
                        lean_dec(v___x_2654_);
                        v___x_2706_ = lean_box(0);
                        v_isShared_2707_ = v_isSharedCheck_2711_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2655_) == 1 {
                    lean_dec_ref(v_e_2645_);
                    v_val_2659_ = lean_ctor_get(v_a_2655_, 0);
                    v_isSharedCheck_2669_ = (!lean_is_exclusive(v_a_2655_)) as u8;
                    if v_isSharedCheck_2669_ == 0 {
                        v___x_2661_ = v_a_2655_;
                        v_isShared_2662_ = v_isSharedCheck_2669_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2659_);
                        lean_dec(v_a_2655_);
                        v___x_2661_ = lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2669_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2657_);
                    lean_dec(v_a_2655_);
                    v___x_2670_ = lean_st_ref_get(v_a_2646_);
                    v___x_2671_ = lean_st_ref_get(v_a_2646_);
                    v_vars_2672_ = lean_ctor_get(v___x_2670_, 1);
                    lean_inc_ref(v_vars_2672_);
                    lean_dec(v___x_2670_);
                    v_varMap_2673_ = lean_ctor_get(v___x_2671_, 0);
                    v_vars_2674_ = lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2702_ = (!lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2676_ = v___x_2671_;
                        v_isShared_2677_ = v_isSharedCheck_2702_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_vars_2674_);
                        lean_inc(v_varMap_2673_);
                        lean_dec(v___x_2671_);
                        v___x_2676_ = lean_box(0);
                        v_isShared_2677_ = v_isSharedCheck_2702_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2662_ == 0 {
                    v___x_2664_ = v___x_2661_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_val_2659_);
                    v___x_2664_ = v_reuseFailAlloc_2668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2658_ == 0 {
                    lean_ctor_set(v___x_2657_, 0, v___x_2664_);
                    v___x_2666_ = v___x_2657_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2666_;
            }
            5 => {
                v___x_2678_ = lean_array_get_size(v_vars_2672_);
                lean_dec_ref(v_vars_2672_);
                lean_inc_ref(v_e_2645_);
                v___x_2679_ = l_Lean_Meta_KExprMap_insert___redArg(
                    v_varMap_2673_,
                    v_e_2645_,
                    v___x_2678_,
                    v_a_2647_,
                    v_a_2648_,
                    v_a_2649_,
                    v_a_2650_,
                );
                if lean_obj_tag(v___x_2679_) == 0 {
                    v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2693_ = (!lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2682_ = v___x_2679_;
                        v_isShared_2683_ = v_isSharedCheck_2693_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2680_);
                        lean_dec(v___x_2679_);
                        v___x_2682_ = lean_box(0);
                        v_isShared_2683_ = v_isSharedCheck_2693_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2676_);
                    lean_dec_ref(v_vars_2674_);
                    lean_dec_ref(v_e_2645_);
                    v_a_2694_ = lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2701_ = (!lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2701_ == 0 {
                        v___x_2696_ = v___x_2679_;
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2694_);
                        lean_dec(v___x_2679_);
                        v___x_2696_ = lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2684_ = lean_array_push(v_vars_2674_, v_e_2645_);
                if v_isShared_2677_ == 0 {
                    lean_ctor_set(v___x_2676_, 1, v___x_2684_);
                    lean_ctor_set(v___x_2676_, 0, v_a_2680_);
                    v___x_2686_ = v___x_2676_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2680_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2684_);
                    v___x_2686_ = v_reuseFailAlloc_2692_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2687_ = lean_st_ref_set(v_a_2646_, v___x_2686_);
                v___x_2688_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2688_, 0, v___x_2678_);
                if v_isShared_2683_ == 0 {
                    lean_ctor_set(v___x_2682_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2682_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2690_;
            }
            9 => {
                if v_isShared_2697_ == 0 {
                    v___x_2699_ = v___x_2696_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
                    v___x_2699_ = v_reuseFailAlloc_2700_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2699_;
            }
            11 => {
                if v_isShared_2707_ == 0 {
                    v___x_2709_ = v___x_2706_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(
    mut v_e_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
        v_e_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_,
    );
    lean_dec(v_a_2717_);
    lean_dec_ref(v_a_2716_);
    lean_dec(v_a_2715_);
    lean_dec_ref(v_a_2714_);
    lean_dec(v_a_2713_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(
    mut v_e_2757_: *mut LeanObject,
    mut v_a_2758_: *mut LeanObject,
    mut v_a_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
    mut v_a_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_val_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_a_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2825_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2890_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_a_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v_a_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2757_);
                v___x_2764_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2757_, v_a_2760_);
                if lean_obj_tag(v___x_2764_) == 0 {
                    v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
                    lean_inc(v_a_2765_);
                    lean_dec_ref_known(v___x_2764_, 1);
                    v___x_2766_ = l_Lean_Expr_cleanupAnnotations(v_a_2765_);
                    v___x_2767_ = l_Lean_Expr_isApp(v___x_2766_);
                    if v___x_2767_ == 0 {
                        lean_dec_ref(v___x_2766_);
                        v___x_2768_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_,
                        );
                        return v___x_2768_;
                    } else {
                        v_arg_2769_ = lean_ctor_get(v___x_2766_, 1);
                        lean_inc_ref(v_arg_2769_);
                        v___x_2770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2766_);
                        v___x_2771_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
                        v___x_2772_ = l_Lean_Expr_isConstOf(v___x_2770_, v___x_2771_);
                        if v___x_2772_ == 0 {
                            v___x_2773_ = l_Lean_Expr_isApp(v___x_2770_);
                            if v___x_2773_ == 0 {
                                lean_dec_ref(v___x_2770_);
                                lean_dec_ref(v_arg_2769_);
                                v___x_2774_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_,
                                    v_a_2762_,
                                );
                                return v___x_2774_;
                            } else {
                                v_arg_2775_ = lean_ctor_get(v___x_2770_, 1);
                                lean_inc_ref(v_arg_2775_);
                                v___x_2826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2770_);
                                v___x_2827_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
                                v___x_2828_ = l_Lean_Expr_isConstOf(v___x_2826_, v___x_2827_);
                                if v___x_2828_ == 0 {
                                    v___x_2829_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
                                    v___x_2830_ = l_Lean_Expr_isConstOf(v___x_2826_, v___x_2829_);
                                    if v___x_2830_ == 0 {
                                        v___x_2831_ = l_Lean_Expr_isApp(v___x_2826_);
                                        if v___x_2831_ == 0 {
                                            lean_dec_ref(v___x_2826_);
                                            lean_dec_ref(v_arg_2775_);
                                            lean_dec_ref(v_arg_2769_);
                                            v___x_2832_ =
                                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                                    v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_,
                                                    v_a_2761_, v_a_2762_,
                                                );
                                            return v___x_2832_;
                                        } else {
                                            v_arg_2833_ = lean_ctor_get(v___x_2826_, 1);
                                            lean_inc_ref(v_arg_2833_);
                                            v___x_2834_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2826_);
                                            v___x_2835_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
                                            v___x_2836_ =
                                                l_Lean_Expr_isConstOf(v___x_2834_, v___x_2835_);
                                            if v___x_2836_ == 0 {
                                                v___x_2837_ = l_Lean_Expr_isApp(v___x_2834_);
                                                if v___x_2837_ == 0 {
                                                    lean_dec_ref(v___x_2834_);
                                                    lean_dec_ref(v_arg_2833_);
                                                    lean_dec_ref(v_arg_2775_);
                                                    lean_dec_ref(v_arg_2769_);
                                                    v___x_2838_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                    return v___x_2838_;
                                                } else {
                                                    v___x_2839_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2834_,
                                                    );
                                                    v___x_2840_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
                                                    v___x_2841_ = l_Lean_Expr_isConstOf(
                                                        v___x_2839_,
                                                        v___x_2840_,
                                                    );
                                                    if v___x_2841_ == 0 {
                                                        v___x_2842_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
                                                        v___x_2843_ = l_Lean_Expr_isConstOf(
                                                            v___x_2839_,
                                                            v___x_2842_,
                                                        );
                                                        if v___x_2843_ == 0 {
                                                            v___x_2844_ =
                                                                l_Lean_Expr_isApp(v___x_2839_);
                                                            if v___x_2844_ == 0 {
                                                                lean_dec_ref(v___x_2839_);
                                                                lean_dec_ref(v_arg_2833_);
                                                                lean_dec_ref(v_arg_2775_);
                                                                lean_dec_ref(v_arg_2769_);
                                                                v___x_2845_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2845_;
                                                            } else {
                                                                v___x_2846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2839_);
                                                                v___x_2847_ =
                                                                    l_Lean_Expr_isApp(v___x_2846_);
                                                                if v___x_2847_ == 0 {
                                                                    lean_dec_ref(v___x_2846_);
                                                                    lean_dec_ref(v_arg_2833_);
                                                                    lean_dec_ref(v_arg_2775_);
                                                                    lean_dec_ref(v_arg_2769_);
                                                                    v___x_2848_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    return v___x_2848_;
                                                                } else {
                                                                    v___x_2849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2846_);
                                                                    v___x_2850_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
                                                                    v___x_2851_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2849_,
                                                                            v___x_2850_,
                                                                        );
                                                                    if v___x_2851_ == 0 {
                                                                        v___x_2852_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
                                                                        v___x_2853_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_2849_,
                                                                                v___x_2852_,
                                                                            );
                                                                        lean_dec_ref(v___x_2849_);
                                                                        if v___x_2853_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_2833_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2775_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2769_,
                                                                            );
                                                                            v___x_2854_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                            return v___x_2854_;
                                                                        } else {
                                                                            v___x_2855_ = l_Lean_Meta_DefEq_isInstHAddNat(v_arg_2833_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                            if lean_obj_tag(
                                                                                v___x_2855_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_2856_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2855_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_a_2856_);
                                                                                lean_dec_ref_known(
                                                                                    v___x_2855_,
                                                                                    1,
                                                                                );
                                                                                v___x_2857_ =
                                                                                    (lean_unbox(
                                                                                        v_a_2856_,
                                                                                    )
                                                                                        as u8);
                                                                                lean_dec(v_a_2856_);
                                                                                if v___x_2857_ == 0
                                                                                {
                                                                                    lean_dec_ref(
                                                                                        v_arg_2775_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_2769_,
                                                                                    );
                                                                                    v___x_2858_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                                    return v___x_2858_;
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_e_2757_,
                                                                                    );
                                                                                    v___x_2859_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_2859_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
                                                                                        lean_inc(v_a_2860_);
                                                                                        lean_dec_ref_known(v___x_2859_, 1);
                                                                                        v___x_2861_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2769_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                                        if lean_obj_tag(v___x_2861_) == 0 {
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2870_ = (!lean_is_exclusive(v___x_2861_)) as u8;
if v_isSharedCheck_2870_ == 0 {
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2870_;
state = 10; continue;
} else {
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2870_;
state = 10; continue;
}
} else {
lean_dec(v_a_2860_);
return v___x_2861_;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_arg_2769_);
                                                                                        return v___x_2859_;
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_2775_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2769_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_e_2757_,
                                                                                );
                                                                                v_a_2871_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2855_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_2878_ = (!lean_is_exclusive(v___x_2855_)) as u8;
                                                                                if v_isSharedCheck_2878_ == 0 {
v___x_2873_ = v___x_2855_;
v_isShared_2874_ = v_isSharedCheck_2878_;
state = 12; continue;
} else {
lean_inc(v_a_2871_);
lean_dec(v___x_2855_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
state = 12; continue;
}
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_2849_);
                                                                        v___x_2879_ = l_Lean_Meta_DefEq_isInstHMulNat(v_arg_2833_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                        if lean_obj_tag(v___x_2879_)
                                                                            == 0
                                                                        {
                                                                            v_a_2880_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2879_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_2880_);
                                                                            lean_dec_ref_known(
                                                                                v___x_2879_,
                                                                                1,
                                                                            );
                                                                            v___x_2881_ =
                                                                                (lean_unbox(
                                                                                    v_a_2880_,
                                                                                )
                                                                                    as u8);
                                                                            lean_dec(v_a_2880_);
                                                                            if v___x_2881_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_2775_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2769_,
                                                                                );
                                                                                v___x_2882_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                                return v___x_2882_;
                                                                            } else {
                                                                                v_b_2777_ =
                                                                                    v_arg_2769_;
                                                                                v___y_2778_ =
                                                                                    v_a_2758_;
                                                                                v___y_2779_ =
                                                                                    v_a_2759_;
                                                                                v___y_2780_ =
                                                                                    v_a_2760_;
                                                                                v___y_2781_ =
                                                                                    v_a_2761_;
                                                                                v___y_2782_ =
                                                                                    v_a_2762_;
                                                                                state = 1;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_2775_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2769_,
                                                                            );
                                                                            lean_dec_ref(v_e_2757_);
                                                                            v_a_2883_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2879_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2890_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2879_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2890_
                                                                                == 0
                                                                            {
                                                                                v___x_2885_ =
                                                                                    v___x_2879_;
                                                                                v_isShared_2886_ = v_isSharedCheck_2890_;
                                                                                state = 14;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2883_);
                                                                                lean_dec(
                                                                                    v___x_2879_,
                                                                                );
                                                                                v___x_2885_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2886_ = v_isSharedCheck_2890_;
                                                                                state = 14;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_2839_);
                                                            v___x_2891_ =
                                                                l_Lean_Meta_DefEq_isInstAddNat(
                                                                    v_arg_2833_,
                                                                    v_a_2759_,
                                                                    v_a_2760_,
                                                                    v_a_2761_,
                                                                    v_a_2762_,
                                                                );
                                                            if lean_obj_tag(v___x_2891_) == 0 {
                                                                v_a_2892_ =
                                                                    lean_ctor_get(v___x_2891_, 0);
                                                                lean_inc(v_a_2892_);
                                                                lean_dec_ref_known(v___x_2891_, 1);
                                                                v___x_2893_ =
                                                                    (lean_unbox(v_a_2892_) as u8);
                                                                lean_dec(v_a_2892_);
                                                                if v___x_2893_ == 0 {
                                                                    lean_dec_ref(v_arg_2775_);
                                                                    lean_dec_ref(v_arg_2769_);
                                                                    v___x_2894_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    return v___x_2894_;
                                                                } else {
                                                                    lean_dec_ref(v_e_2757_);
                                                                    v___x_2895_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    if lean_obj_tag(v___x_2895_)
                                                                        == 0
                                                                    {
                                                                        v_a_2896_ = lean_ctor_get(
                                                                            v___x_2895_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_2896_);
                                                                        lean_dec_ref_known(
                                                                            v___x_2895_,
                                                                            1,
                                                                        );
                                                                        v___x_2897_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2769_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                        if lean_obj_tag(v___x_2897_)
                                                                            == 0
                                                                        {
                                                                            v_a_2898_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2897_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2906_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2897_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2906_
                                                                                == 0
                                                                            {
                                                                                v___x_2900_ =
                                                                                    v___x_2897_;
                                                                                v_isShared_2901_ = v_isSharedCheck_2906_;
                                                                                state = 16;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2898_);
                                                                                lean_dec(
                                                                                    v___x_2897_,
                                                                                );
                                                                                v___x_2900_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2901_ = v_isSharedCheck_2906_;
                                                                                state = 16;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec(v_a_2896_);
                                                                            return v___x_2897_;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_2769_);
                                                                        return v___x_2895_;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_2775_);
                                                                lean_dec_ref(v_arg_2769_);
                                                                lean_dec_ref(v_e_2757_);
                                                                v_a_2907_ =
                                                                    lean_ctor_get(v___x_2891_, 0);
                                                                v_isSharedCheck_2914_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2891_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2914_ == 0 {
                                                                    v___x_2909_ = v___x_2891_;
                                                                    v_isShared_2910_ =
                                                                        v_isSharedCheck_2914_;
                                                                    state = 18;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_2907_);
                                                                    lean_dec(v___x_2891_);
                                                                    v___x_2909_ = lean_box(0);
                                                                    v_isShared_2910_ =
                                                                        v_isSharedCheck_2914_;
                                                                    state = 18;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_2839_);
                                                        v___x_2915_ =
                                                            l_Lean_Meta_DefEq_isInstMulNat(
                                                                v_arg_2833_,
                                                                v_a_2759_,
                                                                v_a_2760_,
                                                                v_a_2761_,
                                                                v_a_2762_,
                                                            );
                                                        if lean_obj_tag(v___x_2915_) == 0 {
                                                            v_a_2916_ =
                                                                lean_ctor_get(v___x_2915_, 0);
                                                            lean_inc(v_a_2916_);
                                                            lean_dec_ref_known(v___x_2915_, 1);
                                                            v___x_2917_ =
                                                                (lean_unbox(v_a_2916_) as u8);
                                                            lean_dec(v_a_2916_);
                                                            if v___x_2917_ == 0 {
                                                                lean_dec_ref(v_arg_2775_);
                                                                lean_dec_ref(v_arg_2769_);
                                                                v___x_2918_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2918_;
                                                            } else {
                                                                v_b_2777_ = v_arg_2769_;
                                                                v___y_2778_ = v_a_2758_;
                                                                v___y_2779_ = v_a_2759_;
                                                                v___y_2780_ = v_a_2760_;
                                                                v___y_2781_ = v_a_2761_;
                                                                v___y_2782_ = v_a_2762_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_2775_);
                                                            lean_dec_ref(v_arg_2769_);
                                                            lean_dec_ref(v_e_2757_);
                                                            v_a_2919_ =
                                                                lean_ctor_get(v___x_2915_, 0);
                                                            v_isSharedCheck_2926_ =
                                                                (!lean_is_exclusive(v___x_2915_))
                                                                    as u8;
                                                            if v_isSharedCheck_2926_ == 0 {
                                                                v___x_2921_ = v___x_2915_;
                                                                v_isShared_2922_ =
                                                                    v_isSharedCheck_2926_;
                                                                state = 20;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2919_);
                                                                lean_dec(v___x_2915_);
                                                                v___x_2921_ = lean_box(0);
                                                                v_isShared_2922_ =
                                                                    v_isSharedCheck_2926_;
                                                                state = 20;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2834_);
                                                lean_dec_ref(v_arg_2833_);
                                                lean_inc_ref(v_arg_2769_);
                                                v___x_2927_ =
                                                    l_Lean_Meta_Structural_isInstOfNatNat___redArg(
                                                        v_arg_2769_,
                                                        v_a_2760_,
                                                    );
                                                if lean_obj_tag(v___x_2927_) == 0 {
                                                    v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
                                                    lean_inc(v_a_2928_);
                                                    lean_dec_ref_known(v___x_2927_, 1);
                                                    v___x_2929_ = (lean_unbox(v_a_2928_) as u8);
                                                    lean_dec(v_a_2928_);
                                                    if v___x_2929_ == 0 {
                                                        lean_inc_ref(v_arg_2775_);
                                                        v___x_2930_ =
                                                            l_Lean_mkInstOfNatNat(v_arg_2775_);
                                                        v___x_2931_ = l_Lean_Meta_isDefEqI(
                                                            v_arg_2769_,
                                                            v___x_2930_,
                                                            v_a_2759_,
                                                            v_a_2760_,
                                                            v_a_2761_,
                                                            v_a_2762_,
                                                        );
                                                        if lean_obj_tag(v___x_2931_) == 0 {
                                                            v_a_2932_ =
                                                                lean_ctor_get(v___x_2931_, 0);
                                                            lean_inc(v_a_2932_);
                                                            lean_dec_ref_known(v___x_2931_, 1);
                                                            v___x_2933_ =
                                                                (lean_unbox(v_a_2932_) as u8);
                                                            lean_dec(v_a_2932_);
                                                            if v___x_2933_ == 0 {
                                                                lean_dec_ref(v_arg_2775_);
                                                                v___x_2934_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2934_;
                                                            } else {
                                                                lean_dec_ref(v_e_2757_);
                                                                v___x_2935_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2935_;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_2775_);
                                                            lean_dec_ref(v_e_2757_);
                                                            v_a_2936_ =
                                                                lean_ctor_get(v___x_2931_, 0);
                                                            v_isSharedCheck_2943_ =
                                                                (!lean_is_exclusive(v___x_2931_))
                                                                    as u8;
                                                            if v_isSharedCheck_2943_ == 0 {
                                                                v___x_2938_ = v___x_2931_;
                                                                v_isShared_2939_ =
                                                                    v_isSharedCheck_2943_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2936_);
                                                                lean_dec(v___x_2931_);
                                                                v___x_2938_ = lean_box(0);
                                                                v_isShared_2939_ =
                                                                    v_isSharedCheck_2943_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_2769_);
                                                        lean_dec_ref(v_e_2757_);
                                                        v___x_2944_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                        return v___x_2944_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_2775_);
                                                    lean_dec_ref(v_arg_2769_);
                                                    lean_dec_ref(v_e_2757_);
                                                    v_a_2945_ = lean_ctor_get(v___x_2927_, 0);
                                                    v_isSharedCheck_2952_ =
                                                        (!lean_is_exclusive(v___x_2927_)) as u8;
                                                    if v_isSharedCheck_2952_ == 0 {
                                                        v___x_2947_ = v___x_2927_;
                                                        v_isShared_2948_ = v_isSharedCheck_2952_;
                                                        state = 24;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2945_);
                                                        lean_dec(v___x_2927_);
                                                        v___x_2947_ = lean_box(0);
                                                        v_isShared_2948_ = v_isSharedCheck_2952_;
                                                        state = 24;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_2826_);
                                        lean_dec_ref(v_e_2757_);
                                        v___x_2953_ =
                                            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                                v_arg_2775_,
                                                v_a_2758_,
                                                v_a_2759_,
                                                v_a_2760_,
                                                v_a_2761_,
                                                v_a_2762_,
                                            );
                                        if lean_obj_tag(v___x_2953_) == 0 {
                                            v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
                                            lean_inc(v_a_2954_);
                                            lean_dec_ref_known(v___x_2953_, 1);
                                            v___x_2955_ =
                                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                                    v_arg_2769_,
                                                    v_a_2758_,
                                                    v_a_2759_,
                                                    v_a_2760_,
                                                    v_a_2761_,
                                                    v_a_2762_,
                                                );
                                            if lean_obj_tag(v___x_2955_) == 0 {
                                                v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
                                                v_isSharedCheck_2964_ =
                                                    (!lean_is_exclusive(v___x_2955_)) as u8;
                                                if v_isSharedCheck_2964_ == 0 {
                                                    v___x_2958_ = v___x_2955_;
                                                    v_isShared_2959_ = v_isSharedCheck_2964_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2956_);
                                                    lean_dec(v___x_2955_);
                                                    v___x_2958_ = lean_box(0);
                                                    v_isShared_2959_ = v_isSharedCheck_2964_;
                                                    state = 26;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_2954_);
                                                return v___x_2955_;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_2769_);
                                            return v___x_2953_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_2826_);
                                    v_b_2777_ = v_arg_2769_;
                                    v___y_2778_ = v_a_2758_;
                                    v___y_2779_ = v_a_2759_;
                                    v___y_2780_ = v_a_2760_;
                                    v___y_2781_ = v_a_2761_;
                                    v___y_2782_ = v_a_2762_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_2770_);
                            lean_dec_ref(v_e_2757_);
                            v___x_2965_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                v_arg_2769_,
                                v_a_2758_,
                                v_a_2759_,
                                v_a_2760_,
                                v_a_2761_,
                                v_a_2762_,
                            );
                            if lean_obj_tag(v___x_2965_) == 0 {
                                v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
                                v_isSharedCheck_2974_ = (!lean_is_exclusive(v___x_2965_)) as u8;
                                if v_isSharedCheck_2974_ == 0 {
                                    v___x_2968_ = v___x_2965_;
                                    v_isShared_2969_ = v_isSharedCheck_2974_;
                                    state = 28;
                                    continue;
                                } else {
                                    lean_inc(v_a_2966_);
                                    lean_dec(v___x_2965_);
                                    v___x_2968_ = lean_box(0);
                                    v_isShared_2969_ = v_isSharedCheck_2974_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                return v___x_2965_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_2757_);
                    v_a_2975_ = lean_ctor_get(v___x_2764_, 0);
                    v_isSharedCheck_2982_ = (!lean_is_exclusive(v___x_2764_)) as u8;
                    if v_isSharedCheck_2982_ == 0 {
                        v___x_2977_ = v___x_2764_;
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_2975_);
                        lean_dec(v___x_2764_);
                        v___x_2977_ = lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_arg_2775_);
                v___x_2783_ = l_Lean_Meta_evalNat(
                    v_arg_2775_,
                    v___y_2779_,
                    v___y_2780_,
                    v___y_2781_,
                    v___y_2782_,
                );
                if lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
                    lean_inc(v_a_2784_);
                    lean_dec_ref_known(v___x_2783_, 1);
                    if lean_obj_tag(v_a_2784_) == 0 {
                        v___x_2785_ = l_Lean_Meta_evalNat(
                            v_b_2777_,
                            v___y_2779_,
                            v___y_2780_,
                            v___y_2781_,
                            v___y_2782_,
                        );
                        if lean_obj_tag(v___x_2785_) == 0 {
                            v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
                            lean_inc(v_a_2786_);
                            lean_dec_ref_known(v___x_2785_, 1);
                            if lean_obj_tag(v_a_2786_) == 0 {
                                lean_dec_ref(v_arg_2775_);
                                v___x_2787_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2757_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    v___y_2781_,
                                    v___y_2782_,
                                );
                                return v___x_2787_;
                            } else {
                                lean_dec_ref(v_e_2757_);
                                v_val_2788_ = lean_ctor_get(v_a_2786_, 0);
                                lean_inc(v_val_2788_);
                                lean_dec_ref_known(v_a_2786_, 1);
                                v___x_2789_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_2775_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    v___y_2781_,
                                    v___y_2782_,
                                );
                                if lean_obj_tag(v___x_2789_) == 0 {
                                    v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
                                    v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2789_)) as u8;
                                    if v_isSharedCheck_2798_ == 0 {
                                        v___x_2792_ = v___x_2789_;
                                        v_isShared_2793_ = v_isSharedCheck_2798_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2790_);
                                        lean_dec(v___x_2789_);
                                        v___x_2792_ = lean_box(0);
                                        v_isShared_2793_ = v_isSharedCheck_2798_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_2788_);
                                    return v___x_2789_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_2775_);
                            lean_dec_ref(v_e_2757_);
                            v_a_2799_ = lean_ctor_get(v___x_2785_, 0);
                            v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2785_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2785_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2799_);
                                lean_dec(v___x_2785_);
                                v___x_2801_ = lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2775_);
                        lean_dec_ref(v_e_2757_);
                        v_val_2807_ = lean_ctor_get(v_a_2784_, 0);
                        lean_inc(v_val_2807_);
                        lean_dec_ref_known(v_a_2784_, 1);
                        v___x_2808_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_b_2777_,
                            v___y_2778_,
                            v___y_2779_,
                            v___y_2780_,
                            v___y_2781_,
                            v___y_2782_,
                        );
                        if lean_obj_tag(v___x_2808_) == 0 {
                            v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
                            v_isSharedCheck_2817_ = (!lean_is_exclusive(v___x_2808_)) as u8;
                            if v_isSharedCheck_2817_ == 0 {
                                v___x_2811_ = v___x_2808_;
                                v_isShared_2812_ = v_isSharedCheck_2817_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2809_);
                                lean_dec(v___x_2808_);
                                v___x_2811_ = lean_box(0);
                                v_isShared_2812_ = v_isSharedCheck_2817_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_2807_);
                            return v___x_2808_;
                        }
                    }
                } else {
                    lean_dec_ref(v_b_2777_);
                    lean_dec_ref(v_arg_2775_);
                    lean_dec_ref(v_e_2757_);
                    v_a_2818_ = lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2825_ = (!lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2825_ == 0 {
                        v___x_2820_ = v___x_2783_;
                        v_isShared_2821_ = v_isSharedCheck_2825_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2818_);
                        lean_dec(v___x_2783_);
                        v___x_2820_ = lean_box(0);
                        v_isShared_2821_ = v_isSharedCheck_2825_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2794_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2794_, 0, v_a_2790_);
                lean_ctor_set(v___x_2794_, 1, v_val_2788_);
                if v_isShared_2793_ == 0 {
                    lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2796_;
            }
            4 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2804_;
            }
            6 => {
                v___x_2813_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_2813_, 0, v_val_2807_);
                lean_ctor_set(v___x_2813_, 1, v_a_2809_);
                if v_isShared_2812_ == 0 {
                    lean_ctor_set(v___x_2811_, 0, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2815_;
            }
            8 => {
                if v_isShared_2821_ == 0 {
                    v___x_2823_ = v___x_2820_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
                    v___x_2823_ = v_reuseFailAlloc_2824_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2823_;
            }
            10 => {
                v___x_2866_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2866_, 0, v_a_2860_);
                lean_ctor_set(v___x_2866_, 1, v_a_2862_);
                if v_isShared_2865_ == 0 {
                    lean_ctor_set(v___x_2864_, 0, v___x_2866_);
                    v___x_2868_ = v___x_2864_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2868_;
            }
            12 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2876_;
            }
            14 => {
                if v_isShared_2886_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2888_;
            }
            16 => {
                v___x_2902_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2902_, 0, v_a_2896_);
                lean_ctor_set(v___x_2902_, 1, v_a_2898_);
                if v_isShared_2901_ == 0 {
                    lean_ctor_set(v___x_2900_, 0, v___x_2902_);
                    v___x_2904_ = v___x_2900_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2904_;
            }
            18 => {
                if v_isShared_2910_ == 0 {
                    v___x_2912_ = v___x_2909_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2912_;
            }
            20 => {
                if v_isShared_2922_ == 0 {
                    v___x_2924_ = v___x_2921_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
                    v___x_2924_ = v_reuseFailAlloc_2925_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2924_;
            }
            22 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2941_;
            }
            24 => {
                if v_isShared_2948_ == 0 {
                    v___x_2950_ = v___x_2947_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2950_;
            }
            26 => {
                v___x_2960_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2960_, 0, v_a_2954_);
                lean_ctor_set(v___x_2960_, 1, v_a_2956_);
                if v_isShared_2959_ == 0 {
                    lean_ctor_set(v___x_2958_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2958_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2962_;
            }
            28 => {
                v___x_2970_ = l_Nat_Linear_Expr_inc(v_a_2966_);
                if v_isShared_2969_ == 0 {
                    lean_ctor_set(v___x_2968_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2968_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2972_;
            }
            30 => {
                if v_isShared_2978_ == 0 {
                    v___x_2980_ = v___x_2977_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
    mut v_e_2983_: *mut LeanObject,
    mut v_a_2984_: *mut LeanObject,
    mut v_a_2985_: *mut LeanObject,
    mut v_a_2986_: *mut LeanObject,
    mut v_a_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2999_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2983_) {
                9 => {
                    v_a_2990_ = lean_ctor_get(v_e_2983_, 0);
                    lean_inc_ref(v_a_2990_);
                    if lean_obj_tag(v_a_2990_) == 0 {
                        lean_dec_ref_known(v_e_2983_, 1);
                        v_val_2991_ = lean_ctor_get(v_a_2990_, 0);
                        v_isSharedCheck_2999_ = (!lean_is_exclusive(v_a_2990_)) as u8;
                        if v_isSharedCheck_2999_ == 0 {
                            v___x_2993_ = v_a_2990_;
                            v_isShared_2994_ = v_isSharedCheck_2999_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2991_);
                            lean_dec(v_a_2990_);
                            v___x_2993_ = lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_2999_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_2990_);
                        v___x_3000_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                        );
                        return v___x_3000_;
                    }
                }
                10 => {
                    v_expr_3001_ = lean_ctor_get(v_e_2983_, 1);
                    lean_inc_ref(v_expr_3001_);
                    lean_dec_ref_known(v_e_2983_, 2);
                    v_e_2983_ = v_expr_3001_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_declName_3003_ = lean_ctor_get(v_e_2983_, 0);
                    if lean_obj_tag(v_declName_3003_) == 1 {
                        v_pre_3004_ = lean_ctor_get(v_declName_3003_, 0);
                        if lean_obj_tag(v_pre_3004_) == 1 {
                            v_pre_3005_ = lean_ctor_get(v_pre_3004_, 0);
                            if lean_obj_tag(v_pre_3005_) == 0 {
                                v_str_3006_ = lean_ctor_get(v_declName_3003_, 1);
                                v_str_3007_ = lean_ctor_get(v_pre_3004_, 1);
                                v___x_3008_ =
                                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
                                v___x_3009_ = lean_string_dec_eq(v_str_3007_, v___x_3008_);
                                if v___x_3009_ == 0 {
                                    v___x_3010_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                        v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                        v_a_2988_,
                                    );
                                    return v___x_3010_;
                                } else {
                                    v___x_3011_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
                                    v___x_3012_ = lean_string_dec_eq(v_str_3006_, v___x_3011_);
                                    if v___x_3012_ == 0 {
                                        v___x_3013_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                            v_a_2988_,
                                        );
                                        return v___x_3013_;
                                    } else {
                                        lean_dec_ref_known(v_e_2983_, 2);
                                        v___x_3014_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
                                        v___x_3015_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_3015_, 0, v___x_3014_);
                                        return v___x_3015_;
                                    }
                                }
                            } else {
                                v___x_3016_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                    v_a_2988_,
                                );
                                return v___x_3016_;
                            }
                        } else {
                            v___x_3017_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                            );
                            return v___x_3017_;
                        }
                    } else {
                        v___x_3018_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                        );
                        return v___x_3018_;
                    }
                }
                5 => {
                    v___x_3019_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
                    return v___x_3019_;
                }
                2 => {
                    v___x_3020_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
                    return v___x_3020_;
                }
                _ => {
                    v___x_3021_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                        v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                    );
                    return v___x_3021_;
                }
            },
            1 => {
                if v_isShared_2994_ == 0 {
                    v___x_2996_ = v___x_2993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_val_2991_);
                    v___x_2996_ = v_reuseFailAlloc_2998_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2997_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2997_, 0, v___x_2996_);
                return v___x_2997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(
    mut v_e_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3029_: *mut LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
        v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_,
    );
    lean_dec(v_a_3027_);
    lean_dec_ref(v_a_3026_);
    lean_dec(v_a_3025_);
    lean_dec_ref(v_a_3024_);
    lean_dec(v_a_3023_);
    return v_res_3029_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(
    mut v_e_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
    mut v_a_3032_: *mut LeanObject,
    mut v_a_3033_: *mut LeanObject,
    mut v_a_3034_: *mut LeanObject,
    mut v_a_3035_: *mut LeanObject,
    mut v_a_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3037_: *mut LeanObject = core::ptr::null_mut();
    v_res_3037_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
    lean_dec(v_a_3035_);
    lean_dec_ref(v_a_3034_);
    lean_dec(v_a_3033_);
    lean_dec_ref(v_a_3032_);
    lean_dec(v_a_3031_);
    return v_res_3037_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(
    mut v_e_3069_: *mut LeanObject,
    mut v_a_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3080_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v_arg_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v_arg_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___x_3097_: u8 = 0;
    let mut v_arg_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_a_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_a_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3146_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_a_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_a_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_a_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3213_: u8 = 0;
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_a_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3235_: u8 = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_a_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_a_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_a_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_a_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3334_: u8 = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3338_: u8 = 0;
    let mut v_a_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3342_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_isSharedCheck_3347_: u8 = 0;
    let mut v_a_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_a_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_a_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3391_: u8 = 0;
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_a_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_a_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_a_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3420_: u8 = 0;
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3069_, v_a_3072_);
                if lean_obj_tag(v___x_3076_) == 0 {
                    v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
                    v_isSharedCheck_3416_ = (!lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3079_ = v___x_3076_;
                        v_isShared_3080_ = v_isSharedCheck_3416_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3077_);
                        lean_dec(v___x_3076_);
                        v___x_3079_ = lean_box(0);
                        v_isShared_3080_ = v_isSharedCheck_3416_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3417_ = lean_ctor_get(v___x_3076_, 0);
                    v_isSharedCheck_3424_ = (!lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3419_ = v___x_3076_;
                        v_isShared_3420_ = v_isSharedCheck_3424_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_a_3417_);
                        lean_dec(v___x_3076_);
                        v___x_3419_ = lean_box(0);
                        v_isShared_3420_ = v_isSharedCheck_3424_;
                        state = 66;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3086_ = l_Lean_Expr_cleanupAnnotations(v_a_3077_);
                v___x_3087_ = l_Lean_Expr_isApp(v___x_3086_);
                if v___x_3087_ == 0 {
                    lean_dec_ref(v___x_3086_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3088_ = lean_ctor_get(v___x_3086_, 1);
                    lean_inc_ref(v_arg_3088_);
                    v___x_3089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3086_);
                    v___x_3090_ = l_Lean_Expr_isApp(v___x_3089_);
                    if v___x_3090_ == 0 {
                        lean_dec_ref(v___x_3089_);
                        lean_dec_ref(v_arg_3088_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3091_ = lean_ctor_get(v___x_3089_, 1);
                        lean_inc_ref(v_arg_3091_);
                        v___x_3092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3089_);
                        v___x_3093_ =
                            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
                        v___x_3094_ = l_Lean_Expr_isConstOf(v___x_3092_, v___x_3093_);
                        if v___x_3094_ == 0 {
                            v___x_3095_ =
                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
                            v___x_3096_ = l_Lean_Expr_isConstOf(v___x_3092_, v___x_3095_);
                            if v___x_3096_ == 0 {
                                v___x_3097_ = l_Lean_Expr_isApp(v___x_3092_);
                                if v___x_3097_ == 0 {
                                    lean_dec_ref(v___x_3092_);
                                    lean_dec_ref(v_arg_3091_);
                                    lean_dec_ref(v_arg_3088_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_3098_ = lean_ctor_get(v___x_3092_, 1);
                                    lean_inc_ref(v_arg_3098_);
                                    v___x_3099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3092_);
                                    v___x_3100_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
                                    v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3099_, v___x_3100_);
                                    if v___x_3101_ == 0 {
                                        v___x_3102_ = l_Lean_Expr_isApp(v___x_3099_);
                                        if v___x_3102_ == 0 {
                                            lean_dec_ref(v___x_3099_);
                                            lean_dec_ref(v_arg_3098_);
                                            lean_dec_ref(v_arg_3091_);
                                            lean_dec_ref(v_arg_3088_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_3103_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3099_);
                                            v___x_3104_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
                                            v___x_3105_ =
                                                l_Lean_Expr_isConstOf(v___x_3103_, v___x_3104_);
                                            if v___x_3105_ == 0 {
                                                v___x_3106_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
                                                v___x_3107_ =
                                                    l_Lean_Expr_isConstOf(v___x_3103_, v___x_3106_);
                                                if v___x_3107_ == 0 {
                                                    v___x_3108_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
                                                    v___x_3109_ = l_Lean_Expr_isConstOf(
                                                        v___x_3103_,
                                                        v___x_3108_,
                                                    );
                                                    if v___x_3109_ == 0 {
                                                        v___x_3110_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
                                                        v___x_3111_ = l_Lean_Expr_isConstOf(
                                                            v___x_3103_,
                                                            v___x_3110_,
                                                        );
                                                        lean_dec_ref(v___x_3103_);
                                                        if v___x_3111_ == 0 {
                                                            lean_dec_ref(v_arg_3098_);
                                                            lean_dec_ref(v_arg_3091_);
                                                            lean_dec_ref(v_arg_3088_);
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_del_object(v___x_3079_);
                                                            v___x_3112_ =
                                                                l_Lean_Meta_DefEq_isInstLENat(
                                                                    v_arg_3098_,
                                                                    v_a_3071_,
                                                                    v_a_3072_,
                                                                    v_a_3073_,
                                                                    v_a_3074_,
                                                                );
                                                            if lean_obj_tag(v___x_3112_) == 0 {
                                                                v_a_3113_ =
                                                                    lean_ctor_get(v___x_3112_, 0);
                                                                v_isSharedCheck_3151_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3112_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3151_ == 0 {
                                                                    v___x_3115_ = v___x_3112_;
                                                                    v_isShared_3116_ =
                                                                        v_isSharedCheck_3151_;
                                                                    state = 4;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3113_);
                                                                    lean_dec(v___x_3112_);
                                                                    v___x_3115_ = lean_box(0);
                                                                    v_isShared_3116_ =
                                                                        v_isSharedCheck_3151_;
                                                                    state = 4;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_3091_);
                                                                lean_dec_ref(v_arg_3088_);
                                                                v_a_3152_ =
                                                                    lean_ctor_get(v___x_3112_, 0);
                                                                v_isSharedCheck_3159_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3112_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3159_ == 0 {
                                                                    v___x_3154_ = v___x_3112_;
                                                                    v_isShared_3155_ =
                                                                        v_isSharedCheck_3159_;
                                                                    state = 12;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3152_);
                                                                    lean_dec(v___x_3112_);
                                                                    v___x_3154_ = lean_box(0);
                                                                    v_isShared_3155_ =
                                                                        v_isSharedCheck_3159_;
                                                                    state = 12;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_3103_);
                                                        lean_del_object(v___x_3079_);
                                                        v___x_3160_ = l_Lean_Meta_DefEq_isInstLTNat(
                                                            v_arg_3098_,
                                                            v_a_3071_,
                                                            v_a_3072_,
                                                            v_a_3073_,
                                                            v_a_3074_,
                                                        );
                                                        if lean_obj_tag(v___x_3160_) == 0 {
                                                            v_a_3161_ =
                                                                lean_ctor_get(v___x_3160_, 0);
                                                            v_isSharedCheck_3200_ =
                                                                (!lean_is_exclusive(v___x_3160_))
                                                                    as u8;
                                                            if v_isSharedCheck_3200_ == 0 {
                                                                v___x_3163_ = v___x_3160_;
                                                                v_isShared_3164_ =
                                                                    v_isSharedCheck_3200_;
                                                                state = 14;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3161_);
                                                                lean_dec(v___x_3160_);
                                                                v___x_3163_ = lean_box(0);
                                                                v_isShared_3164_ =
                                                                    v_isSharedCheck_3200_;
                                                                state = 14;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_3091_);
                                                            lean_dec_ref(v_arg_3088_);
                                                            v_a_3201_ =
                                                                lean_ctor_get(v___x_3160_, 0);
                                                            v_isSharedCheck_3208_ =
                                                                (!lean_is_exclusive(v___x_3160_))
                                                                    as u8;
                                                            if v_isSharedCheck_3208_ == 0 {
                                                                v___x_3203_ = v___x_3160_;
                                                                v_isShared_3204_ =
                                                                    v_isSharedCheck_3208_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3201_);
                                                                lean_dec(v___x_3160_);
                                                                v___x_3203_ = lean_box(0);
                                                                v_isShared_3204_ =
                                                                    v_isSharedCheck_3208_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_3103_);
                                                    lean_del_object(v___x_3079_);
                                                    v___x_3209_ = l_Lean_Meta_DefEq_isInstLENat(
                                                        v_arg_3098_,
                                                        v_a_3071_,
                                                        v_a_3072_,
                                                        v_a_3073_,
                                                        v_a_3074_,
                                                    );
                                                    if lean_obj_tag(v___x_3209_) == 0 {
                                                        v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
                                                        v_isSharedCheck_3248_ =
                                                            (!lean_is_exclusive(v___x_3209_)) as u8;
                                                        if v_isSharedCheck_3248_ == 0 {
                                                            v___x_3212_ = v___x_3209_;
                                                            v_isShared_3213_ =
                                                                v_isSharedCheck_3248_;
                                                            state = 24;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3210_);
                                                            lean_dec(v___x_3209_);
                                                            v___x_3212_ = lean_box(0);
                                                            v_isShared_3213_ =
                                                                v_isSharedCheck_3248_;
                                                            state = 24;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_3091_);
                                                        lean_dec_ref(v_arg_3088_);
                                                        v_a_3249_ = lean_ctor_get(v___x_3209_, 0);
                                                        v_isSharedCheck_3256_ =
                                                            (!lean_is_exclusive(v___x_3209_)) as u8;
                                                        if v_isSharedCheck_3256_ == 0 {
                                                            v___x_3251_ = v___x_3209_;
                                                            v_isShared_3252_ =
                                                                v_isSharedCheck_3256_;
                                                            state = 32;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3249_);
                                                            lean_dec(v___x_3209_);
                                                            v___x_3251_ = lean_box(0);
                                                            v_isShared_3252_ =
                                                                v_isSharedCheck_3256_;
                                                            state = 32;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_3103_);
                                                lean_del_object(v___x_3079_);
                                                v___x_3257_ = l_Lean_Meta_DefEq_isInstLTNat(
                                                    v_arg_3098_,
                                                    v_a_3071_,
                                                    v_a_3072_,
                                                    v_a_3073_,
                                                    v_a_3074_,
                                                );
                                                if lean_obj_tag(v___x_3257_) == 0 {
                                                    v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                                                    v_isSharedCheck_3297_ =
                                                        (!lean_is_exclusive(v___x_3257_)) as u8;
                                                    if v_isSharedCheck_3297_ == 0 {
                                                        v___x_3260_ = v___x_3257_;
                                                        v_isShared_3261_ = v_isSharedCheck_3297_;
                                                        state = 34;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3258_);
                                                        lean_dec(v___x_3257_);
                                                        v___x_3260_ = lean_box(0);
                                                        v_isShared_3261_ = v_isSharedCheck_3297_;
                                                        state = 34;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_3091_);
                                                    lean_dec_ref(v_arg_3088_);
                                                    v_a_3298_ = lean_ctor_get(v___x_3257_, 0);
                                                    v_isSharedCheck_3305_ =
                                                        (!lean_is_exclusive(v___x_3257_)) as u8;
                                                    if v_isSharedCheck_3305_ == 0 {
                                                        v___x_3300_ = v___x_3257_;
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 42;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3298_);
                                                        lean_dec(v___x_3257_);
                                                        v___x_3300_ = lean_box(0);
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 42;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3099_);
                                        lean_del_object(v___x_3079_);
                                        v___x_3306_ =
                                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                v_arg_3098_,
                                                v_a_3072_,
                                            );
                                        if lean_obj_tag(v___x_3306_) == 0 {
                                            v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
                                            v_isSharedCheck_3347_ =
                                                (!lean_is_exclusive(v___x_3306_)) as u8;
                                            if v_isSharedCheck_3347_ == 0 {
                                                v___x_3309_ = v___x_3306_;
                                                v_isShared_3310_ = v_isSharedCheck_3347_;
                                                state = 44;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3307_);
                                                lean_dec(v___x_3306_);
                                                v___x_3309_ = lean_box(0);
                                                v_isShared_3310_ = v_isSharedCheck_3347_;
                                                state = 44;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_3091_);
                                            lean_dec_ref(v_arg_3088_);
                                            v_a_3348_ = lean_ctor_get(v___x_3306_, 0);
                                            v_isSharedCheck_3355_ =
                                                (!lean_is_exclusive(v___x_3306_)) as u8;
                                            if v_isSharedCheck_3355_ == 0 {
                                                v___x_3350_ = v___x_3306_;
                                                v_isShared_3351_ = v_isSharedCheck_3355_;
                                                state = 52;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3348_);
                                                lean_dec(v___x_3306_);
                                                v___x_3350_ = lean_box(0);
                                                v_isShared_3351_ = v_isSharedCheck_3355_;
                                                state = 52;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_3092_);
                                lean_del_object(v___x_3079_);
                                v___x_3356_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_3091_,
                                    v_a_3070_,
                                    v_a_3071_,
                                    v_a_3072_,
                                    v_a_3073_,
                                    v_a_3074_,
                                );
                                if lean_obj_tag(v___x_3356_) == 0 {
                                    v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
                                    lean_inc(v_a_3357_);
                                    lean_dec_ref_known(v___x_3356_, 1);
                                    v___x_3358_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                        v_arg_3088_,
                                        v_a_3070_,
                                        v_a_3071_,
                                        v_a_3072_,
                                        v_a_3073_,
                                        v_a_3074_,
                                    );
                                    if lean_obj_tag(v___x_3358_) == 0 {
                                        v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
                                        v_isSharedCheck_3368_ =
                                            (!lean_is_exclusive(v___x_3358_)) as u8;
                                        if v_isSharedCheck_3368_ == 0 {
                                            v___x_3361_ = v___x_3358_;
                                            v_isShared_3362_ = v_isSharedCheck_3368_;
                                            state = 54;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3359_);
                                            lean_dec(v___x_3358_);
                                            v___x_3361_ = lean_box(0);
                                            v_isShared_3362_ = v_isSharedCheck_3368_;
                                            state = 54;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3357_);
                                        v_a_3369_ = lean_ctor_get(v___x_3358_, 0);
                                        v_isSharedCheck_3376_ =
                                            (!lean_is_exclusive(v___x_3358_)) as u8;
                                        if v_isSharedCheck_3376_ == 0 {
                                            v___x_3371_ = v___x_3358_;
                                            v_isShared_3372_ = v_isSharedCheck_3376_;
                                            state = 56;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3369_);
                                            lean_dec(v___x_3358_);
                                            v___x_3371_ = lean_box(0);
                                            v_isShared_3372_ = v_isSharedCheck_3376_;
                                            state = 56;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_arg_3088_);
                                    v_a_3377_ = lean_ctor_get(v___x_3356_, 0);
                                    v_isSharedCheck_3384_ = (!lean_is_exclusive(v___x_3356_)) as u8;
                                    if v_isSharedCheck_3384_ == 0 {
                                        v___x_3379_ = v___x_3356_;
                                        v_isShared_3380_ = v_isSharedCheck_3384_;
                                        state = 58;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3377_);
                                        lean_dec(v___x_3356_);
                                        v___x_3379_ = lean_box(0);
                                        v_isShared_3380_ = v_isSharedCheck_3384_;
                                        state = 58;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3092_);
                            lean_del_object(v___x_3079_);
                            v___x_3385_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                v_arg_3091_,
                                v_a_3070_,
                                v_a_3071_,
                                v_a_3072_,
                                v_a_3073_,
                                v_a_3074_,
                            );
                            if lean_obj_tag(v___x_3385_) == 0 {
                                v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
                                lean_inc(v_a_3386_);
                                lean_dec_ref_known(v___x_3385_, 1);
                                v___x_3387_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_3088_,
                                    v_a_3070_,
                                    v_a_3071_,
                                    v_a_3072_,
                                    v_a_3073_,
                                    v_a_3074_,
                                );
                                if lean_obj_tag(v___x_3387_) == 0 {
                                    v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
                                    v_isSharedCheck_3399_ = (!lean_is_exclusive(v___x_3387_)) as u8;
                                    if v_isSharedCheck_3399_ == 0 {
                                        v___x_3390_ = v___x_3387_;
                                        v_isShared_3391_ = v_isSharedCheck_3399_;
                                        state = 60;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3388_);
                                        lean_dec(v___x_3387_);
                                        v___x_3390_ = lean_box(0);
                                        v_isShared_3391_ = v_isSharedCheck_3399_;
                                        state = 60;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3386_);
                                    v_a_3400_ = lean_ctor_get(v___x_3387_, 0);
                                    v_isSharedCheck_3407_ = (!lean_is_exclusive(v___x_3387_)) as u8;
                                    if v_isSharedCheck_3407_ == 0 {
                                        v___x_3402_ = v___x_3387_;
                                        v_isShared_3403_ = v_isSharedCheck_3407_;
                                        state = 62;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3400_);
                                        lean_dec(v___x_3387_);
                                        v___x_3402_ = lean_box(0);
                                        v_isShared_3403_ = v_isSharedCheck_3407_;
                                        state = 62;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_arg_3088_);
                                v_a_3408_ = lean_ctor_get(v___x_3385_, 0);
                                v_isSharedCheck_3415_ = (!lean_is_exclusive(v___x_3385_)) as u8;
                                if v_isSharedCheck_3415_ == 0 {
                                    v___x_3410_ = v___x_3385_;
                                    v_isShared_3411_ = v_isSharedCheck_3415_;
                                    state = 64;
                                    continue;
                                } else {
                                    lean_inc(v_a_3408_);
                                    lean_dec(v___x_3385_);
                                    v___x_3410_ = lean_box(0);
                                    v_isShared_3411_ = v_isSharedCheck_3415_;
                                    state = 64;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3082_ = lean_box(0);
                if v_isShared_3080_ == 0 {
                    lean_ctor_set(v___x_3079_, 0, v___x_3082_);
                    v___x_3084_ = v___x_3079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3084_;
            }
            4 => {
                v___x_3117_ = (lean_unbox(v_a_3113_) as u8);
                lean_dec(v_a_3113_);
                if v___x_3117_ == 0 {
                    lean_dec_ref(v_arg_3091_);
                    lean_dec_ref(v_arg_3088_);
                    v___x_3118_ = lean_box(0);
                    if v_isShared_3116_ == 0 {
                        lean_ctor_set(v___x_3115_, 0, v___x_3118_);
                        v___x_3120_ = v___x_3115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
                        v___x_3120_ = v_reuseFailAlloc_3121_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3115_);
                    v___x_3122_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if lean_obj_tag(v___x_3122_) == 0 {
                        v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
                        lean_inc(v_a_3123_);
                        lean_dec_ref_known(v___x_3122_, 1);
                        v___x_3124_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if lean_obj_tag(v___x_3124_) == 0 {
                            v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
                            v_isSharedCheck_3134_ = (!lean_is_exclusive(v___x_3124_)) as u8;
                            if v_isSharedCheck_3134_ == 0 {
                                v___x_3127_ = v___x_3124_;
                                v_isShared_3128_ = v_isSharedCheck_3134_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3125_);
                                lean_dec(v___x_3124_);
                                v___x_3127_ = lean_box(0);
                                v_isShared_3128_ = v_isSharedCheck_3134_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3123_);
                            v_a_3135_ = lean_ctor_get(v___x_3124_, 0);
                            v_isSharedCheck_3142_ = (!lean_is_exclusive(v___x_3124_)) as u8;
                            if v_isSharedCheck_3142_ == 0 {
                                v___x_3137_ = v___x_3124_;
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3135_);
                                lean_dec(v___x_3124_);
                                v___x_3137_ = lean_box(0);
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3088_);
                        v_a_3143_ = lean_ctor_get(v___x_3122_, 0);
                        v_isSharedCheck_3150_ = (!lean_is_exclusive(v___x_3122_)) as u8;
                        if v_isSharedCheck_3150_ == 0 {
                            v___x_3145_ = v___x_3122_;
                            v_isShared_3146_ = v_isSharedCheck_3150_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3143_);
                            lean_dec(v___x_3122_);
                            v___x_3145_ = lean_box(0);
                            v_isShared_3146_ = v_isSharedCheck_3150_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3120_;
            }
            6 => {
                v___x_3129_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3129_, 0, v_a_3123_);
                lean_ctor_set(v___x_3129_, 1, v_a_3125_);
                lean_ctor_set_uint8(
                    v___x_3129_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3109_,
                );
                v___x_3130_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3130_, 0, v___x_3129_);
                if v_isShared_3128_ == 0 {
                    lean_ctor_set(v___x_3127_, 0, v___x_3130_);
                    v___x_3132_ = v___x_3127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3132_;
            }
            8 => {
                if v_isShared_3138_ == 0 {
                    v___x_3140_ = v___x_3137_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3140_;
            }
            10 => {
                if v_isShared_3146_ == 0 {
                    v___x_3148_ = v___x_3145_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
                    v___x_3148_ = v_reuseFailAlloc_3149_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3148_;
            }
            12 => {
                if v_isShared_3155_ == 0 {
                    v___x_3157_ = v___x_3154_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3157_;
            }
            14 => {
                v___x_3165_ = (lean_unbox(v_a_3161_) as u8);
                lean_dec(v_a_3161_);
                if v___x_3165_ == 0 {
                    lean_dec_ref(v_arg_3091_);
                    lean_dec_ref(v_arg_3088_);
                    v___x_3166_ = lean_box(0);
                    if v_isShared_3164_ == 0 {
                        lean_ctor_set(v___x_3163_, 0, v___x_3166_);
                        v___x_3168_ = v___x_3163_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
                        v___x_3168_ = v_reuseFailAlloc_3169_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3163_);
                    v___x_3170_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if lean_obj_tag(v___x_3170_) == 0 {
                        v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
                        lean_inc(v_a_3171_);
                        lean_dec_ref_known(v___x_3170_, 1);
                        v___x_3172_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if lean_obj_tag(v___x_3172_) == 0 {
                            v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
                            v_isSharedCheck_3183_ = (!lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3183_ == 0 {
                                v___x_3175_ = v___x_3172_;
                                v_isShared_3176_ = v_isSharedCheck_3183_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_3173_);
                                lean_dec(v___x_3172_);
                                v___x_3175_ = lean_box(0);
                                v_isShared_3176_ = v_isSharedCheck_3183_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3171_);
                            v_a_3184_ = lean_ctor_get(v___x_3172_, 0);
                            v_isSharedCheck_3191_ = (!lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3191_ == 0 {
                                v___x_3186_ = v___x_3172_;
                                v_isShared_3187_ = v_isSharedCheck_3191_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_3184_);
                                lean_dec(v___x_3172_);
                                v___x_3186_ = lean_box(0);
                                v_isShared_3187_ = v_isSharedCheck_3191_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3088_);
                        v_a_3192_ = lean_ctor_get(v___x_3170_, 0);
                        v_isSharedCheck_3199_ = (!lean_is_exclusive(v___x_3170_)) as u8;
                        if v_isSharedCheck_3199_ == 0 {
                            v___x_3194_ = v___x_3170_;
                            v_isShared_3195_ = v_isSharedCheck_3199_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3192_);
                            lean_dec(v___x_3170_);
                            v___x_3194_ = lean_box(0);
                            v_isShared_3195_ = v_isSharedCheck_3199_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            15 => {
                return v___x_3168_;
            }
            16 => {
                v___x_3177_ = l_Nat_Linear_Expr_inc(v_a_3171_);
                v___x_3178_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3178_, 0, v___x_3177_);
                lean_ctor_set(v___x_3178_, 1, v_a_3173_);
                lean_ctor_set_uint8(
                    v___x_3178_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3107_,
                );
                v___x_3179_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3181_;
            }
            18 => {
                if v_isShared_3187_ == 0 {
                    v___x_3189_ = v___x_3186_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
                    v___x_3189_ = v_reuseFailAlloc_3190_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3189_;
            }
            20 => {
                if v_isShared_3195_ == 0 {
                    v___x_3197_ = v___x_3194_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3197_;
            }
            22 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3206_;
            }
            24 => {
                v___x_3214_ = (lean_unbox(v_a_3210_) as u8);
                lean_dec(v_a_3210_);
                if v___x_3214_ == 0 {
                    lean_dec_ref(v_arg_3091_);
                    lean_dec_ref(v_arg_3088_);
                    v___x_3215_ = lean_box(0);
                    if v_isShared_3213_ == 0 {
                        lean_ctor_set(v___x_3212_, 0, v___x_3215_);
                        v___x_3217_ = v___x_3212_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
                        v___x_3217_ = v_reuseFailAlloc_3218_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3212_);
                    v___x_3219_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3088_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
                        lean_inc(v_a_3220_);
                        lean_dec_ref_known(v___x_3219_, 1);
                        v___x_3221_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3091_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if lean_obj_tag(v___x_3221_) == 0 {
                            v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
                            v_isSharedCheck_3231_ = (!lean_is_exclusive(v___x_3221_)) as u8;
                            if v_isSharedCheck_3231_ == 0 {
                                v___x_3224_ = v___x_3221_;
                                v_isShared_3225_ = v_isSharedCheck_3231_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_3222_);
                                lean_dec(v___x_3221_);
                                v___x_3224_ = lean_box(0);
                                v_isShared_3225_ = v_isSharedCheck_3231_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3220_);
                            v_a_3232_ = lean_ctor_get(v___x_3221_, 0);
                            v_isSharedCheck_3239_ = (!lean_is_exclusive(v___x_3221_)) as u8;
                            if v_isSharedCheck_3239_ == 0 {
                                v___x_3234_ = v___x_3221_;
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_3232_);
                                lean_dec(v___x_3221_);
                                v___x_3234_ = lean_box(0);
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3091_);
                        v_a_3240_ = lean_ctor_get(v___x_3219_, 0);
                        v_isSharedCheck_3247_ = (!lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v___x_3242_ = v___x_3219_;
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_3240_);
                            lean_dec(v___x_3219_);
                            v___x_3242_ = lean_box(0);
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_3217_;
            }
            26 => {
                v___x_3226_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3226_, 0, v_a_3220_);
                lean_ctor_set(v___x_3226_, 1, v_a_3222_);
                lean_ctor_set_uint8(
                    v___x_3226_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3105_,
                );
                v___x_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3227_, 0, v___x_3226_);
                if v_isShared_3225_ == 0 {
                    lean_ctor_set(v___x_3224_, 0, v___x_3227_);
                    v___x_3229_ = v___x_3224_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3229_;
            }
            28 => {
                if v_isShared_3235_ == 0 {
                    v___x_3237_ = v___x_3234_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3237_;
            }
            30 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3245_;
            }
            32 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3254_;
            }
            34 => {
                v___x_3262_ = (lean_unbox(v_a_3258_) as u8);
                lean_dec(v_a_3258_);
                if v___x_3262_ == 0 {
                    lean_dec_ref(v_arg_3091_);
                    lean_dec_ref(v_arg_3088_);
                    v___x_3263_ = lean_box(0);
                    if v_isShared_3261_ == 0 {
                        lean_ctor_set(v___x_3260_, 0, v___x_3263_);
                        v___x_3265_ = v___x_3260_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
                        v___x_3265_ = v_reuseFailAlloc_3266_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3260_);
                    v___x_3267_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3088_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if lean_obj_tag(v___x_3267_) == 0 {
                        v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
                        lean_inc(v_a_3268_);
                        lean_dec_ref_known(v___x_3267_, 1);
                        v___x_3269_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3091_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if lean_obj_tag(v___x_3269_) == 0 {
                            v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
                            v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3269_)) as u8;
                            if v_isSharedCheck_3280_ == 0 {
                                v___x_3272_ = v___x_3269_;
                                v_isShared_3273_ = v_isSharedCheck_3280_;
                                state = 36;
                                continue;
                            } else {
                                lean_inc(v_a_3270_);
                                lean_dec(v___x_3269_);
                                v___x_3272_ = lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3280_;
                                state = 36;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3268_);
                            v_a_3281_ = lean_ctor_get(v___x_3269_, 0);
                            v_isSharedCheck_3288_ = (!lean_is_exclusive(v___x_3269_)) as u8;
                            if v_isSharedCheck_3288_ == 0 {
                                v___x_3283_ = v___x_3269_;
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_3281_);
                                lean_dec(v___x_3269_);
                                v___x_3283_ = lean_box(0);
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3091_);
                        v_a_3289_ = lean_ctor_get(v___x_3267_, 0);
                        v_isSharedCheck_3296_ = (!lean_is_exclusive(v___x_3267_)) as u8;
                        if v_isSharedCheck_3296_ == 0 {
                            v___x_3291_ = v___x_3267_;
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 40;
                            continue;
                        } else {
                            lean_inc(v_a_3289_);
                            lean_dec(v___x_3267_);
                            v___x_3291_ = lean_box(0);
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            35 => {
                return v___x_3265_;
            }
            36 => {
                v___x_3274_ = l_Nat_Linear_Expr_inc(v_a_3268_);
                v___x_3275_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3275_, 0, v___x_3274_);
                lean_ctor_set(v___x_3275_, 1, v_a_3270_);
                lean_ctor_set_uint8(
                    v___x_3275_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3101_,
                );
                v___x_3276_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                if v_isShared_3273_ == 0 {
                    lean_ctor_set(v___x_3272_, 0, v___x_3276_);
                    v___x_3278_ = v___x_3272_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3278_;
            }
            38 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3286_;
            }
            40 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3294_;
            }
            42 => {
                if v_isShared_3301_ == 0 {
                    v___x_3303_ = v___x_3300_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3303_;
            }
            44 => {
                v___x_3311_ = l_Lean_Expr_cleanupAnnotations(v_a_3307_);
                v___x_3312_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
                v___x_3313_ = l_Lean_Expr_isConstOf(v___x_3311_, v___x_3312_);
                lean_dec_ref(v___x_3311_);
                if v___x_3313_ == 0 {
                    lean_dec_ref(v_arg_3091_);
                    lean_dec_ref(v_arg_3088_);
                    v___x_3314_ = lean_box(0);
                    if v_isShared_3310_ == 0 {
                        lean_ctor_set(v___x_3309_, 0, v___x_3314_);
                        v___x_3316_ = v___x_3309_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                        v___x_3316_ = v_reuseFailAlloc_3317_;
                        state = 45;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3309_);
                    v___x_3318_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if lean_obj_tag(v___x_3318_) == 0 {
                        v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
                        lean_inc(v_a_3319_);
                        lean_dec_ref_known(v___x_3318_, 1);
                        v___x_3320_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if lean_obj_tag(v___x_3320_) == 0 {
                            v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
                            v_isSharedCheck_3330_ = (!lean_is_exclusive(v___x_3320_)) as u8;
                            if v_isSharedCheck_3330_ == 0 {
                                v___x_3323_ = v___x_3320_;
                                v_isShared_3324_ = v_isSharedCheck_3330_;
                                state = 46;
                                continue;
                            } else {
                                lean_inc(v_a_3321_);
                                lean_dec(v___x_3320_);
                                v___x_3323_ = lean_box(0);
                                v_isShared_3324_ = v_isSharedCheck_3330_;
                                state = 46;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3319_);
                            v_a_3331_ = lean_ctor_get(v___x_3320_, 0);
                            v_isSharedCheck_3338_ = (!lean_is_exclusive(v___x_3320_)) as u8;
                            if v_isSharedCheck_3338_ == 0 {
                                v___x_3333_ = v___x_3320_;
                                v_isShared_3334_ = v_isSharedCheck_3338_;
                                state = 48;
                                continue;
                            } else {
                                lean_inc(v_a_3331_);
                                lean_dec(v___x_3320_);
                                v___x_3333_ = lean_box(0);
                                v_isShared_3334_ = v_isSharedCheck_3338_;
                                state = 48;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_3088_);
                        v_a_3339_ = lean_ctor_get(v___x_3318_, 0);
                        v_isSharedCheck_3346_ = (!lean_is_exclusive(v___x_3318_)) as u8;
                        if v_isSharedCheck_3346_ == 0 {
                            v___x_3341_ = v___x_3318_;
                            v_isShared_3342_ = v_isSharedCheck_3346_;
                            state = 50;
                            continue;
                        } else {
                            lean_inc(v_a_3339_);
                            lean_dec(v___x_3318_);
                            v___x_3341_ = lean_box(0);
                            v_isShared_3342_ = v_isSharedCheck_3346_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            45 => {
                return v___x_3316_;
            }
            46 => {
                v___x_3325_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3325_, 0, v_a_3319_);
                lean_ctor_set(v___x_3325_, 1, v_a_3321_);
                lean_ctor_set_uint8(
                    v___x_3325_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3313_,
                );
                v___x_3326_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3326_, 0, v___x_3325_);
                if v_isShared_3324_ == 0 {
                    lean_ctor_set(v___x_3323_, 0, v___x_3326_);
                    v___x_3328_ = v___x_3323_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
                    v___x_3328_ = v_reuseFailAlloc_3329_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3328_;
            }
            48 => {
                if v_isShared_3334_ == 0 {
                    v___x_3336_ = v___x_3333_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
                    v___x_3336_ = v_reuseFailAlloc_3337_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3336_;
            }
            50 => {
                if v_isShared_3342_ == 0 {
                    v___x_3344_ = v___x_3341_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
                    v___x_3344_ = v_reuseFailAlloc_3345_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3344_;
            }
            52 => {
                if v_isShared_3351_ == 0 {
                    v___x_3353_ = v___x_3350_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
                    v___x_3353_ = v_reuseFailAlloc_3354_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3353_;
            }
            54 => {
                v___x_3363_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3363_, 0, v_a_3357_);
                lean_ctor_set(v___x_3363_, 1, v_a_3359_);
                lean_ctor_set_uint8(
                    v___x_3363_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3094_,
                );
                v___x_3364_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3364_, 0, v___x_3363_);
                if v_isShared_3362_ == 0 {
                    lean_ctor_set(v___x_3361_, 0, v___x_3364_);
                    v___x_3366_ = v___x_3361_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_3366_;
            }
            56 => {
                if v_isShared_3372_ == 0 {
                    v___x_3374_ = v___x_3371_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
                    v___x_3374_ = v_reuseFailAlloc_3375_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_3374_;
            }
            58 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_3382_;
            }
            60 => {
                v___x_3392_ = 0;
                v___x_3393_ = l_Nat_Linear_Expr_inc(v_a_3386_);
                v___x_3394_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3394_, 0, v___x_3393_);
                lean_ctor_set(v___x_3394_, 1, v_a_3388_);
                lean_ctor_set_uint8(
                    v___x_3394_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3392_,
                );
                v___x_3395_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3395_, 0, v___x_3394_);
                if v_isShared_3391_ == 0 {
                    lean_ctor_set(v___x_3390_, 0, v___x_3395_);
                    v___x_3397_ = v___x_3390_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_3397_;
            }
            62 => {
                if v_isShared_3403_ == 0 {
                    v___x_3405_ = v___x_3402_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3406_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_3405_;
            }
            64 => {
                if v_isShared_3411_ == 0 {
                    v___x_3413_ = v___x_3410_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
                    v___x_3413_ = v_reuseFailAlloc_3414_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_3413_;
            }
            66 => {
                if v_isShared_3420_ == 0 {
                    v___x_3422_ = v___x_3419_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
                    v___x_3422_ = v_reuseFailAlloc_3423_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_3422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(
    mut v_e_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
    mut v_a_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3432_: *mut LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(
        v_e_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_,
    );
    lean_dec(v_a_3430_);
    lean_dec_ref(v_a_3429_);
    lean_dec(v_a_3428_);
    lean_dec_ref(v_a_3427_);
    lean_dec(v_a_3426_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0() -> *mut LeanObject
{
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3433_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1() -> *mut LeanObject
{
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3434_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0,
    );
    v___x_3435_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3435_, 0, v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3() -> *mut LeanObject
{
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3438_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2;
    v___x_3439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1,
    );
    v___x_3440_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    lean_ctor_set(v___x_3440_, 1, v___x_3438_);
    return v___x_3440_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
    mut v_x_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3447_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3,
                );
                v___x_3448_ = lean_st_mk_ref(v___x_3447_);
                lean_inc(v_a_3445_);
                lean_inc_ref(v_a_3444_);
                lean_inc(v_a_3443_);
                lean_inc_ref(v_a_3442_);
                lean_inc(v___x_3448_);
                v___x_3449_ = lean_apply_6(
                    v_x_3441_,
                    v___x_3448_,
                    v_a_3442_,
                    v_a_3443_,
                    v_a_3444_,
                    v_a_3445_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3449_) == 0 {
                    v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3467_ = (!lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3467_ == 0 {
                        v___x_3452_ = v___x_3449_;
                        v_isShared_3453_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3450_);
                        lean_dec(v___x_3449_);
                        v___x_3452_ = lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3448_);
                    v_a_3468_ = lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3475_ = (!lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3470_ = v___x_3449_;
                        v_isShared_3471_ = v_isSharedCheck_3475_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3468_);
                        lean_dec(v___x_3449_);
                        v___x_3470_ = lean_box(0);
                        v_isShared_3471_ = v_isSharedCheck_3475_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3454_ = lean_st_ref_get(v___x_3448_);
                lean_dec(v___x_3448_);
                v_vars_3455_ = lean_ctor_get(v___x_3454_, 1);
                v_isSharedCheck_3465_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                if v_isSharedCheck_3465_ == 0 {
                    v_unused_3466_ = lean_ctor_get(v___x_3454_, 0);
                    lean_dec(v_unused_3466_);
                    v___x_3457_ = v___x_3454_;
                    v_isShared_3458_ = v_isSharedCheck_3465_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_vars_3455_);
                    lean_dec(v___x_3454_);
                    v___x_3457_ = lean_box(0);
                    v_isShared_3458_ = v_isSharedCheck_3465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3458_ == 0 {
                    lean_ctor_set(v___x_3457_, 0, v_a_3450_);
                    v___x_3460_ = v___x_3457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3450_);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_vars_3455_);
                    v___x_3460_ = v_reuseFailAlloc_3464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3453_ == 0 {
                    lean_ctor_set(v___x_3452_, 0, v___x_3460_);
                    v___x_3462_ = v___x_3452_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3462_;
            }
            5 => {
                if v_isShared_3471_ == 0 {
                    v___x_3473_ = v___x_3470_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(
    mut v_x_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3482_: *mut LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
        v_x_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_,
    );
    lean_dec(v_a_3480_);
    lean_dec_ref(v_a_3479_);
    lean_dec(v_a_3478_);
    lean_dec_ref(v_a_3477_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(
    mut v_00_u03b1_3483_: *mut LeanObject,
    mut v_x_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
    mut v_a_3488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    v___x_3490_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
        v_x_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_,
    );
    return v___x_3490_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(
    mut v_00_u03b1_3491_: *mut LeanObject,
    mut v_x_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3498_: *mut LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(
        v_00_u03b1_3491_,
        v_x_3492_,
        v_a_3493_,
        v_a_3494_,
        v_a_3495_,
        v_a_3496_,
    );
    lean_dec(v_a_3496_);
    lean_dec_ref(v_a_3495_);
    lean_dec(v_a_3494_);
    lean_dec_ref(v_a_3493_);
    return v_res_3498_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(
    mut v_e_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: u8 = 0;
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_unused_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_3505_, 0, v_e_3499_);
                v___x_3506_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
                    v___x_3505_,
                    v_a_3500_,
                    v_a_3501_,
                    v_a_3502_,
                    v_a_3503_,
                );
                if lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
                    lean_inc(v_a_3507_);
                    v_fst_3508_ = lean_ctor_get(v_a_3507_, 0);
                    lean_inc(v_fst_3508_);
                    v_snd_3509_ = lean_ctor_get(v_a_3507_, 1);
                    lean_inc(v_snd_3509_);
                    lean_dec(v_a_3507_);
                    v___x_3510_ = lean_array_get_size(v_snd_3509_);
                    v___x_3511_ = lean_unsigned_to_nat(1);
                    v___x_3512_ = lean_nat_dec_eq(v___x_3510_, v___x_3511_);
                    if v___x_3512_ == 0 {
                        v_isSharedCheck_3531_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3531_ == 0 {
                            v_unused_3532_ = lean_ctor_get(v___x_3506_, 0);
                            lean_dec(v_unused_3532_);
                            v___x_3514_ = v___x_3506_;
                            v_isShared_3515_ = v_isSharedCheck_3531_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3506_);
                            v___x_3514_ = lean_box(0);
                            v_isShared_3515_ = v_isSharedCheck_3531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_3509_);
                        lean_dec(v_fst_3508_);
                        return v___x_3506_;
                    }
                } else {
                    return v___x_3506_;
                }
            }
            1 => {
                v___x_3516_ = 1;
                v___x_3517_ = l_Lean_sortExprs(v_snd_3509_, v___x_3516_);
                lean_dec(v_snd_3509_);
                v_fst_3518_ = lean_ctor_get(v___x_3517_, 0);
                v_snd_3519_ = lean_ctor_get(v___x_3517_, 1);
                v_isSharedCheck_3530_ = (!lean_is_exclusive(v___x_3517_)) as u8;
                if v_isSharedCheck_3530_ == 0 {
                    v___x_3521_ = v___x_3517_;
                    v_isShared_3522_ = v_isSharedCheck_3530_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3519_);
                    lean_inc(v_fst_3518_);
                    lean_dec(v___x_3517_);
                    v___x_3521_ = lean_box(0);
                    v_isShared_3522_ = v_isSharedCheck_3530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3523_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_snd_3519_, v_fst_3508_);
                lean_dec(v_snd_3519_);
                if v_isShared_3522_ == 0 {
                    lean_ctor_set(v___x_3521_, 1, v_fst_3518_);
                    lean_ctor_set(v___x_3521_, 0, v___x_3523_);
                    v___x_3525_ = v___x_3521_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3523_);
                    lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_fst_3518_);
                    v___x_3525_ = v_reuseFailAlloc_3529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3515_ == 0 {
                    lean_ctor_set(v___x_3514_, 0, v___x_3525_);
                    v___x_3527_ = v___x_3514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(
    mut v_e_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3539_: *mut LeanObject = core::ptr::null_mut();
    v_res_3539_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(
        v_e_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_,
    );
    lean_dec(v_a_3537_);
    lean_dec_ref(v_a_3536_);
    lean_dec(v_a_3535_);
    lean_dec_ref(v_a_3534_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(
    mut v_e_3540_: *mut LeanObject,
    mut v_a_3541_: *mut LeanObject,
    mut v_a_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
    mut v_a_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v_fst_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v_val_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_unused_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_a_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3602_: u8 = 0;
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3546_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___x_3546_, 0, v_e_3540_);
                v___x_3547_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
                    v___x_3546_,
                    v_a_3541_,
                    v_a_3542_,
                    v_a_3543_,
                    v_a_3544_,
                );
                if lean_obj_tag(v___x_3547_) == 0 {
                    v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
                    v_isSharedCheck_3598_ = (!lean_is_exclusive(v___x_3547_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v___x_3550_ = v___x_3547_;
                        v_isShared_3551_ = v_isSharedCheck_3598_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3548_);
                        lean_dec(v___x_3547_);
                        v___x_3550_ = lean_box(0);
                        v_isShared_3551_ = v_isSharedCheck_3598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3599_ = lean_ctor_get(v___x_3547_, 0);
                    v_isSharedCheck_3606_ = (!lean_is_exclusive(v___x_3547_)) as u8;
                    if v_isSharedCheck_3606_ == 0 {
                        v___x_3601_ = v___x_3547_;
                        v_isShared_3602_ = v_isSharedCheck_3606_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3599_);
                        lean_dec(v___x_3547_);
                        v___x_3601_ = lean_box(0);
                        v_isShared_3602_ = v_isSharedCheck_3606_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3552_ = lean_ctor_get(v_a_3548_, 0);
                lean_inc(v_fst_3552_);
                if lean_obj_tag(v_fst_3552_) == 1 {
                    v_snd_3553_ = lean_ctor_get(v_a_3548_, 1);
                    v_isSharedCheck_3592_ = (!lean_is_exclusive(v_a_3548_)) as u8;
                    if v_isSharedCheck_3592_ == 0 {
                        v_unused_3593_ = lean_ctor_get(v_a_3548_, 0);
                        lean_dec(v_unused_3593_);
                        v___x_3555_ = v_a_3548_;
                        v_isShared_3556_ = v_isSharedCheck_3592_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3553_);
                        lean_dec(v_a_3548_);
                        v___x_3555_ = lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3592_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_3552_);
                    lean_dec(v_a_3548_);
                    v___x_3594_ = lean_box(0);
                    if v_isShared_3551_ == 0 {
                        lean_ctor_set(v___x_3550_, 0, v___x_3594_);
                        v___x_3596_ = v___x_3550_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
                        v___x_3596_ = v_reuseFailAlloc_3597_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v_val_3557_ = lean_ctor_get(v_fst_3552_, 0);
                v_isSharedCheck_3591_ = (!lean_is_exclusive(v_fst_3552_)) as u8;
                if v_isSharedCheck_3591_ == 0 {
                    v___x_3559_ = v_fst_3552_;
                    v_isShared_3560_ = v_isSharedCheck_3591_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_val_3557_);
                    lean_dec(v_fst_3552_);
                    v___x_3559_ = lean_box(0);
                    v_isShared_3560_ = v_isSharedCheck_3591_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3561_ = lean_array_get_size(v_snd_3553_);
                v___x_3562_ = lean_unsigned_to_nat(1);
                v___x_3563_ = lean_nat_dec_le(v___x_3561_, v___x_3562_);
                if v___x_3563_ == 0 {
                    lean_del_object(v___x_3555_);
                    v___x_3564_ = 1;
                    v___x_3565_ = l_Lean_sortExprs(v_snd_3553_, v___x_3564_);
                    lean_dec(v_snd_3553_);
                    v_fst_3566_ = lean_ctor_get(v___x_3565_, 0);
                    v_snd_3567_ = lean_ctor_get(v___x_3565_, 1);
                    v_isSharedCheck_3581_ = (!lean_is_exclusive(v___x_3565_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3569_ = v___x_3565_;
                        v_isShared_3570_ = v_isSharedCheck_3581_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_3567_);
                        lean_inc(v_fst_3566_);
                        lean_dec(v___x_3565_);
                        v___x_3569_ = lean_box(0);
                        v_isShared_3570_ = v_isSharedCheck_3581_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_3556_ == 0 {
                        lean_ctor_set(v___x_3555_, 0, v_val_3557_);
                        v___x_3583_ = v___x_3555_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_val_3557_);
                        lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_snd_3553_);
                        v___x_3583_ = v_reuseFailAlloc_3590_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3571_ = l_Nat_Linear_ExprCnstr_applyPerm(v_snd_3567_, v_val_3557_);
                lean_dec(v_snd_3567_);
                if v_isShared_3570_ == 0 {
                    lean_ctor_set(v___x_3569_, 1, v_fst_3566_);
                    lean_ctor_set(v___x_3569_, 0, v___x_3571_);
                    v___x_3573_ = v___x_3569_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3571_);
                    lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_fst_3566_);
                    v___x_3573_ = v_reuseFailAlloc_3580_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3560_ == 0 {
                    lean_ctor_set(v___x_3559_, 0, v___x_3573_);
                    v___x_3575_ = v___x_3559_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3573_);
                    v___x_3575_ = v_reuseFailAlloc_3579_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3551_ == 0 {
                    lean_ctor_set(v___x_3550_, 0, v___x_3575_);
                    v___x_3577_ = v___x_3550_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
                    v___x_3577_ = v_reuseFailAlloc_3578_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3577_;
            }
            8 => {
                if v_isShared_3560_ == 0 {
                    lean_ctor_set(v___x_3559_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3559_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3589_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3551_ == 0 {
                    lean_ctor_set(v___x_3550_, 0, v___x_3585_);
                    v___x_3587_ = v___x_3550_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3587_;
            }
            11 => {
                return v___x_3596_;
            }
            12 => {
                if v_isShared_3602_ == 0 {
                    v___x_3604_ = v___x_3601_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
                    v___x_3604_ = v_reuseFailAlloc_3605_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(
    mut v_e_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(
        v_e_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_,
    );
    lean_dec(v_a_3611_);
    lean_dec_ref(v_a_3610_);
    lean_dec(v_a_3609_);
    lean_dec_ref(v_a_3608_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(
    mut v___y_3614_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3614_);
    return v___y_3614_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(
    mut v___y_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3616_: *mut LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(v___y_3615_);
    lean_dec_ref(v___y_3615_);
    return v_res_3616_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1() -> *mut LeanObject {
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    v___x_3618_ = lean_box(0);
    v___x_3619_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
    v___x_3620_ = l_Lean_mkConst(v___x_3619_, v___x_3618_);
    return v___x_3620_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2() -> *mut LeanObject {
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    v___x_3621_ = lean_unsigned_to_nat(0);
    v___x_3622_ = l_Lean_mkNatLit(v___x_3621_);
    return v___x_3622_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3() -> *mut LeanObject {
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    v___x_3623_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2,
    );
    v___x_3624_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3624_, 0, v___x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
    mut v_ctx_3625_: *mut LeanObject,
    mut v_a_3626_: *mut LeanObject,
    mut v_a_3627_: *mut LeanObject,
    mut v_a_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: u8 = 0;
    v___x_3631_ = lean_unsigned_to_nat(0);
    v___x_3632_ = lean_array_get_size(v_ctx_3625_);
    v___x_3633_ = lean_nat_dec_lt(v___x_3631_, v___x_3632_);
    if v___x_3633_ == 0 {
        let mut v___f_3634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ctx_3625_);
        v___f_3634_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
        v___x_3635_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1,
        );
        v___x_3636_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3,
        );
        v___x_3637_ = l_Lean_RArray_toExpr___redArg(
            v___x_3635_,
            v___f_3634_,
            v___x_3636_,
            v_a_3626_,
            v_a_3627_,
            v_a_3628_,
            v_a_3629_,
        );
        return v___x_3637_;
    } else {
        let mut v___f_3638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
        v___f_3638_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
        v___x_3639_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1,
        );
        v___x_3640_ = l_Lean_RArray_ofArray___redArg(v_ctx_3625_);
        v___x_3641_ = l_Lean_RArray_toExpr___redArg(
            v___x_3639_,
            v___f_3638_,
            v___x_3640_,
            v_a_3626_,
            v_a_3627_,
            v_a_3628_,
            v_a_3629_,
        );
        return v___x_3641_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(
    mut v_ctx_3642_: *mut LeanObject,
    mut v_a_3643_: *mut LeanObject,
    mut v_a_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
    mut v_a_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3648_: *mut LeanObject = core::ptr::null_mut();
    v_res_3648_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
        v_ctx_3642_,
        v_a_3643_,
        v_a_3644_,
        v_a_3645_,
        v_a_3646_,
    );
    lean_dec(v_a_3646_);
    lean_dec_ref(v_a_3645_);
    lean_dec(v_a_3644_);
    lean_dec_ref(v_a_3643_);
    return v_res_3648_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_SortExprs(builtin);
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
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr =
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr();
    lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr);
    l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr =
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
    lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_SortExprs(builtin);
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
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
}
