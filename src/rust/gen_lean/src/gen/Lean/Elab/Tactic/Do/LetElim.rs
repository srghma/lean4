// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: Lean.Meta.Tactic.Simp Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_ofFn___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_maxRecDepthErrorMessage, l_Lean_mkAtom,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_KVMap_getNat, l_Lean_KVMap_mergeBy, l_Lean_KVMap_setNat,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_proj___override, l_Lean_Expr_replaceFVars, l_Lean_Expr_sort___override,
    l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash, l_Lean_instBEqFVarId_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_setType, l_Lean_LocalDecl_setValue,
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f, l_Lean_instInhabitedLocalDecl_default,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    l_Lean_Meta_Simp_isCharLit, l_Lean_Meta_Simp_isOfNatNatLit, l_Lean_Meta_Simp_isOfScientificLit,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::ffi::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
use crate::ffi::{lean_expr_instantiate_rev, lean_expr_instantiate1};
pub static l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instBEqUses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instBEqUses: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instOrdUses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instOrdUses: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedUses_default: u8 = 0;
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedUses: u8 = 0;
pub static l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Do_Uses_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instAddUses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instAddUses: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_FVarUses_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instAddFVarUses: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105,
        99, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3731765604234633101 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_addMData___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_addMData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_addMData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [117, 115, 101, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10599070204101149623 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUses___closed__0_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
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
            66, 86, 97, 114, 32, 105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98,
            111, 117, 110, 100, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUses___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 62, 61, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUses___closed__4_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 97, 105, 108, 101, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorIdx(
    mut v_x_4306_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_4306_ {
        0 => {
            let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4307_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4307_;
        }
        1 => {
            let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4308_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4308_;
        }
        _ => {
            let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4309_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4309_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(
    mut v_x_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4311_ = (crate::leanh::lean_unbox(v_x_4310_) as u8);
    v_res_4312_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_boxed_4311_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(
    mut v_x_4313_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4314_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4313_);
    return v___x_4314_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(
    mut v_x_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4316_: u8 = 0;
    let mut v_res_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4316_ = (crate::leanh::lean_unbox(v_x_4315_) as u8);
    v_res_4317_ = l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(v_x_4__boxed_4316_);
    return v_res_4317_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(
    mut v_k_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4318_);
    return v_k_4318_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(
    mut v_k_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_4319_);
    crate::leanh::lean_dec(v_k_4319_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim(
    mut v_motive_4321_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4322_: *mut crate::leanh::LeanObject,
    mut v_t_4323_: u8,
    mut v_h_4324_: *mut crate::leanh::LeanObject,
    mut v_k_4325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4325_);
    return v_k_4325_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(
    mut v_motive_4326_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4327_: *mut crate::leanh::LeanObject,
    mut v_t_4328_: *mut crate::leanh::LeanObject,
    mut v_h_4329_: *mut crate::leanh::LeanObject,
    mut v_k_4330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4331_: u8 = 0;
    let mut v_res_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4331_ = (crate::leanh::lean_unbox(v_t_4328_) as u8);
    v_res_4332_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(
        v_motive_4326_,
        v_ctorIdx_4327_,
        v_t_boxed_4331_,
        v_h_4329_,
        v_k_4330_,
    );
    crate::leanh::lean_dec(v_k_4330_);
    crate::leanh::lean_dec(v_ctorIdx_4327_);
    return v_res_4332_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(
    mut v_zero_4333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_zero_4333_);
    return v_zero_4333_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(
    mut v_zero_4334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_4334_);
    crate::leanh::lean_dec(v_zero_4334_);
    return v_res_4335_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim(
    mut v_motive_4336_: *mut crate::leanh::LeanObject,
    mut v_t_4337_: u8,
    mut v_h_4338_: *mut crate::leanh::LeanObject,
    mut v_zero_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_zero_4339_);
    return v_zero_4339_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(
    mut v_motive_4340_: *mut crate::leanh::LeanObject,
    mut v_t_4341_: *mut crate::leanh::LeanObject,
    mut v_h_4342_: *mut crate::leanh::LeanObject,
    mut v_zero_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4344_: u8 = 0;
    let mut v_res_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4344_ = (crate::leanh::lean_unbox(v_t_4341_) as u8);
    v_res_4345_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(
        v_motive_4340_,
        v_t_boxed_4344_,
        v_h_4342_,
        v_zero_4343_,
    );
    crate::leanh::lean_dec(v_zero_4343_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(
    mut v_one_4346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_one_4346_);
    return v_one_4346_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(
    mut v_one_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4348_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_4347_);
    crate::leanh::lean_dec(v_one_4347_);
    return v_res_4348_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim(
    mut v_motive_4349_: *mut crate::leanh::LeanObject,
    mut v_t_4350_: u8,
    mut v_h_4351_: *mut crate::leanh::LeanObject,
    mut v_one_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_one_4352_);
    return v_one_4352_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(
    mut v_motive_4353_: *mut crate::leanh::LeanObject,
    mut v_t_4354_: *mut crate::leanh::LeanObject,
    mut v_h_4355_: *mut crate::leanh::LeanObject,
    mut v_one_4356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4357_: u8 = 0;
    let mut v_res_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4357_ = (crate::leanh::lean_unbox(v_t_4354_) as u8);
    v_res_4358_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(
        v_motive_4353_,
        v_t_boxed_4357_,
        v_h_4355_,
        v_one_4356_,
    );
    crate::leanh::lean_dec(v_one_4356_);
    return v_res_4358_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(
    mut v_many_4359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_many_4359_);
    return v_many_4359_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(
    mut v_many_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_4360_);
    crate::leanh::lean_dec(v_many_4360_);
    return v_res_4361_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim(
    mut v_motive_4362_: *mut crate::leanh::LeanObject,
    mut v_t_4363_: u8,
    mut v_h_4364_: *mut crate::leanh::LeanObject,
    mut v_many_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_many_4365_);
    return v_many_4365_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(
    mut v_motive_4366_: *mut crate::leanh::LeanObject,
    mut v_t_4367_: *mut crate::leanh::LeanObject,
    mut v_h_4368_: *mut crate::leanh::LeanObject,
    mut v_many_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4370_: u8 = 0;
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4370_ = (crate::leanh::lean_unbox(v_t_4367_) as u8);
    v_res_4371_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(
        v_motive_4366_,
        v_t_boxed_4370_,
        v_h_4368_,
        v_many_4369_,
    );
    crate::leanh::lean_dec(v_many_4369_);
    return v_res_4371_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instBEqUses_beq(mut v_x_4372_: u8, mut v_y_4373_: u8) -> u8 {
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    v___x_4374_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4372_);
    v___x_4375_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_4373_);
    v___x_4376_ = lean_nat_dec_eq(v___x_4374_, v___x_4375_);
    crate::leanh::lean_dec(v___x_4375_);
    crate::leanh::lean_dec(v___x_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(
    mut v_x_4377_: *mut crate::leanh::LeanObject,
    mut v_y_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_4379_: u8 = 0;
    let mut v_y_18__boxed_4380_: u8 = 0;
    let mut v_res_4381_: u8 = 0;
    let mut v_r_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_4379_ = (crate::leanh::lean_unbox(v_x_4377_) as u8);
    v_y_18__boxed_4380_ = (crate::leanh::lean_unbox(v_y_4378_) as u8);
    v_res_4381_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_4379_, v_y_18__boxed_4380_);
    v_r_4382_ = crate::leanh::lean_box((v_res_4381_) as usize);
    return v_r_4382_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instOrdUses_ord(mut v_x_4385_: u8, mut v_y_4386_: u8) -> u8 {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    v___x_4387_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4385_);
    v___x_4388_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_4386_);
    v___x_4389_ = lean_nat_dec_lt(v___x_4387_, v___x_4388_);
    if v___x_4389_ == 0 {
        let mut v___x_4390_: u8 = 0;
        v___x_4390_ = lean_nat_dec_eq(v___x_4387_, v___x_4388_);
        crate::leanh::lean_dec(v___x_4388_);
        crate::leanh::lean_dec(v___x_4387_);
        if v___x_4390_ == 0 {
            let mut v___x_4391_: u8 = 0;
            v___x_4391_ = 2;
            return v___x_4391_;
        } else {
            let mut v___x_4392_: u8 = 0;
            v___x_4392_ = 1;
            return v___x_4392_;
        }
    } else {
        let mut v___x_4393_: u8 = 0;
        crate::leanh::lean_dec(v___x_4388_);
        crate::leanh::lean_dec(v___x_4387_);
        v___x_4393_ = 0;
        return v___x_4393_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(
    mut v_x_4394_: *mut crate::leanh::LeanObject,
    mut v_y_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_4396_: u8 = 0;
    let mut v_y_31__boxed_4397_: u8 = 0;
    let mut v_res_4398_: u8 = 0;
    let mut v_r_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4396_ = (crate::leanh::lean_unbox(v_x_4394_) as u8);
    v_y_31__boxed_4397_ = (crate::leanh::lean_unbox(v_y_4395_) as u8);
    v_res_4398_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_4396_, v_y_31__boxed_4397_);
    v_r_4399_ = crate::leanh::lean_box((v_res_4398_) as usize);
    return v_r_4399_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default() -> u8 {
    let mut v___x_4402_: u8 = 0;
    v___x_4402_ = 0;
    return v___x_4402_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedUses() -> u8 {
    let mut v___x_4403_: u8 = 0;
    v___x_4403_ = 0;
    return v___x_4403_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_add(mut v_x_4404_: u8, mut v_x_4405_: u8) -> u8 {
    if v_x_4404_ == 0 {
        return v_x_4405_;
    } else {
        if v_x_4405_ == 0 {
            return v_x_4404_;
        } else {
            let mut v___x_4406_: u8 = 0;
            v___x_4406_ = 2;
            return v___x_4406_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_add___boxed(
    mut v_x_4407_: *mut crate::leanh::LeanObject,
    mut v_x_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_4409_: u8 = 0;
    let mut v_x_31__boxed_4410_: u8 = 0;
    let mut v_res_4411_: u8 = 0;
    let mut v_r_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4409_ = (crate::leanh::lean_unbox(v_x_4407_) as u8);
    v_x_31__boxed_4410_ = (crate::leanh::lean_unbox(v_x_4408_) as u8);
    v_res_4411_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_4409_, v_x_31__boxed_4410_);
    v_r_4412_ = crate::leanh::lean_box((v_res_4411_) as usize);
    return v_r_4412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toNat(mut v_x_4413_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4413_ {
        0 => {
            let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4414_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4414_;
        }
        1 => {
            let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4415_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4415_;
        }
        _ => {
            let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4416_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4416_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(
    mut v_x_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_34__boxed_4418_: u8 = 0;
    let mut v_res_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_34__boxed_4418_ = (crate::leanh::lean_unbox(v_x_4417_) as u8);
    v_res_4419_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_4418_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_fromNat(
    mut v_x_4420_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    v___x_4421_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4422_ = lean_nat_dec_eq(v_x_4420_, v___x_4421_);
    if v___x_4422_ == 0 {
        let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4424_: u8 = 0;
        v___x_4423_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4424_ = lean_nat_dec_eq(v_x_4420_, v___x_4423_);
        if v___x_4424_ == 0 {
            let mut v___x_4425_: u8 = 0;
            v___x_4425_ = 2;
            return v___x_4425_;
        } else {
            let mut v___x_4426_: u8 = 0;
            v___x_4426_ = 1;
            return v___x_4426_;
        }
    } else {
        let mut v___x_4427_: u8 = 0;
        v___x_4427_ = 0;
        return v___x_4427_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(
    mut v_x_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4429_: u8 = 0;
    let mut v_r_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_4428_);
    crate::leanh::lean_dec(v_x_4428_);
    v_r_4430_ = crate::leanh::lean_box((v_res_4429_) as usize);
    return v_r_4430_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_4433_: *mut crate::leanh::LeanObject,
    mut v_x_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4440_: u8 = 0;
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: u64 = 0;
    let mut v___x_4443_: u64 = 0;
    let mut v___x_4444_: u64 = 0;
    let mut v_fold_4445_: u64 = 0;
    let mut v___x_4446_: u64 = 0;
    let mut v___x_4447_: u64 = 0;
    let mut v___x_4448_: u64 = 0;
    let mut v___x_4449_: usize = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: usize = 0;
    let mut v___x_4452_: usize = 0;
    let mut v___x_4453_: usize = 0;
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4434_) == 0 {
                    return v_x_4433_;
                } else {
                    v_key_4435_ = crate::leanh::lean_ctor_get(v_x_4434_, 0);
                    v_value_4436_ = crate::leanh::lean_ctor_get(v_x_4434_, 1);
                    v_tail_4437_ = crate::leanh::lean_ctor_get(v_x_4434_, 2);
                    v_isSharedCheck_4460_ = (!crate::leanh::lean_is_exclusive(v_x_4434_)) as u8;
                    if v_isSharedCheck_4460_ == 0 {
                        v___x_4439_ = v_x_4434_;
                        v_isShared_4440_ = v_isSharedCheck_4460_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4437_);
                        crate::leanh::lean_inc(v_value_4436_);
                        crate::leanh::lean_inc(v_key_4435_);
                        crate::leanh::lean_dec(v_x_4434_);
                        v___x_4439_ = crate::leanh::lean_box(0);
                        v_isShared_4440_ = v_isSharedCheck_4460_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4441_ = lean_array_get_size(v_x_4433_);
                v___x_4442_ = l_Lean_instHashableFVarId_hash(v_key_4435_);
                v___x_4443_ = 32u64;
                v___x_4444_ = lean_uint64_shift_right(v___x_4442_, v___x_4443_);
                v_fold_4445_ = lean_uint64_xor(v___x_4442_, v___x_4444_);
                v___x_4446_ = 16u64;
                v___x_4447_ = lean_uint64_shift_right(v_fold_4445_, v___x_4446_);
                v___x_4448_ = lean_uint64_xor(v_fold_4445_, v___x_4447_);
                v___x_4449_ = lean_uint64_to_usize(v___x_4448_);
                v___x_4450_ = lean_usize_of_nat(v___x_4441_);
                v___x_4451_ = 1usize;
                v___x_4452_ = lean_usize_sub(v___x_4450_, v___x_4451_);
                v___x_4453_ = lean_usize_land(v___x_4449_, v___x_4452_);
                v___x_4454_ = lean_array_uget_borrowed(v_x_4433_, v___x_4453_);
                crate::leanh::lean_inc(v___x_4454_);
                if v_isShared_4440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4439_, 2, v___x_4454_);
                    v___x_4456_ = v___x_4439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_key_4435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_value_4436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 2, v___x_4454_);
                    v___x_4456_ = v_reuseFailAlloc_4459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4457_ = lean_array_uset(v_x_4433_, v___x_4453_, v___x_4456_);
                v_x_4433_ = v___x_4457_;
                v_x_4434_ = v_tail_4437_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(
    mut v_i_4461_: *mut crate::leanh::LeanObject,
    mut v_source_4462_: *mut crate::leanh::LeanObject,
    mut v_target_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_es_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4464_ = lean_array_get_size(v_source_4462_);
                v___x_4465_ = lean_nat_dec_lt(v_i_4461_, v___x_4464_);
                if v___x_4465_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4462_);
                    crate::leanh::lean_dec(v_i_4461_);
                    return v_target_4463_;
                } else {
                    v_es_4466_ = lean_array_fget(v_source_4462_, v_i_4461_);
                    v___x_4467_ = crate::leanh::lean_box(0);
                    v_source_4468_ = lean_array_fset(v_source_4462_, v_i_4461_, v___x_4467_);
                    v_target_4469_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_4463_, v_es_4466_);
                    v___x_4470_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4471_ = lean_nat_add(v_i_4461_, v___x_4470_);
                    crate::leanh::lean_dec(v_i_4461_);
                    v_i_4461_ = v___x_4471_;
                    v_source_4462_ = v_source_4468_;
                    v_target_4463_ = v_target_4469_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(
    mut v_data_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = lean_array_get_size(v_data_4473_);
    v___x_4475_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4476_ = lean_nat_mul(v___x_4474_, v___x_4475_);
    v___x_4477_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4478_ = crate::leanh::lean_box(0);
    v___x_4479_ = lean_mk_array(v_nbuckets_4476_, v___x_4478_);
    v___x_4480_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_4477_, v_data_4473_, v___x_4479_);
    return v___x_4480_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(
    mut v_a_4481_: *mut crate::leanh::LeanObject,
    mut v_x_4482_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4483_: u8 = 0;
    let mut v_key_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4482_) == 0 {
                    v___x_4483_ = 0;
                    return v___x_4483_;
                } else {
                    v_key_4484_ = crate::leanh::lean_ctor_get(v_x_4482_, 0);
                    v_tail_4485_ = crate::leanh::lean_ctor_get(v_x_4482_, 2);
                    v___x_4486_ = l_Lean_instBEqFVarId_beq(v_key_4484_, v_a_4481_);
                    if v___x_4486_ == 0 {
                        v_x_4482_ = v_tail_4485_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4486_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(
    mut v_a_4488_: *mut crate::leanh::LeanObject,
    mut v_x_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4488_, v_x_4489_);
    crate::leanh::lean_dec(v_x_4489_);
    crate::leanh::lean_dec(v_a_4488_);
    v_r_4491_ = crate::leanh::lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(
    mut v_x3_4492_: u8,
    mut v_x_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4500_: u8 = 0;
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4493_) == 0 {
                    v___x_4494_ = crate::leanh::lean_box((v_x3_4492_) as usize);
                    v___x_4495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4494_);
                    return v___x_4495_;
                } else {
                    v_val_4496_ = crate::leanh::lean_ctor_get(v_x_4493_, 0);
                    v_isSharedCheck_4506_ = (!crate::leanh::lean_is_exclusive(v_x_4493_)) as u8;
                    if v_isSharedCheck_4506_ == 0 {
                        v___x_4498_ = v_x_4493_;
                        v_isShared_4499_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4496_);
                        crate::leanh::lean_dec(v_x_4493_);
                        v___x_4498_ = crate::leanh::lean_box(0);
                        v_isShared_4499_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4500_ = (crate::leanh::lean_unbox(v_val_4496_) as u8);
                crate::leanh::lean_dec(v_val_4496_);
                v___x_4501_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_4492_, v___x_4500_);
                v___x_4502_ = crate::leanh::lean_box((v___x_4501_) as usize);
                if v_isShared_4499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4498_, 0, v___x_4502_);
                    v___x_4504_ = v___x_4498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(
    mut v_x3_4507_: *mut crate::leanh::LeanObject,
    mut v_x_4508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x3_854__boxed_4509_: u8 = 0;
    let mut v_res_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x3_854__boxed_4509_ = (crate::leanh::lean_unbox(v_x3_4507_) as u8);
    v_res_4510_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_854__boxed_4509_, v_x_4508_);
    return v_res_4510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(
    mut v_x3_4511_: u8,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_x_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v_tail_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4513_) == 0 {
                    v___x_4514_ = crate::leanh::lean_box(0);
                    v___x_4515_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_4511_, v___x_4514_);
                    v_val_4516_ = crate::leanh::lean_ctor_get(v___x_4515_, 0);
                    crate::leanh::lean_inc(v_val_4516_);
                    crate::leanh::lean_dec(v___x_4515_);
                    v___x_4517_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4517_, 0, v_a_4512_);
                    crate::leanh::lean_ctor_set(v___x_4517_, 1, v_val_4516_);
                    crate::leanh::lean_ctor_set(v___x_4517_, 2, v_x_4513_);
                    return v___x_4517_;
                } else {
                    v_key_4518_ = crate::leanh::lean_ctor_get(v_x_4513_, 0);
                    v_value_4519_ = crate::leanh::lean_ctor_get(v_x_4513_, 1);
                    v_tail_4520_ = crate::leanh::lean_ctor_get(v_x_4513_, 2);
                    v_isSharedCheck_4535_ = (!crate::leanh::lean_is_exclusive(v_x_4513_)) as u8;
                    if v_isSharedCheck_4535_ == 0 {
                        v___x_4522_ = v_x_4513_;
                        v_isShared_4523_ = v_isSharedCheck_4535_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4520_);
                        crate::leanh::lean_inc(v_value_4519_);
                        crate::leanh::lean_inc(v_key_4518_);
                        crate::leanh::lean_dec(v_x_4513_);
                        v___x_4522_ = crate::leanh::lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4535_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4524_ = l_Lean_instBEqFVarId_beq(v_key_4518_, v_a_4512_);
                if v___x_4524_ == 0 {
                    v_tail_4525_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_4511_, v_a_4512_, v_tail_4520_);
                    if v_isShared_4523_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4522_, 2, v_tail_4525_);
                        v___x_4527_ = v___x_4522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4528_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_key_4518_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_value_4519_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_tail_4525_);
                        v___x_4527_ = v_reuseFailAlloc_4528_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_4518_);
                    v___x_4529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4529_, 0, v_value_4519_);
                    v___x_4530_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_4511_, v___x_4529_);
                    v_val_4531_ = crate::leanh::lean_ctor_get(v___x_4530_, 0);
                    crate::leanh::lean_inc(v_val_4531_);
                    crate::leanh::lean_dec(v___x_4530_);
                    if v_isShared_4523_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4522_, 1, v_val_4531_);
                        crate::leanh::lean_ctor_set(v___x_4522_, 0, v_a_4512_);
                        v___x_4533_ = v___x_4522_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4512_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_val_4531_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 2, v_tail_4520_);
                        v___x_4533_ = v_reuseFailAlloc_4534_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4527_;
            }
            3 => {
                return v___x_4533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(
    mut v_x3_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_x_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x3_886__boxed_4539_: u8 = 0;
    let mut v_res_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x3_886__boxed_4539_ = (crate::leanh::lean_unbox(v_x3_4536_) as u8);
    v_res_4540_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_886__boxed_4539_, v_a_4537_, v_x_4538_);
    return v_res_4540_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(
    mut v_x3_4541_: u8,
    mut v_m_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u64 = 0;
    let mut v___x_4551_: u64 = 0;
    let mut v___x_4552_: u64 = 0;
    let mut v_fold_4553_: u64 = 0;
    let mut v___x_4554_: u64 = 0;
    let mut v___x_4555_: u64 = 0;
    let mut v___x_4556_: u64 = 0;
    let mut v___x_4557_: usize = 0;
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: usize = 0;
    let mut v___x_4561_: usize = 0;
    let mut v_bkt_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v_val_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4544_ = crate::leanh::lean_ctor_get(v_m_4542_, 0);
                v_buckets_4545_ = crate::leanh::lean_ctor_get(v_m_4542_, 1);
                v_isSharedCheck_4594_ = (!crate::leanh::lean_is_exclusive(v_m_4542_)) as u8;
                if v_isSharedCheck_4594_ == 0 {
                    v___x_4547_ = v_m_4542_;
                    v_isShared_4548_ = v_isSharedCheck_4594_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4545_);
                    crate::leanh::lean_inc(v_size_4544_);
                    crate::leanh::lean_dec(v_m_4542_);
                    v___x_4547_ = crate::leanh::lean_box(0);
                    v_isShared_4548_ = v_isSharedCheck_4594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4549_ = lean_array_get_size(v_buckets_4545_);
                v___x_4550_ = l_Lean_instHashableFVarId_hash(v_a_4543_);
                v___x_4551_ = 32u64;
                v___x_4552_ = lean_uint64_shift_right(v___x_4550_, v___x_4551_);
                v_fold_4553_ = lean_uint64_xor(v___x_4550_, v___x_4552_);
                v___x_4554_ = 16u64;
                v___x_4555_ = lean_uint64_shift_right(v_fold_4553_, v___x_4554_);
                v___x_4556_ = lean_uint64_xor(v_fold_4553_, v___x_4555_);
                v___x_4557_ = lean_uint64_to_usize(v___x_4556_);
                v___x_4558_ = lean_usize_of_nat(v___x_4549_);
                v___x_4559_ = 1usize;
                v___x_4560_ = lean_usize_sub(v___x_4558_, v___x_4559_);
                v___x_4561_ = lean_usize_land(v___x_4557_, v___x_4560_);
                v_bkt_4562_ = lean_array_uget_borrowed(v_buckets_4545_, v___x_4561_);
                v___x_4563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4543_, v_bkt_4562_);
                if v___x_4563_ == 0 {
                    v___x_4564_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4565_ = lean_nat_add(v_size_4544_, v___x_4564_);
                    crate::leanh::lean_dec(v_size_4544_);
                    v___x_4566_ = crate::leanh::lean_box((v_x3_4541_) as usize);
                    crate::leanh::lean_inc(v_bkt_4562_);
                    v___x_4567_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4567_, 0, v_a_4543_);
                    crate::leanh::lean_ctor_set(v___x_4567_, 1, v___x_4566_);
                    crate::leanh::lean_ctor_set(v___x_4567_, 2, v_bkt_4562_);
                    v_buckets_x27_4568_ =
                        lean_array_uset(v_buckets_4545_, v___x_4561_, v___x_4567_);
                    v___x_4569_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4570_ = lean_nat_mul(v_size_x27_4565_, v___x_4569_);
                    v___x_4571_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4572_ = lean_nat_div(v___x_4570_, v___x_4571_);
                    crate::leanh::lean_dec(v___x_4570_);
                    v___x_4573_ = lean_array_get_size(v_buckets_x27_4568_);
                    v___x_4574_ = lean_nat_dec_le(v___x_4572_, v___x_4573_);
                    crate::leanh::lean_dec(v___x_4572_);
                    if v___x_4574_ == 0 {
                        v_val_4575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_4568_);
                        if v_isShared_4548_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4547_, 1, v_val_4575_);
                            crate::leanh::lean_ctor_set(v___x_4547_, 0, v_size_x27_4565_);
                            v___x_4577_ = v___x_4547_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4578_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4578_,
                                0,
                                v_size_x27_4565_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_val_4575_);
                            v___x_4577_ = v_reuseFailAlloc_4578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4548_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4547_, 1, v_buckets_x27_4568_);
                            crate::leanh::lean_ctor_set(v___x_4547_, 0, v_size_x27_4565_);
                            v___x_4580_ = v___x_4547_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4581_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4581_,
                                0,
                                v_size_x27_4565_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4581_,
                                1,
                                v_buckets_x27_4568_,
                            );
                            v___x_4580_ = v_reuseFailAlloc_4581_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4562_);
                    v___x_4582_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4583_ =
                        lean_array_uset(v_buckets_4545_, v___x_4561_, v___x_4582_);
                    crate::leanh::lean_inc(v_a_4543_);
                    v_bkt_x27_4584_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_4541_, v_a_4543_, v_bkt_4562_);
                    v___x_4591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4543_, v_bkt_x27_4584_);
                    crate::leanh::lean_dec(v_a_4543_);
                    if v___x_4591_ == 0 {
                        v___x_4592_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4593_ = lean_nat_sub(v_size_4544_, v___x_4592_);
                        crate::leanh::lean_dec(v_size_4544_);
                        v___y_4586_ = v___x_4593_;
                        state = 4;
                        continue;
                    } else {
                        v___y_4586_ = v_size_4544_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4577_;
            }
            3 => {
                return v___x_4580_;
            }
            4 => {
                v___x_4587_ = lean_array_uset(v_buckets_x27_4583_, v___x_4561_, v_bkt_x27_4584_);
                if v_isShared_4548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4547_, 1, v___x_4587_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 0, v___y_4586_);
                    v___x_4589_ = v___x_4547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___y_4586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 1, v___x_4587_);
                    v___x_4589_ = v_reuseFailAlloc_4590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(
    mut v_x3_4595_: *mut crate::leanh::LeanObject,
    mut v_m_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x3_934__boxed_4598_: u8 = 0;
    let mut v_res_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x3_934__boxed_4598_ = (crate::leanh::lean_unbox(v_x3_4595_) as u8);
    v_res_4599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_934__boxed_4598_, v_m_4596_, v_a_4597_);
    return v_res_4599_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(
    mut v_x_4600_: *mut crate::leanh::LeanObject,
    mut v_x_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4601_) == 0 {
                    return v_x_4600_;
                } else {
                    v_key_4602_ = crate::leanh::lean_ctor_get(v_x_4601_, 0);
                    crate::leanh::lean_inc(v_key_4602_);
                    v_value_4603_ = crate::leanh::lean_ctor_get(v_x_4601_, 1);
                    crate::leanh::lean_inc(v_value_4603_);
                    v_tail_4604_ = crate::leanh::lean_ctor_get(v_x_4601_, 2);
                    crate::leanh::lean_inc(v_tail_4604_);
                    crate::leanh::lean_dec_ref_known(v_x_4601_, 3);
                    v___x_4605_ = (crate::leanh::lean_unbox(v_value_4603_) as u8);
                    crate::leanh::lean_dec(v_value_4603_);
                    v___x_4606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_4605_, v_x_4600_, v_key_4602_);
                    v_x_4600_ = v___x_4606_;
                    v_x_4601_ = v_tail_4604_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(
    mut v_as_4608_: *mut crate::leanh::LeanObject,
    mut v_i_4609_: usize,
    mut v_stop_4610_: usize,
    mut v_b_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: usize = 0;
    let mut v___x_4616_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4612_ = lean_usize_dec_eq(v_i_4609_, v_stop_4610_);
                if v___x_4612_ == 0 {
                    v___x_4613_ = lean_array_uget_borrowed(v_as_4608_, v_i_4609_);
                    crate::leanh::lean_inc(v___x_4613_);
                    v___x_4614_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_4611_, v___x_4613_);
                    v___x_4615_ = 1usize;
                    v___x_4616_ = lean_usize_add(v_i_4609_, v___x_4615_);
                    v_i_4609_ = v___x_4616_;
                    v_b_4611_ = v___x_4614_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4611_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(
    mut v_as_4618_: *mut crate::leanh::LeanObject,
    mut v_i_4619_: *mut crate::leanh::LeanObject,
    mut v_stop_4620_: *mut crate::leanh::LeanObject,
    mut v_b_4621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4622_: usize = 0;
    let mut v_stop_boxed_4623_: usize = 0;
    let mut v_res_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4622_ = crate::leanh::lean_unbox_usize(v_i_4619_);
    crate::leanh::lean_dec(v_i_4619_);
    v_stop_boxed_4623_ = crate::leanh::lean_unbox_usize(v_stop_4620_);
    crate::leanh::lean_dec(v_stop_4620_);
    v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_4618_, v_i_boxed_4622_, v_stop_boxed_4623_, v_b_4621_);
    crate::leanh::lean_dec_ref(v_as_4618_);
    return v_res_4624_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_FVarUses_add(
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_b_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u8 = 0;
    v_buckets_4627_ = crate::leanh::lean_ctor_get(v_a_4625_, 1);
    v___x_4628_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4629_ = lean_array_get_size(v_buckets_4627_);
    v___x_4630_ = lean_nat_dec_lt(v___x_4628_, v___x_4629_);
    if v___x_4630_ == 0 {
        return v_b_4626_;
    } else {
        let mut v___x_4631_: u8 = 0;
        v___x_4631_ = lean_nat_dec_le(v___x_4629_, v___x_4629_);
        if v___x_4631_ == 0 {
            if v___x_4630_ == 0 {
                return v_b_4626_;
            } else {
                let mut v___x_4632_: usize = 0;
                let mut v___x_4633_: usize = 0;
                let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4632_ = 0usize;
                v___x_4633_ = lean_usize_of_nat(v___x_4629_);
                v___x_4634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_4627_, v___x_4632_, v___x_4633_, v_b_4626_);
                return v___x_4634_;
            }
        } else {
            let mut v___x_4635_: usize = 0;
            let mut v___x_4636_: usize = 0;
            let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4635_ = 0usize;
            v___x_4636_ = lean_usize_of_nat(v___x_4629_);
            v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_4627_, v___x_4635_, v___x_4636_, v_b_4626_);
            return v___x_4637_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_b_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4640_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_4638_, v_b_4639_);
    crate::leanh::lean_dec_ref(v_a_4638_);
    return v_res_4640_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(
    mut v_00_u03b2_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_x_4643_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4644_: u8 = 0;
    v___x_4644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4642_, v_x_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(
    mut v_00_u03b2_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_x_4647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4648_: u8 = 0;
    let mut v_r_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_4645_, v_a_4646_, v_x_4647_);
    crate::leanh::lean_dec(v_x_4647_);
    crate::leanh::lean_dec(v_a_4646_);
    v_r_4649_ = crate::leanh::lean_box((v_res_4648_) as usize);
    return v_r_4649_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(
    mut v_00_u03b2_4650_: *mut crate::leanh::LeanObject,
    mut v_data_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_4651_);
    return v___x_4652_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4653_: *mut crate::leanh::LeanObject,
    mut v_i_4654_: *mut crate::leanh::LeanObject,
    mut v_source_4655_: *mut crate::leanh::LeanObject,
    mut v_target_4656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4657_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_4654_, v_source_4655_, v_target_4656_);
    return v___x_4657_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_4658_: *mut crate::leanh::LeanObject,
    mut v_x_4659_: *mut crate::leanh::LeanObject,
    mut v_x_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_4659_, v_x_4660_);
    return v___x_4661_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(
    mut v_x_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4664_) == 0 {
        let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4665_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4665_;
    } else {
        let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4666_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4666_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(
    mut v_x_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_4667_);
    crate::leanh::lean_dec(v_x_4667_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(
    mut v_n_4669_: *mut crate::leanh::LeanObject,
    mut v_x_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_4670_);
    return v___x_4671_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(
    mut v_n_4672_: *mut crate::leanh::LeanObject,
    mut v_x_4673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_4672_, v_x_4673_);
    crate::leanh::lean_dec(v_x_4673_);
    crate::leanh::lean_dec(v_n_4672_);
    return v_res_4674_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(
    mut v_t_4675_: *mut crate::leanh::LeanObject,
    mut v_k_4676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4675_) == 0 {
        return v_k_4676_;
    } else {
        let mut v_uses_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_uses_4677_ = crate::leanh::lean_ctor_get(v_t_4675_, 0);
        crate::leanh::lean_inc_ref(v_uses_4677_);
        crate::leanh::lean_dec_ref_known(v_t_4675_, 1);
        v___x_4678_ = crate::leanh::lean_apply_1(v_k_4676_, v_uses_4677_);
        return v___x_4678_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(
    mut v_n_4679_: *mut crate::leanh::LeanObject,
    mut v_motive_4680_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4681_: *mut crate::leanh::LeanObject,
    mut v_t_4682_: *mut crate::leanh::LeanObject,
    mut v_h_4683_: *mut crate::leanh::LeanObject,
    mut v_k_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4685_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4682_, v_k_4684_);
    return v___x_4685_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(
    mut v_n_4686_: *mut crate::leanh::LeanObject,
    mut v_motive_4687_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4688_: *mut crate::leanh::LeanObject,
    mut v_t_4689_: *mut crate::leanh::LeanObject,
    mut v_h_4690_: *mut crate::leanh::LeanObject,
    mut v_k_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4692_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(
        v_n_4686_,
        v_motive_4687_,
        v_ctorIdx_4688_,
        v_t_4689_,
        v_h_4690_,
        v_k_4691_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4688_);
    crate::leanh::lean_dec(v_n_4686_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(
    mut v_t_4693_: *mut crate::leanh::LeanObject,
    mut v_none_4694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4695_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4693_, v_none_4694_);
    return v___x_4695_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim(
    mut v_n_4696_: *mut crate::leanh::LeanObject,
    mut v_motive_4697_: *mut crate::leanh::LeanObject,
    mut v_t_4698_: *mut crate::leanh::LeanObject,
    mut v_h_4699_: *mut crate::leanh::LeanObject,
    mut v_none_4700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4698_, v_none_4700_);
    return v___x_4701_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(
    mut v_n_4702_: *mut crate::leanh::LeanObject,
    mut v_motive_4703_: *mut crate::leanh::LeanObject,
    mut v_t_4704_: *mut crate::leanh::LeanObject,
    mut v_h_4705_: *mut crate::leanh::LeanObject,
    mut v_none_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(
        v_n_4702_,
        v_motive_4703_,
        v_t_4704_,
        v_h_4705_,
        v_none_4706_,
    );
    crate::leanh::lean_dec(v_n_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(
    mut v_t_4708_: *mut crate::leanh::LeanObject,
    mut v_some_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4708_, v_some_4709_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim(
    mut v_n_4711_: *mut crate::leanh::LeanObject,
    mut v_motive_4712_: *mut crate::leanh::LeanObject,
    mut v_t_4713_: *mut crate::leanh::LeanObject,
    mut v_h_4714_: *mut crate::leanh::LeanObject,
    mut v_some_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4716_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4713_, v_some_4715_);
    return v___x_4716_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(
    mut v_n_4717_: *mut crate::leanh::LeanObject,
    mut v_motive_4718_: *mut crate::leanh::LeanObject,
    mut v_t_4719_: *mut crate::leanh::LeanObject,
    mut v_h_4720_: *mut crate::leanh::LeanObject,
    mut v_some_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(
        v_n_4717_,
        v_motive_4718_,
        v_t_4719_,
        v_h_4720_,
        v_some_4721_,
    );
    crate::leanh::lean_dec(v_n_4717_);
    return v_res_4722_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12;
    v___x_4748_ = l_Lean_mkAtom(v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4749_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13,
    );
    v___x_4750_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4751_ = lean_array_push(v___x_4750_, v___x_4749_);
    return v___x_4751_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14,
    );
    v___x_4753_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11;
    v___x_4754_ = crate::leanh::lean_box(2);
    v___x_4755_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4755_, 0, v___x_4754_);
    crate::leanh::lean_ctor_set(v___x_4755_, 1, v___x_4753_);
    crate::leanh::lean_ctor_set(v___x_4755_, 2, v___x_4752_);
    return v___x_4755_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15,
    );
    v___x_4757_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4758_ = lean_array_push(v___x_4757_, v___x_4756_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16,
    );
    v___x_4760_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9;
    v___x_4761_ = crate::leanh::lean_box(2);
    v___x_4762_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4762_, 0, v___x_4761_);
    crate::leanh::lean_ctor_set(v___x_4762_, 1, v___x_4760_);
    crate::leanh::lean_ctor_set(v___x_4762_, 2, v___x_4759_);
    return v___x_4762_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17,
    );
    v___x_4764_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4765_ = lean_array_push(v___x_4764_, v___x_4763_);
    return v___x_4765_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18,
    );
    v___x_4767_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7;
    v___x_4768_ = crate::leanh::lean_box(2);
    v___x_4769_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4769_, 0, v___x_4768_);
    crate::leanh::lean_ctor_set(v___x_4769_, 1, v___x_4767_);
    crate::leanh::lean_ctor_set(v___x_4769_, 2, v___x_4766_);
    return v___x_4769_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19,
    );
    v___x_4771_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4772_ = lean_array_push(v___x_4771_, v___x_4770_);
    return v___x_4772_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20,
    );
    v___x_4774_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4;
    v___x_4775_ = crate::leanh::lean_box(2);
    v___x_4776_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4776_, 0, v___x_4775_);
    crate::leanh::lean_ctor_set(v___x_4776_, 1, v___x_4774_);
    crate::leanh::lean_ctor_set(v___x_4776_, 2, v___x_4773_);
    return v___x_4776_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21,
    );
    return v___x_4777_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(
    mut v_numBVars_4778_: *mut crate::leanh::LeanObject,
    mut v_n_4779_: *mut crate::leanh::LeanObject,
    mut v_i_4780_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: u8 = 0;
    v___x_4781_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4782_ = lean_nat_sub(v_numBVars_4778_, v___x_4781_);
    v___x_4783_ = lean_nat_sub(v___x_4782_, v_n_4779_);
    crate::leanh::lean_dec(v___x_4782_);
    v___x_4784_ = lean_nat_dec_eq(v_i_4780_, v___x_4783_);
    crate::leanh::lean_dec(v___x_4783_);
    if v___x_4784_ == 0 {
        let mut v___x_4785_: u8 = 0;
        v___x_4785_ = 0;
        return v___x_4785_;
    } else {
        let mut v___x_4786_: u8 = 0;
        v___x_4786_ = 1;
        return v___x_4786_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(
    mut v_numBVars_4787_: *mut crate::leanh::LeanObject,
    mut v_n_4788_: *mut crate::leanh::LeanObject,
    mut v_i_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: u8 = 0;
    let mut v_r_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(
        v_numBVars_4787_,
        v_n_4788_,
        v_i_4789_,
    );
    crate::leanh::lean_dec(v_i_4789_);
    crate::leanh::lean_dec(v_n_4788_);
    crate::leanh::lean_dec(v_numBVars_4787_);
    v_r_4791_ = crate::leanh::lean_box((v_res_4790_) as usize);
    return v_r_4791_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(
    mut v_numBVars_4792_: *mut crate::leanh::LeanObject,
    mut v_n_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_numBVars_4792_);
    v___f_4794_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4794_, 0, v_numBVars_4792_);
    crate::leanh::lean_closure_set(v___f_4794_, 1, v_n_4793_);
    v___x_4795_ = l_Array_ofFn___redArg(v_numBVars_4792_, v___f_4794_);
    v___x_4796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single(
    mut v_numBVars_4797_: *mut crate::leanh::LeanObject,
    mut v_n_4798_: *mut crate::leanh::LeanObject,
    mut v_x_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_4797_, v_n_4798_);
    return v___x_4800_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_pop(
    mut v_numBVars_4805_: *mut crate::leanh::LeanObject,
    mut v_x_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uses_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4806_) == 0 {
                    v___x_4807_ = l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0;
                    return v___x_4807_;
                } else {
                    v_uses_4808_ = crate::leanh::lean_ctor_get(v_x_4806_, 0);
                    v_isSharedCheck_4821_ = (!crate::leanh::lean_is_exclusive(v_x_4806_)) as u8;
                    if v_isSharedCheck_4821_ == 0 {
                        v___x_4810_ = v_x_4806_;
                        v_isShared_4811_ = v_isSharedCheck_4821_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_uses_4808_);
                        crate::leanh::lean_dec(v_x_4806_);
                        v___x_4810_ = crate::leanh::lean_box(0);
                        v_isShared_4811_ = v_isSharedCheck_4821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4812_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4813_ = lean_nat_add(v_numBVars_4805_, v___x_4812_);
                v___x_4814_ = lean_nat_sub(v___x_4813_, v___x_4812_);
                crate::leanh::lean_dec(v___x_4813_);
                v___x_4815_ = lean_array_fget(v_uses_4808_, v___x_4814_);
                crate::leanh::lean_dec(v___x_4814_);
                v___x_4816_ = lean_array_pop(v_uses_4808_);
                if v_isShared_4811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4810_, 0, v___x_4816_);
                    v___x_4818_ = v___x_4810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4816_);
                    v___x_4818_ = v_reuseFailAlloc_4820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4819_, 0, v___x_4815_);
                crate::leanh::lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                return v___x_4819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(
    mut v_numBVars_4822_: *mut crate::leanh::LeanObject,
    mut v_x_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_4822_, v_x_4823_);
    crate::leanh::lean_dec(v_numBVars_4822_);
    return v_res_4824_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
    mut v_as_4825_: *mut crate::leanh::LeanObject,
    mut v_bs_4826_: *mut crate::leanh::LeanObject,
    mut v_i_4827_: *mut crate::leanh::LeanObject,
    mut v_cs_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: u8 = 0;
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: u8 = 0;
    let mut v___x_4836_: u8 = 0;
    let mut v___x_4837_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = lean_array_get_size(v_as_4825_);
                v___x_4830_ = lean_nat_dec_lt(v_i_4827_, v___x_4829_);
                if v___x_4830_ == 0 {
                    crate::leanh::lean_dec(v_i_4827_);
                    return v_cs_4828_;
                } else {
                    v___x_4831_ = lean_array_get_size(v_bs_4826_);
                    v___x_4832_ = lean_nat_dec_lt(v_i_4827_, v___x_4831_);
                    if v___x_4832_ == 0 {
                        crate::leanh::lean_dec(v_i_4827_);
                        return v_cs_4828_;
                    } else {
                        v_a_4833_ = lean_array_fget_borrowed(v_as_4825_, v_i_4827_);
                        v_b_4834_ = lean_array_fget_borrowed(v_bs_4826_, v_i_4827_);
                        v___x_4835_ = (crate::leanh::lean_unbox(v_a_4833_) as u8);
                        v___x_4836_ = (crate::leanh::lean_unbox(v_b_4834_) as u8);
                        v___x_4837_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_4835_, v___x_4836_);
                        v___x_4838_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4839_ = lean_nat_add(v_i_4827_, v___x_4838_);
                        crate::leanh::lean_dec(v_i_4827_);
                        v___x_4840_ = crate::leanh::lean_box((v___x_4837_) as usize);
                        v___x_4841_ = lean_array_push(v_cs_4828_, v___x_4840_);
                        v_i_4827_ = v___x_4839_;
                        v_cs_4828_ = v___x_4841_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(
    mut v_as_4843_: *mut crate::leanh::LeanObject,
    mut v_bs_4844_: *mut crate::leanh::LeanObject,
    mut v_i_4845_: *mut crate::leanh::LeanObject,
    mut v_cs_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
        v_as_4843_, v_bs_4844_, v_i_4845_, v_cs_4846_,
    );
    crate::leanh::lean_dec_ref(v_bs_4844_);
    crate::leanh::lean_dec_ref(v_as_4843_);
    return v_res_4847_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_b_4851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uses_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_uses_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uses_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4850_) == 0 {
                    return v_b_4851_;
                } else {
                    if crate::leanh::lean_obj_tag(v_b_4851_) == 0 {
                        v_uses_4852_ = crate::leanh::lean_ctor_get(v_a_4850_, 0);
                        v_isSharedCheck_4859_ = (!crate::leanh::lean_is_exclusive(v_a_4850_)) as u8;
                        if v_isSharedCheck_4859_ == 0 {
                            v___x_4854_ = v_a_4850_;
                            v_isShared_4855_ = v_isSharedCheck_4859_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_uses_4852_);
                            crate::leanh::lean_dec(v_a_4850_);
                            v___x_4854_ = crate::leanh::lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4859_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_uses_4860_ = crate::leanh::lean_ctor_get(v_a_4850_, 0);
                        crate::leanh::lean_inc_ref(v_uses_4860_);
                        crate::leanh::lean_dec_ref_known(v_a_4850_, 1);
                        v_uses_4861_ = crate::leanh::lean_ctor_get(v_b_4851_, 0);
                        v_isSharedCheck_4871_ = (!crate::leanh::lean_is_exclusive(v_b_4851_)) as u8;
                        if v_isSharedCheck_4871_ == 0 {
                            v___x_4863_ = v_b_4851_;
                            v_isShared_4864_ = v_isSharedCheck_4871_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_uses_4861_);
                            crate::leanh::lean_dec(v_b_4851_);
                            v___x_4863_ = crate::leanh::lean_box(0);
                            v_isShared_4864_ = v_isSharedCheck_4871_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4855_ == 0 {
                    v___x_4857_ = v___x_4854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_uses_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4857_;
            }
            3 => {
                v___x_4865_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4866_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0;
                v___x_4867_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
                    v_uses_4860_,
                    v_uses_4861_,
                    v___x_4865_,
                    v___x_4866_,
                );
                crate::leanh::lean_dec_ref(v_uses_4861_);
                crate::leanh::lean_dec_ref(v_uses_4860_);
                if v_isShared_4864_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4863_, 0, v___x_4867_);
                    v___x_4869_ = v___x_4863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4867_);
                    v___x_4869_ = v_reuseFailAlloc_4870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_add(
    mut v_numBVars_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_b_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_4873_, v_b_4874_);
    return v___x_4875_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(
    mut v_numBVars_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
    mut v_b_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4879_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_4876_, v_a_4877_, v_b_4878_);
    crate::leanh::lean_dec(v_numBVars_4876_);
    return v_res_4879_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instAddBVarUses(
    mut v_numBVars_4880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_BVarUses_add___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4881_, 0, v_numBVars_4880_);
    return v___x_4881_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_over1Of2___redArg(
    mut v_f_4882_: *mut crate::leanh::LeanObject,
    mut v_x_4883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4884_ = crate::leanh::lean_ctor_get(v_x_4883_, 0);
                v_snd_4885_ = crate::leanh::lean_ctor_get(v_x_4883_, 1);
                v_isSharedCheck_4893_ = (!crate::leanh::lean_is_exclusive(v_x_4883_)) as u8;
                if v_isSharedCheck_4893_ == 0 {
                    v___x_4887_ = v_x_4883_;
                    v_isShared_4888_ = v_isSharedCheck_4893_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4885_);
                    crate::leanh::lean_inc(v_fst_4884_);
                    crate::leanh::lean_dec(v_x_4883_);
                    v___x_4887_ = crate::leanh::lean_box(0);
                    v_isShared_4888_ = v_isSharedCheck_4893_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4889_ = crate::leanh::lean_apply_1(v_f_4882_, v_fst_4884_);
                if v_isShared_4888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4889_);
                    v___x_4891_ = v___x_4887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_snd_4885_);
                    v___x_4891_ = v_reuseFailAlloc_4892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_over1Of2(
    mut v_00_u03b1_u2081_4894_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_4895_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4896_: *mut crate::leanh::LeanObject,
    mut v_f_4897_: *mut crate::leanh::LeanObject,
    mut v_x_4898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4899_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_4897_, v_x_4898_);
    return v___x_4899_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData___lam__0(
    mut v_x_4900_: *mut crate::leanh::LeanObject,
    mut v_new_4901_: *mut crate::leanh::LeanObject,
    mut v_x_4902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_new_4901_);
    return v_new_4901_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(
    mut v_x_4903_: *mut crate::leanh::LeanObject,
    mut v_new_4904_: *mut crate::leanh::LeanObject,
    mut v_x_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_4903_, v_new_4904_, v_x_4905_);
    crate::leanh::lean_dec_ref(v_x_4905_);
    crate::leanh::lean_dec_ref(v_new_4904_);
    crate::leanh::lean_dec(v_x_4903_);
    return v_res_4906_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData(
    mut v_d_4908_: *mut crate::leanh::LeanObject,
    mut v_e_4909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_4909_) == 10 {
        let mut v_data_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_data_4910_ = crate::leanh::lean_ctor_get(v_e_4909_, 0);
        crate::leanh::lean_inc(v_data_4910_);
        v_expr_4911_ = crate::leanh::lean_ctor_get(v_e_4909_, 1);
        crate::leanh::lean_inc_ref(v_expr_4911_);
        crate::leanh::lean_dec_ref_known(v_e_4909_, 2);
        v___f_4912_ = l_Lean_Elab_Tactic_Do_addMData___closed__0;
        v___x_4913_ = l_Lean_KVMap_mergeBy(v___f_4912_, v_d_4908_, v_data_4910_);
        crate::leanh::lean_dec(v_data_4910_);
        v___x_4914_ = l_Lean_Expr_mdata___override(v___x_4913_, v_expr_4911_);
        return v___x_4914_;
    } else {
        let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4915_ = l_Lean_Expr_mdata___override(v_d_4908_, v_e_4909_);
        return v___x_4915_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(
    mut v_e_4916_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4918_: u8 = 0;
    let mut v___x_4919_: u8 = 0;
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: u8 = 0;
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: u8 = 0;
    let mut v___x_4924_: u8 = 0;
    let mut v___x_4925_: u8 = 0;
    let mut v_expr_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_4916_) {
                1 => {
                    v___x_4920_ = 0;
                    return v___x_4920_;
                }
                5 => {
                    v___x_4921_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_4916_);
                    if v___x_4921_ == 0 {
                        v___x_4922_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_4916_);
                        v___y_4918_ = v___x_4922_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4918_ = v___x_4921_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v___x_4923_ = 0;
                    return v___x_4923_;
                }
                7 => {
                    v___x_4924_ = 0;
                    return v___x_4924_;
                }
                8 => {
                    v___x_4925_ = 0;
                    return v___x_4925_;
                }
                10 => {
                    v_expr_4926_ = crate::leanh::lean_ctor_get(v_e_4916_, 1);
                    v_e_4916_ = v_expr_4926_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_4928_ = crate::leanh::lean_ctor_get(v_e_4916_, 2);
                    v_e_4916_ = v_struct_4928_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_4930_ = 1;
                    return v___x_4930_;
                }
            },
            1 => {
                if v___y_4918_ == 0 {
                    v___x_4919_ = l_Lean_Meta_Simp_isCharLit(v_e_4916_);
                    return v___x_4919_;
                } else {
                    return v___y_4918_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(
    mut v_e_4931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4932_: u8 = 0;
    let mut v_r_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_4931_);
    crate::leanh::lean_dec_ref(v_e_4931_);
    v_r_4933_ = crate::leanh::lean_box((v_res_4932_) as usize);
    return v_r_4933_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(
    mut v_val_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4935_, 0, v_val_4934_);
    return v___x_4935_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(
    mut v_msgData_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4942_ = lean_st_ref_get(v___y_4940_);
    v_env_4943_ = crate::leanh::lean_ctor_get(v___x_4942_, 0);
    crate::leanh::lean_inc_ref(v_env_4943_);
    crate::leanh::lean_dec(v___x_4942_);
    v___x_4944_ = lean_st_ref_get(v___y_4938_);
    v_mctx_4945_ = crate::leanh::lean_ctor_get(v___x_4944_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4945_);
    crate::leanh::lean_dec(v___x_4944_);
    v_lctx_4946_ = crate::leanh::lean_ctor_get(v___y_4937_, 2);
    v_options_4947_ = crate::leanh::lean_ctor_get(v___y_4939_, 2);
    crate::leanh::lean_inc_ref(v_options_4947_);
    crate::leanh::lean_inc_ref(v_lctx_4946_);
    v___x_4948_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4948_, 0, v_env_4943_);
    crate::leanh::lean_ctor_set(v___x_4948_, 1, v_mctx_4945_);
    crate::leanh::lean_ctor_set(v___x_4948_, 2, v_lctx_4946_);
    crate::leanh::lean_ctor_set(v___x_4948_, 3, v_options_4947_);
    v___x_4949_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4949_, 0, v___x_4948_);
    crate::leanh::lean_ctor_set(v___x_4949_, 1, v_msgData_4936_);
    v___x_4950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(
    mut v_msgData_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    crate::leanh::lean_dec(v___y_4955_);
    crate::leanh::lean_dec_ref(v___y_4954_);
    crate::leanh::lean_dec(v___y_4953_);
    crate::leanh::lean_dec_ref(v___y_4952_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
    mut v_msg_4958_: *mut crate::leanh::LeanObject,
    mut v___y_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4969_: u8 = 0;
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4964_ = crate::leanh::lean_ctor_get(v___y_4961_, 5);
                v___x_4965_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
                v_a_4966_ = crate::leanh::lean_ctor_get(v___x_4965_, 0);
                v_isSharedCheck_4974_ = (!crate::leanh::lean_is_exclusive(v___x_4965_)) as u8;
                if v_isSharedCheck_4974_ == 0 {
                    v___x_4968_ = v___x_4965_;
                    v_isShared_4969_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4966_);
                    crate::leanh::lean_dec(v___x_4965_);
                    v___x_4968_ = crate::leanh::lean_box(0);
                    v_isShared_4969_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4964_);
                v___x_4970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4970_, 0, v_ref_4964_);
                crate::leanh::lean_ctor_set(v___x_4970_, 1, v_a_4966_);
                if v_isShared_4969_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4968_, 1);
                    crate::leanh::lean_ctor_set(v___x_4968_, 0, v___x_4970_);
                    v___x_4972_ = v___x_4968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4970_);
                    v___x_4972_ = v_reuseFailAlloc_4973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(
    mut v_msg_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
    mut v___y_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4981_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
        v_msg_4975_,
        v___y_4976_,
        v___y_4977_,
        v___y_4978_,
        v___y_4979_,
    );
    crate::leanh::lean_dec(v___y_4979_);
    crate::leanh::lean_dec_ref(v___y_4978_);
    crate::leanh::lean_dec(v___y_4977_);
    crate::leanh::lean_dec_ref(v___y_4976_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___lam__0(
    mut v_data_4982_: *mut crate::leanh::LeanObject,
    mut v_expr_4983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4984_ = l_Lean_Expr_mdata___override(v_data_4982_, v_expr_4983_);
    return v___x_4984_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___lam__1(
    mut v_typeName_4985_: *mut crate::leanh::LeanObject,
    mut v_idx_4986_: *mut crate::leanh::LeanObject,
    mut v_struct_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4988_ = l_Lean_Expr_proj___override(v_typeName_4985_, v_idx_4986_, v_struct_4987_);
    return v___x_4988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_b_4990_: *mut crate::leanh::LeanObject,
    mut v_x_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4997_: u8 = 0;
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4991_) == 0 {
                    crate::leanh::lean_dec(v_b_4990_);
                    crate::leanh::lean_dec(v_a_4989_);
                    return v_x_4991_;
                } else {
                    v_key_4992_ = crate::leanh::lean_ctor_get(v_x_4991_, 0);
                    v_value_4993_ = crate::leanh::lean_ctor_get(v_x_4991_, 1);
                    v_tail_4994_ = crate::leanh::lean_ctor_get(v_x_4991_, 2);
                    v_isSharedCheck_5006_ = (!crate::leanh::lean_is_exclusive(v_x_4991_)) as u8;
                    if v_isSharedCheck_5006_ == 0 {
                        v___x_4996_ = v_x_4991_;
                        v_isShared_4997_ = v_isSharedCheck_5006_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4994_);
                        crate::leanh::lean_inc(v_value_4993_);
                        crate::leanh::lean_inc(v_key_4992_);
                        crate::leanh::lean_dec(v_x_4991_);
                        v___x_4996_ = crate::leanh::lean_box(0);
                        v_isShared_4997_ = v_isSharedCheck_5006_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4998_ = l_Lean_instBEqFVarId_beq(v_key_4992_, v_a_4989_);
                if v___x_4998_ == 0 {
                    v___x_4999_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_4989_, v_b_4990_, v_tail_4994_);
                    if v_isShared_4997_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4996_, 2, v___x_4999_);
                        v___x_5001_ = v___x_4996_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5002_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_key_4992_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5002_, 1, v_value_4993_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5002_, 2, v___x_4999_);
                        v___x_5001_ = v_reuseFailAlloc_5002_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4993_);
                    crate::leanh::lean_dec(v_key_4992_);
                    if v_isShared_4997_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4996_, 1, v_b_4990_);
                        crate::leanh::lean_ctor_set(v___x_4996_, 0, v_a_4989_);
                        v___x_5004_ = v___x_4996_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4989_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v_b_4990_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 2, v_tail_4994_);
                        v___x_5004_ = v_reuseFailAlloc_5005_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5001_;
            }
            3 => {
                return v___x_5004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(
    mut v_m_5007_: *mut crate::leanh::LeanObject,
    mut v_a_5008_: *mut crate::leanh::LeanObject,
    mut v_b_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u64 = 0;
    let mut v___x_5017_: u64 = 0;
    let mut v___x_5018_: u64 = 0;
    let mut v_fold_5019_: u64 = 0;
    let mut v___x_5020_: u64 = 0;
    let mut v___x_5021_: u64 = 0;
    let mut v___x_5022_: u64 = 0;
    let mut v___x_5023_: usize = 0;
    let mut v___x_5024_: usize = 0;
    let mut v___x_5025_: usize = 0;
    let mut v___x_5026_: usize = 0;
    let mut v___x_5027_: usize = 0;
    let mut v_bkt_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut v_val_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5010_ = crate::leanh::lean_ctor_get(v_m_5007_, 0);
                v_buckets_5011_ = crate::leanh::lean_ctor_get(v_m_5007_, 1);
                v_isSharedCheck_5054_ = (!crate::leanh::lean_is_exclusive(v_m_5007_)) as u8;
                if v_isSharedCheck_5054_ == 0 {
                    v___x_5013_ = v_m_5007_;
                    v_isShared_5014_ = v_isSharedCheck_5054_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5011_);
                    crate::leanh::lean_inc(v_size_5010_);
                    crate::leanh::lean_dec(v_m_5007_);
                    v___x_5013_ = crate::leanh::lean_box(0);
                    v_isShared_5014_ = v_isSharedCheck_5054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5015_ = lean_array_get_size(v_buckets_5011_);
                v___x_5016_ = l_Lean_instHashableFVarId_hash(v_a_5008_);
                v___x_5017_ = 32u64;
                v___x_5018_ = lean_uint64_shift_right(v___x_5016_, v___x_5017_);
                v_fold_5019_ = lean_uint64_xor(v___x_5016_, v___x_5018_);
                v___x_5020_ = 16u64;
                v___x_5021_ = lean_uint64_shift_right(v_fold_5019_, v___x_5020_);
                v___x_5022_ = lean_uint64_xor(v_fold_5019_, v___x_5021_);
                v___x_5023_ = lean_uint64_to_usize(v___x_5022_);
                v___x_5024_ = lean_usize_of_nat(v___x_5015_);
                v___x_5025_ = 1usize;
                v___x_5026_ = lean_usize_sub(v___x_5024_, v___x_5025_);
                v___x_5027_ = lean_usize_land(v___x_5023_, v___x_5026_);
                v_bkt_5028_ = lean_array_uget_borrowed(v_buckets_5011_, v___x_5027_);
                v___x_5029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_5008_, v_bkt_5028_);
                if v___x_5029_ == 0 {
                    v___x_5030_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5031_ = lean_nat_add(v_size_5010_, v___x_5030_);
                    crate::leanh::lean_dec(v_size_5010_);
                    crate::leanh::lean_inc(v_bkt_5028_);
                    v___x_5032_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5032_, 0, v_a_5008_);
                    crate::leanh::lean_ctor_set(v___x_5032_, 1, v_b_5009_);
                    crate::leanh::lean_ctor_set(v___x_5032_, 2, v_bkt_5028_);
                    v_buckets_x27_5033_ =
                        lean_array_uset(v_buckets_5011_, v___x_5027_, v___x_5032_);
                    v___x_5034_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5035_ = lean_nat_mul(v_size_x27_5031_, v___x_5034_);
                    v___x_5036_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5037_ = lean_nat_div(v___x_5035_, v___x_5036_);
                    crate::leanh::lean_dec(v___x_5035_);
                    v___x_5038_ = lean_array_get_size(v_buckets_x27_5033_);
                    v___x_5039_ = lean_nat_dec_le(v___x_5037_, v___x_5038_);
                    crate::leanh::lean_dec(v___x_5037_);
                    if v___x_5039_ == 0 {
                        v_val_5040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_5033_);
                        if v_isShared_5014_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5013_, 1, v_val_5040_);
                            crate::leanh::lean_ctor_set(v___x_5013_, 0, v_size_x27_5031_);
                            v___x_5042_ = v___x_5013_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5043_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5043_,
                                0,
                                v_size_x27_5031_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_val_5040_);
                            v___x_5042_ = v_reuseFailAlloc_5043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5014_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5013_, 1, v_buckets_x27_5033_);
                            crate::leanh::lean_ctor_set(v___x_5013_, 0, v_size_x27_5031_);
                            v___x_5045_ = v___x_5013_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5046_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5046_,
                                0,
                                v_size_x27_5031_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5046_,
                                1,
                                v_buckets_x27_5033_,
                            );
                            v___x_5045_ = v_reuseFailAlloc_5046_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5028_);
                    v___x_5047_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5048_ =
                        lean_array_uset(v_buckets_5011_, v___x_5027_, v___x_5047_);
                    v___x_5049_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_5008_, v_b_5009_, v_bkt_5028_);
                    v___x_5050_ = lean_array_uset(v_buckets_x27_5048_, v___x_5027_, v___x_5049_);
                    if v_isShared_5014_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5013_, 1, v___x_5050_);
                        v___x_5052_ = v___x_5013_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_size_5010_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5050_);
                        v___x_5052_ = v_reuseFailAlloc_5053_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5042_;
            }
            3 => {
                return v___x_5045_;
            }
            4 => {
                return v___x_5052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(
    mut v___y_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v_r_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v_unused_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5057_ = lean_st_ref_get(v___y_5055_);
                v_ngen_5058_ = crate::leanh::lean_ctor_get(v___x_5057_, 2);
                crate::leanh::lean_inc_ref(v_ngen_5058_);
                crate::leanh::lean_dec(v___x_5057_);
                v_namePrefix_5059_ = crate::leanh::lean_ctor_get(v_ngen_5058_, 0);
                v_idx_5060_ = crate::leanh::lean_ctor_get(v_ngen_5058_, 1);
                v_isSharedCheck_5089_ = (!crate::leanh::lean_is_exclusive(v_ngen_5058_)) as u8;
                if v_isSharedCheck_5089_ == 0 {
                    v___x_5062_ = v_ngen_5058_;
                    v_isShared_5063_ = v_isSharedCheck_5089_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_5060_);
                    crate::leanh::lean_inc(v_namePrefix_5059_);
                    crate::leanh::lean_dec(v_ngen_5058_);
                    v___x_5062_ = crate::leanh::lean_box(0);
                    v_isShared_5063_ = v_isSharedCheck_5089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5064_ = lean_st_ref_take(v___y_5055_);
                v_env_5065_ = crate::leanh::lean_ctor_get(v___x_5064_, 0);
                v_nextMacroScope_5066_ = crate::leanh::lean_ctor_get(v___x_5064_, 1);
                v_auxDeclNGen_5067_ = crate::leanh::lean_ctor_get(v___x_5064_, 3);
                v_traceState_5068_ = crate::leanh::lean_ctor_get(v___x_5064_, 4);
                v_cache_5069_ = crate::leanh::lean_ctor_get(v___x_5064_, 5);
                v_messages_5070_ = crate::leanh::lean_ctor_get(v___x_5064_, 6);
                v_infoState_5071_ = crate::leanh::lean_ctor_get(v___x_5064_, 7);
                v_snapshotTasks_5072_ = crate::leanh::lean_ctor_get(v___x_5064_, 8);
                v_isSharedCheck_5087_ = (!crate::leanh::lean_is_exclusive(v___x_5064_)) as u8;
                if v_isSharedCheck_5087_ == 0 {
                    v_unused_5088_ = crate::leanh::lean_ctor_get(v___x_5064_, 2);
                    crate::leanh::lean_dec(v_unused_5088_);
                    v___x_5074_ = v___x_5064_;
                    v_isShared_5075_ = v_isSharedCheck_5087_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5072_);
                    crate::leanh::lean_inc(v_infoState_5071_);
                    crate::leanh::lean_inc(v_messages_5070_);
                    crate::leanh::lean_inc(v_cache_5069_);
                    crate::leanh::lean_inc(v_traceState_5068_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5067_);
                    crate::leanh::lean_inc(v_nextMacroScope_5066_);
                    crate::leanh::lean_inc(v_env_5065_);
                    crate::leanh::lean_dec(v___x_5064_);
                    v___x_5074_ = crate::leanh::lean_box(0);
                    v_isShared_5075_ = v_isSharedCheck_5087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_5060_);
                crate::leanh::lean_inc(v_namePrefix_5059_);
                v_r_5076_ = l_Lean_Name_num___override(v_namePrefix_5059_, v_idx_5060_);
                v___x_5077_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5078_ = lean_nat_add(v_idx_5060_, v___x_5077_);
                crate::leanh::lean_dec(v_idx_5060_);
                if v_isShared_5063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5062_, 1, v___x_5078_);
                    v___x_5080_ = v___x_5062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_namePrefix_5059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5078_);
                    v___x_5080_ = v_reuseFailAlloc_5086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5075_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5074_, 2, v___x_5080_);
                    v___x_5082_ = v___x_5074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_env_5065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_nextMacroScope_5066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 2, v___x_5080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 3, v_auxDeclNGen_5067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 4, v_traceState_5068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 5, v_cache_5069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 6, v_messages_5070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 7, v_infoState_5071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 8, v_snapshotTasks_5072_);
                    v___x_5082_ = v_reuseFailAlloc_5085_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5083_ = lean_st_ref_set(v___y_5055_, v___x_5082_);
                v___x_5084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5084_, 0, v_r_5076_);
                return v___x_5084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5092_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5090_);
    crate::leanh::lean_dec(v___y_5090_);
    return v_res_5092_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
    mut v___y_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5098_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5096_);
                v_a_5099_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                v_isSharedCheck_5106_ = (!crate::leanh::lean_is_exclusive(v___x_5098_)) as u8;
                if v_isSharedCheck_5106_ == 0 {
                    v___x_5101_ = v___x_5098_;
                    v_isShared_5102_ = v_isSharedCheck_5106_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5099_);
                    crate::leanh::lean_dec(v___x_5098_);
                    v___x_5101_ = crate::leanh::lean_box(0);
                    v_isShared_5102_ = v_isSharedCheck_5106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5102_ == 0 {
                    v___x_5104_ = v___x_5101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
                    v___x_5104_ = v_reuseFailAlloc_5105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5112_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
        v___y_5107_,
        v___y_5108_,
        v___y_5109_,
        v___y_5110_,
    );
    crate::leanh::lean_dec(v___y_5110_);
    crate::leanh::lean_dec_ref(v___y_5109_);
    crate::leanh::lean_dec(v___y_5108_);
    crate::leanh::lean_dec_ref(v___y_5107_);
    return v_res_5112_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(
    mut v_a_5113_: *mut crate::leanh::LeanObject,
    mut v_x_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5121_: u8 = 0;
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5114_) == 0 {
                    return v_x_5114_;
                } else {
                    v_key_5115_ = crate::leanh::lean_ctor_get(v_x_5114_, 0);
                    v_value_5116_ = crate::leanh::lean_ctor_get(v_x_5114_, 1);
                    v_tail_5117_ = crate::leanh::lean_ctor_get(v_x_5114_, 2);
                    v_isSharedCheck_5126_ = (!crate::leanh::lean_is_exclusive(v_x_5114_)) as u8;
                    if v_isSharedCheck_5126_ == 0 {
                        v___x_5119_ = v_x_5114_;
                        v_isShared_5120_ = v_isSharedCheck_5126_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5117_);
                        crate::leanh::lean_inc(v_value_5116_);
                        crate::leanh::lean_inc(v_key_5115_);
                        crate::leanh::lean_dec(v_x_5114_);
                        v___x_5119_ = crate::leanh::lean_box(0);
                        v_isShared_5120_ = v_isSharedCheck_5126_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5121_ = l_Lean_instBEqFVarId_beq(v_key_5115_, v_a_5113_);
                if v___x_5121_ == 0 {
                    v___x_5122_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5113_, v_tail_5117_);
                    if v_isShared_5120_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5119_, 2, v___x_5122_);
                        v___x_5124_ = v___x_5119_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5125_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_key_5115_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_value_5116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 2, v___x_5122_);
                        v___x_5124_ = v_reuseFailAlloc_5125_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5119_);
                    crate::leanh::lean_dec(v_value_5116_);
                    crate::leanh::lean_dec(v_key_5115_);
                    return v_tail_5117_;
                }
            }
            2 => {
                return v___x_5124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(
    mut v_a_5127_: *mut crate::leanh::LeanObject,
    mut v_x_5128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5127_, v_x_5128_);
    crate::leanh::lean_dec(v_a_5127_);
    return v_res_5129_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(
    mut v_m_5130_: *mut crate::leanh::LeanObject,
    mut v_a_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: u64 = 0;
    let mut v___x_5136_: u64 = 0;
    let mut v___x_5137_: u64 = 0;
    let mut v_fold_5138_: u64 = 0;
    let mut v___x_5139_: u64 = 0;
    let mut v___x_5140_: u64 = 0;
    let mut v___x_5141_: u64 = 0;
    let mut v___x_5142_: usize = 0;
    let mut v___x_5143_: usize = 0;
    let mut v___x_5144_: usize = 0;
    let mut v___x_5145_: usize = 0;
    let mut v___x_5146_: usize = 0;
    let mut v_bkt_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut v_unused_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5132_ = crate::leanh::lean_ctor_get(v_m_5130_, 0);
                v_buckets_5133_ = crate::leanh::lean_ctor_get(v_m_5130_, 1);
                v___x_5134_ = lean_array_get_size(v_buckets_5133_);
                v___x_5135_ = l_Lean_instHashableFVarId_hash(v_a_5131_);
                v___x_5136_ = 32u64;
                v___x_5137_ = lean_uint64_shift_right(v___x_5135_, v___x_5136_);
                v_fold_5138_ = lean_uint64_xor(v___x_5135_, v___x_5137_);
                v___x_5139_ = 16u64;
                v___x_5140_ = lean_uint64_shift_right(v_fold_5138_, v___x_5139_);
                v___x_5141_ = lean_uint64_xor(v_fold_5138_, v___x_5140_);
                v___x_5142_ = lean_uint64_to_usize(v___x_5141_);
                v___x_5143_ = lean_usize_of_nat(v___x_5134_);
                v___x_5144_ = 1usize;
                v___x_5145_ = lean_usize_sub(v___x_5143_, v___x_5144_);
                v___x_5146_ = lean_usize_land(v___x_5142_, v___x_5145_);
                v_bkt_5147_ = lean_array_uget_borrowed(v_buckets_5133_, v___x_5146_);
                v___x_5148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_5131_, v_bkt_5147_);
                if v___x_5148_ == 0 {
                    return v_m_5130_;
                } else {
                    crate::leanh::lean_inc(v_bkt_5147_);
                    crate::leanh::lean_inc_ref(v_buckets_5133_);
                    crate::leanh::lean_inc(v_size_5132_);
                    v_isSharedCheck_5161_ = (!crate::leanh::lean_is_exclusive(v_m_5130_)) as u8;
                    if v_isSharedCheck_5161_ == 0 {
                        v_unused_5162_ = crate::leanh::lean_ctor_get(v_m_5130_, 1);
                        crate::leanh::lean_dec(v_unused_5162_);
                        v_unused_5163_ = crate::leanh::lean_ctor_get(v_m_5130_, 0);
                        crate::leanh::lean_dec(v_unused_5163_);
                        v___x_5150_ = v_m_5130_;
                        v_isShared_5151_ = v_isSharedCheck_5161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5130_);
                        v___x_5150_ = crate::leanh::lean_box(0);
                        v_isShared_5151_ = v_isSharedCheck_5161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5152_ = crate::leanh::lean_box(0);
                v_buckets_x27_5153_ = lean_array_uset(v_buckets_5133_, v___x_5146_, v___x_5152_);
                v___x_5154_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5155_ = lean_nat_sub(v_size_5132_, v___x_5154_);
                crate::leanh::lean_dec(v_size_5132_);
                v___x_5156_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5131_, v_bkt_5147_);
                v___x_5157_ = lean_array_uset(v_buckets_x27_5153_, v___x_5146_, v___x_5156_);
                if v_isShared_5151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5150_, 1, v___x_5157_);
                    crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5155_);
                    v___x_5159_ = v___x_5150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5160_, 1, v___x_5157_);
                    v___x_5159_ = v_reuseFailAlloc_5160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(
    mut v_m_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5166_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_5164_, v_a_5165_);
    crate::leanh::lean_dec(v_a_5165_);
    return v_res_5166_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(
    mut v_a_5167_: *mut crate::leanh::LeanObject,
    mut v_fallback_5168_: *mut crate::leanh::LeanObject,
    mut v_x_5169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5169_) == 0 {
                    crate::leanh::lean_inc(v_fallback_5168_);
                    return v_fallback_5168_;
                } else {
                    v_key_5170_ = crate::leanh::lean_ctor_get(v_x_5169_, 0);
                    v_value_5171_ = crate::leanh::lean_ctor_get(v_x_5169_, 1);
                    v_tail_5172_ = crate::leanh::lean_ctor_get(v_x_5169_, 2);
                    v___x_5173_ = l_Lean_instBEqFVarId_beq(v_key_5170_, v_a_5167_);
                    if v___x_5173_ == 0 {
                        v_x_5169_ = v_tail_5172_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5171_);
                        return v_value_5171_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(
    mut v_a_5175_: *mut crate::leanh::LeanObject,
    mut v_fallback_5176_: *mut crate::leanh::LeanObject,
    mut v_x_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5178_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_5175_, v_fallback_5176_, v_x_5177_);
    crate::leanh::lean_dec(v_x_5177_);
    crate::leanh::lean_dec(v_fallback_5176_);
    crate::leanh::lean_dec(v_a_5175_);
    return v_res_5178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(
    mut v_m_5179_: *mut crate::leanh::LeanObject,
    mut v_a_5180_: *mut crate::leanh::LeanObject,
    mut v_fallback_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: u64 = 0;
    let mut v___x_5185_: u64 = 0;
    let mut v___x_5186_: u64 = 0;
    let mut v_fold_5187_: u64 = 0;
    let mut v___x_5188_: u64 = 0;
    let mut v___x_5189_: u64 = 0;
    let mut v___x_5190_: u64 = 0;
    let mut v___x_5191_: usize = 0;
    let mut v___x_5192_: usize = 0;
    let mut v___x_5193_: usize = 0;
    let mut v___x_5194_: usize = 0;
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5182_ = crate::leanh::lean_ctor_get(v_m_5179_, 1);
    v___x_5183_ = lean_array_get_size(v_buckets_5182_);
    v___x_5184_ = l_Lean_instHashableFVarId_hash(v_a_5180_);
    v___x_5185_ = 32u64;
    v___x_5186_ = lean_uint64_shift_right(v___x_5184_, v___x_5185_);
    v_fold_5187_ = lean_uint64_xor(v___x_5184_, v___x_5186_);
    v___x_5188_ = 16u64;
    v___x_5189_ = lean_uint64_shift_right(v_fold_5187_, v___x_5188_);
    v___x_5190_ = lean_uint64_xor(v_fold_5187_, v___x_5189_);
    v___x_5191_ = lean_uint64_to_usize(v___x_5190_);
    v___x_5192_ = lean_usize_of_nat(v___x_5183_);
    v___x_5193_ = 1usize;
    v___x_5194_ = lean_usize_sub(v___x_5192_, v___x_5193_);
    v___x_5195_ = lean_usize_land(v___x_5191_, v___x_5194_);
    v___x_5196_ = lean_array_uget_borrowed(v_buckets_5182_, v___x_5195_);
    v___x_5197_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_5180_, v_fallback_5181_, v___x_5196_);
    return v___x_5197_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(
    mut v_m_5198_: *mut crate::leanh::LeanObject,
    mut v_a_5199_: *mut crate::leanh::LeanObject,
    mut v_fallback_5200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_5198_, v_a_5199_, v_fallback_5200_);
    crate::leanh::lean_dec(v_fallback_5200_);
    crate::leanh::lean_dec(v_a_5199_);
    crate::leanh::lean_dec_ref(v_m_5198_);
    return v_res_5201_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5205_ = crate::leanh::lean_box(0);
    v___x_5206_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5207_ = lean_mk_array(v___x_5206_, v___x_5205_);
    return v___x_5207_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5208_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once),
        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2,
    );
    v___x_5209_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5210_, 0, v___x_5209_);
    crate::leanh::lean_ctor_set(v___x_5210_, 1, v___x_5208_);
    return v___x_5210_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5213_ = l_Lean_Elab_Tactic_Do_countUses___closed__0;
    v___x_5214_ = l_Lean_stringToMessageData(v___x_5213_);
    return v___x_5214_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5216_ = l_Lean_Elab_Tactic_Do_countUses___closed__2;
    v___x_5217_ = l_Lean_stringToMessageData(v___x_5216_);
    return v___x_5217_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5219_ = l_Lean_Elab_Tactic_Do_countUses___closed__4;
    v___x_5220_ = l_Lean_stringToMessageData(v___x_5219_);
    return v___x_5220_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses(
    mut v_e_5221_: *mut crate::leanh::LeanObject,
    mut v_subst_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_deBruijnIndex_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: u8 = 0;
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v_fst_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5275_: u8 = 0;
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v_binderName_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5289_: u8 = 0;
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v_fst_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_a_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_binderName_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5329_: u8 = 0;
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5341_: u8 = 0;
    let mut v_fst_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut v_declName_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5370_: u8 = 0;
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5378_: u8 = 0;
    let mut v_fst_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v_snd_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v_val_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_unused_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_a_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v_reuseFailAlloc_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut v_a_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5425_: u8 = 0;
    let mut v_data_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___f_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_typeName_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v___f_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5452_: u8 = 0;
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_5221_) {
                0 => {
                    v_deBruijnIndex_5228_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    v___x_5229_ = lean_array_get_size(v_subst_5222_);
                    v___x_5230_ = lean_nat_dec_lt(v_deBruijnIndex_5228_, v___x_5229_);
                    if v___x_5230_ == 0 {
                        crate::leanh::lean_inc(v_deBruijnIndex_5228_);
                        crate::leanh::lean_dec_ref_known(v_e_5221_, 1);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        v___x_5231_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUses___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUses___closed__1,
                        );
                        v___x_5232_ = l_Nat_reprFast(v_deBruijnIndex_5228_);
                        v___x_5233_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5232_);
                        v___x_5234_ = l_Lean_MessageData_ofFormat(v___x_5233_);
                        v___x_5235_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5235_, 0, v___x_5231_);
                        crate::leanh::lean_ctor_set(v___x_5235_, 1, v___x_5234_);
                        v___x_5236_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUses___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUses___closed__3,
                        );
                        v___x_5237_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5235_);
                        crate::leanh::lean_ctor_set(v___x_5237_, 1, v___x_5236_);
                        v___x_5238_ = l_Nat_reprFast(v___x_5229_);
                        v___x_5239_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5239_, 0, v___x_5238_);
                        v___x_5240_ = l_Lean_MessageData_ofFormat(v___x_5239_);
                        v___x_5241_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5241_, 0, v___x_5237_);
                        crate::leanh::lean_ctor_set(v___x_5241_, 1, v___x_5240_);
                        v___x_5242_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_5241_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
                        return v___x_5242_;
                    } else {
                        v___x_5243_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5244_ = lean_nat_sub(v___x_5229_, v___x_5243_);
                        v___x_5245_ = lean_nat_sub(v___x_5244_, v_deBruijnIndex_5228_);
                        crate::leanh::lean_dec(v___x_5244_);
                        v___x_5246_ = lean_array_fget(v_subst_5222_, v___x_5245_);
                        crate::leanh::lean_dec(v___x_5245_);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        v___x_5247_ = 1;
                        v___x_5248_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                        );
                        v___x_5249_ = crate::leanh::lean_box((v___x_5247_) as usize);
                        v___x_5250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_5248_, v___x_5246_, v___x_5249_);
                        v___x_5251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5251_, 0, v_e_5221_);
                        crate::leanh::lean_ctor_set(v___x_5251_, 1, v___x_5250_);
                        v___x_5252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5252_, 0, v___x_5251_);
                        return v___x_5252_;
                    }
                }
                1 => {
                    crate::leanh::lean_dec_ref(v_subst_5222_);
                    v_fvarId_5253_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    v___x_5254_ = 1;
                    v___x_5255_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                    );
                    v___x_5256_ = crate::leanh::lean_box((v___x_5254_) as usize);
                    crate::leanh::lean_inc(v_fvarId_5253_);
                    v___x_5257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_5255_, v_fvarId_5253_, v___x_5256_);
                    v___x_5258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5258_, 0, v_e_5221_);
                    crate::leanh::lean_ctor_set(v___x_5258_, 1, v___x_5257_);
                    v___x_5259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5259_, 0, v___x_5258_);
                    return v___x_5259_;
                }
                5 => {
                    v_fn_5260_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5260_);
                    v_arg_5261_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5261_);
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 2);
                    crate::leanh::lean_inc_ref(v_subst_5222_);
                    v___x_5262_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_fn_5260_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5262_) == 0 {
                        v_a_5263_ = crate::leanh::lean_ctor_get(v___x_5262_, 0);
                        crate::leanh::lean_inc(v_a_5263_);
                        crate::leanh::lean_dec_ref_known(v___x_5262_, 1);
                        v_fst_5264_ = crate::leanh::lean_ctor_get(v_a_5263_, 0);
                        crate::leanh::lean_inc(v_fst_5264_);
                        v_snd_5265_ = crate::leanh::lean_ctor_get(v_a_5263_, 1);
                        crate::leanh::lean_inc(v_snd_5265_);
                        crate::leanh::lean_dec(v_a_5263_);
                        v___x_5266_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_arg_5261_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5266_) == 0 {
                            v_a_5267_ = crate::leanh::lean_ctor_get(v___x_5266_, 0);
                            v_isSharedCheck_5285_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5266_)) as u8;
                            if v_isSharedCheck_5285_ == 0 {
                                v___x_5269_ = v___x_5266_;
                                v_isShared_5270_ = v_isSharedCheck_5285_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5267_);
                                crate::leanh::lean_dec(v___x_5266_);
                                v___x_5269_ = crate::leanh::lean_box(0);
                                v_isShared_5270_ = v_isSharedCheck_5285_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_5265_);
                            crate::leanh::lean_dec(v_fst_5264_);
                            return v___x_5266_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_5261_);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        return v___x_5262_;
                    }
                }
                6 => {
                    v_binderName_5286_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc(v_binderName_5286_);
                    v_binderType_5287_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5287_);
                    v_body_5288_ = crate::leanh::lean_ctor_get(v_e_5221_, 2);
                    crate::leanh::lean_inc_ref(v_body_5288_);
                    v_binderInfo_5289_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5290_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5290_) == 0 {
                        v_a_5291_ = crate::leanh::lean_ctor_get(v___x_5290_, 0);
                        crate::leanh::lean_inc(v_a_5291_);
                        crate::leanh::lean_dec_ref_known(v___x_5290_, 1);
                        crate::leanh::lean_inc_ref(v_subst_5222_);
                        v___x_5292_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_binderType_5287_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5292_) == 0 {
                            v_a_5293_ = crate::leanh::lean_ctor_get(v___x_5292_, 0);
                            crate::leanh::lean_inc(v_a_5293_);
                            crate::leanh::lean_dec_ref_known(v___x_5292_, 1);
                            v_fst_5294_ = crate::leanh::lean_ctor_get(v_a_5293_, 0);
                            crate::leanh::lean_inc(v_fst_5294_);
                            v_snd_5295_ = crate::leanh::lean_ctor_get(v_a_5293_, 1);
                            crate::leanh::lean_inc(v_snd_5295_);
                            crate::leanh::lean_dec(v_a_5293_);
                            crate::leanh::lean_inc(v_a_5291_);
                            v___x_5296_ = lean_array_push(v_subst_5222_, v_a_5291_);
                            v___x_5297_ = l_Lean_Elab_Tactic_Do_countUses(
                                v_body_5288_,
                                v___x_5296_,
                                v_a_5223_,
                                v_a_5224_,
                                v_a_5225_,
                                v_a_5226_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5297_) == 0 {
                                v_a_5298_ = crate::leanh::lean_ctor_get(v___x_5297_, 0);
                                v_isSharedCheck_5317_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5297_)) as u8;
                                if v_isSharedCheck_5317_ == 0 {
                                    v___x_5300_ = v___x_5297_;
                                    v_isShared_5301_ = v_isSharedCheck_5317_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5298_);
                                    crate::leanh::lean_dec(v___x_5297_);
                                    v___x_5300_ = crate::leanh::lean_box(0);
                                    v_isShared_5301_ = v_isSharedCheck_5317_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_5295_);
                                crate::leanh::lean_dec(v_fst_5294_);
                                crate::leanh::lean_dec(v_a_5291_);
                                crate::leanh::lean_dec(v_binderName_5286_);
                                return v___x_5297_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5291_);
                            crate::leanh::lean_dec_ref(v_body_5288_);
                            crate::leanh::lean_dec(v_binderName_5286_);
                            crate::leanh::lean_dec_ref(v_subst_5222_);
                            return v___x_5292_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5288_);
                        crate::leanh::lean_dec_ref(v_binderType_5287_);
                        crate::leanh::lean_dec(v_binderName_5286_);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        v_a_5318_ = crate::leanh::lean_ctor_get(v___x_5290_, 0);
                        v_isSharedCheck_5325_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5290_)) as u8;
                        if v_isSharedCheck_5325_ == 0 {
                            v___x_5320_ = v___x_5290_;
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5318_);
                            crate::leanh::lean_dec(v___x_5290_);
                            v___x_5320_ = crate::leanh::lean_box(0);
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 9;
                            continue;
                        }
                    }
                }
                7 => {
                    v_binderName_5326_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc(v_binderName_5326_);
                    v_binderType_5327_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5327_);
                    v_body_5328_ = crate::leanh::lean_ctor_get(v_e_5221_, 2);
                    crate::leanh::lean_inc_ref(v_body_5328_);
                    v_binderInfo_5329_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5330_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5330_) == 0 {
                        v_a_5331_ = crate::leanh::lean_ctor_get(v___x_5330_, 0);
                        crate::leanh::lean_inc(v_a_5331_);
                        crate::leanh::lean_dec_ref_known(v___x_5330_, 1);
                        crate::leanh::lean_inc_ref(v_subst_5222_);
                        v___x_5332_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_binderType_5327_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5332_) == 0 {
                            v_a_5333_ = crate::leanh::lean_ctor_get(v___x_5332_, 0);
                            crate::leanh::lean_inc(v_a_5333_);
                            crate::leanh::lean_dec_ref_known(v___x_5332_, 1);
                            v_fst_5334_ = crate::leanh::lean_ctor_get(v_a_5333_, 0);
                            crate::leanh::lean_inc(v_fst_5334_);
                            v_snd_5335_ = crate::leanh::lean_ctor_get(v_a_5333_, 1);
                            crate::leanh::lean_inc(v_snd_5335_);
                            crate::leanh::lean_dec(v_a_5333_);
                            crate::leanh::lean_inc(v_a_5331_);
                            v___x_5336_ = lean_array_push(v_subst_5222_, v_a_5331_);
                            v___x_5337_ = l_Lean_Elab_Tactic_Do_countUses(
                                v_body_5328_,
                                v___x_5336_,
                                v_a_5223_,
                                v_a_5224_,
                                v_a_5225_,
                                v_a_5226_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5337_) == 0 {
                                v_a_5338_ = crate::leanh::lean_ctor_get(v___x_5337_, 0);
                                v_isSharedCheck_5357_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5337_)) as u8;
                                if v_isSharedCheck_5357_ == 0 {
                                    v___x_5340_ = v___x_5337_;
                                    v_isShared_5341_ = v_isSharedCheck_5357_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5338_);
                                    crate::leanh::lean_dec(v___x_5337_);
                                    v___x_5340_ = crate::leanh::lean_box(0);
                                    v_isShared_5341_ = v_isSharedCheck_5357_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_5335_);
                                crate::leanh::lean_dec(v_fst_5334_);
                                crate::leanh::lean_dec(v_a_5331_);
                                crate::leanh::lean_dec(v_binderName_5326_);
                                return v___x_5337_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5331_);
                            crate::leanh::lean_dec_ref(v_body_5328_);
                            crate::leanh::lean_dec(v_binderName_5326_);
                            crate::leanh::lean_dec_ref(v_subst_5222_);
                            return v___x_5332_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5328_);
                        crate::leanh::lean_dec_ref(v_binderType_5327_);
                        crate::leanh::lean_dec(v_binderName_5326_);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        v_a_5358_ = crate::leanh::lean_ctor_get(v___x_5330_, 0);
                        v_isSharedCheck_5365_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5330_)) as u8;
                        if v_isSharedCheck_5365_ == 0 {
                            v___x_5360_ = v___x_5330_;
                            v_isShared_5361_ = v_isSharedCheck_5365_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5358_);
                            crate::leanh::lean_dec(v___x_5330_);
                            v___x_5360_ = crate::leanh::lean_box(0);
                            v_isShared_5361_ = v_isSharedCheck_5365_;
                            state = 15;
                            continue;
                        }
                    }
                }
                8 => {
                    v_declName_5366_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc(v_declName_5366_);
                    v_type_5367_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc_ref(v_type_5367_);
                    v_value_5368_ = crate::leanh::lean_ctor_get(v_e_5221_, 2);
                    crate::leanh::lean_inc_ref(v_value_5368_);
                    v_body_5369_ = crate::leanh::lean_ctor_get(v_e_5221_, 3);
                    crate::leanh::lean_inc_ref(v_body_5369_);
                    v_nondep_5370_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 4);
                    v___x_5371_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5371_) == 0 {
                        v_a_5372_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
                        crate::leanh::lean_inc_n(v_a_5372_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5371_, 1);
                        crate::leanh::lean_inc_ref(v_subst_5222_);
                        v___x_5373_ = lean_array_push(v_subst_5222_, v_a_5372_);
                        v___x_5374_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_body_5369_,
                            v___x_5373_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5374_) == 0 {
                            v_a_5375_ = crate::leanh::lean_ctor_get(v___x_5374_, 0);
                            v_isSharedCheck_5417_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5374_)) as u8;
                            if v_isSharedCheck_5417_ == 0 {
                                v___x_5377_ = v___x_5374_;
                                v_isShared_5378_ = v_isSharedCheck_5417_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5375_);
                                crate::leanh::lean_dec(v___x_5374_);
                                v___x_5377_ = crate::leanh::lean_box(0);
                                v_isShared_5378_ = v_isSharedCheck_5417_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5372_);
                            crate::leanh::lean_dec_ref(v_value_5368_);
                            crate::leanh::lean_dec_ref(v_type_5367_);
                            crate::leanh::lean_dec(v_declName_5366_);
                            crate::leanh::lean_dec_ref(v_subst_5222_);
                            return v___x_5374_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5369_);
                        crate::leanh::lean_dec_ref(v_value_5368_);
                        crate::leanh::lean_dec_ref(v_type_5367_);
                        crate::leanh::lean_dec(v_declName_5366_);
                        crate::leanh::lean_dec_ref(v_subst_5222_);
                        v_a_5418_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
                        v_isSharedCheck_5425_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5371_)) as u8;
                        if v_isSharedCheck_5425_ == 0 {
                            v___x_5420_ = v___x_5371_;
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5418_);
                            crate::leanh::lean_dec(v___x_5371_);
                            v___x_5420_ = crate::leanh::lean_box(0);
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 25;
                            continue;
                        }
                    }
                }
                10 => {
                    v_data_5426_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc(v_data_5426_);
                    v_expr_5427_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc_ref(v_expr_5427_);
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 2);
                    v___x_5428_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_expr_5427_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5428_) == 0 {
                        v_a_5429_ = crate::leanh::lean_ctor_get(v___x_5428_, 0);
                        v_isSharedCheck_5438_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5428_)) as u8;
                        if v_isSharedCheck_5438_ == 0 {
                            v___x_5431_ = v___x_5428_;
                            v_isShared_5432_ = v_isSharedCheck_5438_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5429_);
                            crate::leanh::lean_dec(v___x_5428_);
                            v___x_5431_ = crate::leanh::lean_box(0);
                            v_isShared_5432_ = v_isSharedCheck_5438_;
                            state = 27;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_data_5426_);
                        return v___x_5428_;
                    }
                }
                11 => {
                    v_typeName_5439_ = crate::leanh::lean_ctor_get(v_e_5221_, 0);
                    crate::leanh::lean_inc(v_typeName_5439_);
                    v_idx_5440_ = crate::leanh::lean_ctor_get(v_e_5221_, 1);
                    crate::leanh::lean_inc(v_idx_5440_);
                    v_struct_5441_ = crate::leanh::lean_ctor_get(v_e_5221_, 2);
                    crate::leanh::lean_inc_ref(v_struct_5441_);
                    crate::leanh::lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5442_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_struct_5441_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5442_) == 0 {
                        v_a_5443_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5452_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5452_ == 0 {
                            v___x_5445_ = v___x_5442_;
                            v_isShared_5446_ = v_isSharedCheck_5452_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5443_);
                            crate::leanh::lean_dec(v___x_5442_);
                            v___x_5445_ = crate::leanh::lean_box(0);
                            v_isShared_5446_ = v_isSharedCheck_5452_;
                            state = 29;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_idx_5440_);
                        crate::leanh::lean_dec(v_typeName_5439_);
                        return v___x_5442_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_subst_5222_);
                    v___x_5453_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                    );
                    v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5454_, 0, v_e_5221_);
                    crate::leanh::lean_ctor_set(v___x_5454_, 1, v___x_5453_);
                    v___x_5455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5455_, 0, v___x_5454_);
                    return v___x_5455_;
                }
            },
            1 => {
                v_fst_5271_ = crate::leanh::lean_ctor_get(v_a_5267_, 0);
                v_snd_5272_ = crate::leanh::lean_ctor_get(v_a_5267_, 1);
                v_isSharedCheck_5284_ = (!crate::leanh::lean_is_exclusive(v_a_5267_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v___x_5274_ = v_a_5267_;
                    v_isShared_5275_ = v_isSharedCheck_5284_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5272_);
                    crate::leanh::lean_inc(v_fst_5271_);
                    crate::leanh::lean_dec(v_a_5267_);
                    v___x_5274_ = crate::leanh::lean_box(0);
                    v_isShared_5275_ = v_isSharedCheck_5284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5276_ = l_Lean_Expr_app___override(v_fst_5264_, v_fst_5271_);
                v___x_5277_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5265_, v_snd_5272_);
                crate::leanh::lean_dec(v_snd_5265_);
                if v_isShared_5275_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5274_, 1, v___x_5277_);
                    crate::leanh::lean_ctor_set(v___x_5274_, 0, v___x_5276_);
                    v___x_5279_ = v___x_5274_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5277_);
                    v___x_5279_ = v_reuseFailAlloc_5283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5269_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5281_;
            }
            5 => {
                v_fst_5302_ = crate::leanh::lean_ctor_get(v_a_5298_, 0);
                v_snd_5303_ = crate::leanh::lean_ctor_get(v_a_5298_, 1);
                v_isSharedCheck_5316_ = (!crate::leanh::lean_is_exclusive(v_a_5298_)) as u8;
                if v_isSharedCheck_5316_ == 0 {
                    v___x_5305_ = v_a_5298_;
                    v_isShared_5306_ = v_isSharedCheck_5316_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5303_);
                    crate::leanh::lean_inc(v_fst_5302_);
                    crate::leanh::lean_dec(v_a_5298_);
                    v___x_5305_ = crate::leanh::lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5316_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5307_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5295_, v_snd_5303_);
                crate::leanh::lean_dec(v_snd_5295_);
                v___x_5308_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_5307_, v_a_5291_);
                crate::leanh::lean_dec(v_a_5291_);
                v___x_5309_ = l_Lean_Expr_lam___override(
                    v_binderName_5286_,
                    v_fst_5294_,
                    v_fst_5302_,
                    v_binderInfo_5289_,
                );
                if v_isShared_5306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5305_, 1, v___x_5308_);
                    crate::leanh::lean_ctor_set(v___x_5305_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5305_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 1, v___x_5308_);
                    v___x_5311_ = v_reuseFailAlloc_5315_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5300_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5300_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5313_;
            }
            9 => {
                if v_isShared_5321_ == 0 {
                    v___x_5323_ = v___x_5320_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5323_;
            }
            11 => {
                v_fst_5342_ = crate::leanh::lean_ctor_get(v_a_5338_, 0);
                v_snd_5343_ = crate::leanh::lean_ctor_get(v_a_5338_, 1);
                v_isSharedCheck_5356_ = (!crate::leanh::lean_is_exclusive(v_a_5338_)) as u8;
                if v_isSharedCheck_5356_ == 0 {
                    v___x_5345_ = v_a_5338_;
                    v_isShared_5346_ = v_isSharedCheck_5356_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5343_);
                    crate::leanh::lean_inc(v_fst_5342_);
                    crate::leanh::lean_dec(v_a_5338_);
                    v___x_5345_ = crate::leanh::lean_box(0);
                    v_isShared_5346_ = v_isSharedCheck_5356_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5347_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5335_, v_snd_5343_);
                crate::leanh::lean_dec(v_snd_5335_);
                v___x_5348_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_5347_, v_a_5331_);
                crate::leanh::lean_dec(v_a_5331_);
                v___x_5349_ = l_Lean_Expr_forallE___override(
                    v_binderName_5326_,
                    v_fst_5334_,
                    v_fst_5342_,
                    v_binderInfo_5329_,
                );
                if v_isShared_5346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5345_, 1, v___x_5348_);
                    crate::leanh::lean_ctor_set(v___x_5345_, 0, v___x_5349_);
                    v___x_5351_ = v___x_5345_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 1, v___x_5348_);
                    v___x_5351_ = v_reuseFailAlloc_5355_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5340_, 0, v___x_5351_);
                    v___x_5353_ = v___x_5340_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5351_);
                    v___x_5353_ = v_reuseFailAlloc_5354_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5353_;
            }
            15 => {
                if v_isShared_5361_ == 0 {
                    v___x_5363_ = v___x_5360_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5363_;
            }
            17 => {
                v_fst_5379_ = crate::leanh::lean_ctor_get(v_a_5375_, 0);
                crate::leanh::lean_inc(v_fst_5379_);
                v_snd_5380_ = crate::leanh::lean_ctor_get(v_a_5375_, 1);
                crate::leanh::lean_inc(v_snd_5380_);
                crate::leanh::lean_dec(v_a_5375_);
                if v_isShared_5378_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5377_, 1);
                    crate::leanh::lean_ctor_set(v___x_5377_, 0, v_value_5368_);
                    v___x_5382_ = v___x_5377_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_value_5368_);
                    v___x_5382_ = v_reuseFailAlloc_5416_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5383_ = l_Lean_Elab_Tactic_Do_countUsesDecl(
                    v_a_5372_,
                    v_type_5367_,
                    v___x_5382_,
                    v_snd_5380_,
                    v_subst_5222_,
                    v_a_5223_,
                    v_a_5224_,
                    v_a_5225_,
                    v_a_5226_,
                );
                crate::leanh::lean_dec(v_a_5372_);
                if crate::leanh::lean_obj_tag(v___x_5383_) == 0 {
                    v_a_5384_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                    v_isSharedCheck_5407_ = (!crate::leanh::lean_is_exclusive(v___x_5383_)) as u8;
                    if v_isSharedCheck_5407_ == 0 {
                        v___x_5386_ = v___x_5383_;
                        v_isShared_5387_ = v_isSharedCheck_5407_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5384_);
                        crate::leanh::lean_dec(v___x_5383_);
                        v___x_5386_ = crate::leanh::lean_box(0);
                        v_isShared_5387_ = v_isSharedCheck_5407_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5379_);
                    crate::leanh::lean_dec(v_declName_5366_);
                    v_a_5408_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                    v_isSharedCheck_5415_ = (!crate::leanh::lean_is_exclusive(v___x_5383_)) as u8;
                    if v_isSharedCheck_5415_ == 0 {
                        v___x_5410_ = v___x_5383_;
                        v_isShared_5411_ = v_isSharedCheck_5415_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5408_);
                        crate::leanh::lean_dec(v___x_5383_);
                        v___x_5410_ = crate::leanh::lean_box(0);
                        v_isShared_5411_ = v_isSharedCheck_5415_;
                        state = 23;
                        continue;
                    }
                }
            }
            19 => {
                v_snd_5388_ = crate::leanh::lean_ctor_get(v_a_5384_, 1);
                crate::leanh::lean_inc(v_snd_5388_);
                v_fst_5389_ = crate::leanh::lean_ctor_get(v_snd_5388_, 0);
                crate::leanh::lean_inc(v_fst_5389_);
                if crate::leanh::lean_obj_tag(v_fst_5389_) == 1 {
                    v_fst_5390_ = crate::leanh::lean_ctor_get(v_a_5384_, 0);
                    crate::leanh::lean_inc(v_fst_5390_);
                    crate::leanh::lean_dec(v_a_5384_);
                    v_snd_5391_ = crate::leanh::lean_ctor_get(v_snd_5388_, 1);
                    v_isSharedCheck_5403_ = (!crate::leanh::lean_is_exclusive(v_snd_5388_)) as u8;
                    if v_isSharedCheck_5403_ == 0 {
                        v_unused_5404_ = crate::leanh::lean_ctor_get(v_snd_5388_, 0);
                        crate::leanh::lean_dec(v_unused_5404_);
                        v___x_5393_ = v_snd_5388_;
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5391_);
                        crate::leanh::lean_dec(v_snd_5388_);
                        v___x_5393_ = crate::leanh::lean_box(0);
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5389_);
                    crate::leanh::lean_dec(v_snd_5388_);
                    crate::leanh::lean_del_object(v___x_5386_);
                    crate::leanh::lean_dec(v_a_5384_);
                    crate::leanh::lean_dec(v_fst_5379_);
                    crate::leanh::lean_dec(v_declName_5366_);
                    v___x_5405_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__5_once),
                        _init_l_Lean_Elab_Tactic_Do_countUses___closed__5,
                    );
                    v___x_5406_ =
                        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
                            v___x_5405_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                    return v___x_5406_;
                }
            }
            20 => {
                v_val_5395_ = crate::leanh::lean_ctor_get(v_fst_5389_, 0);
                crate::leanh::lean_inc(v_val_5395_);
                crate::leanh::lean_dec_ref_known(v_fst_5389_, 1);
                v___x_5396_ = l_Lean_Expr_letE___override(
                    v_declName_5366_,
                    v_fst_5390_,
                    v_val_5395_,
                    v_fst_5379_,
                    v_nondep_5370_,
                );
                if v_isShared_5394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5393_, 0, v___x_5396_);
                    v___x_5398_ = v___x_5393_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_snd_5391_);
                    v___x_5398_ = v_reuseFailAlloc_5402_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v___x_5398_);
                    v___x_5400_ = v___x_5386_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
                    v___x_5400_ = v_reuseFailAlloc_5401_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5400_;
            }
            23 => {
                if v_isShared_5411_ == 0 {
                    v___x_5413_ = v___x_5410_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
                    v___x_5413_ = v_reuseFailAlloc_5414_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5413_;
            }
            25 => {
                if v_isShared_5421_ == 0 {
                    v___x_5423_ = v___x_5420_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
                    v___x_5423_ = v_reuseFailAlloc_5424_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5423_;
            }
            27 => {
                v___f_5433_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_countUses___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5433_, 0, v_data_5426_);
                v___x_5434_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5433_, v_a_5429_);
                if v_isShared_5432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5431_, 0, v___x_5434_);
                    v___x_5436_ = v___x_5431_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5436_;
            }
            29 => {
                v___f_5447_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_countUses___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_5447_, 0, v_typeName_5439_);
                crate::leanh::lean_closure_set(v___f_5447_, 1, v_idx_5440_);
                v___x_5448_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5447_, v_a_5443_);
                if v_isShared_5446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5448_);
                    v___x_5450_ = v___x_5445_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5448_);
                    v___x_5450_ = v_reuseFailAlloc_5451_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesDecl(
    mut v_fvarId_5456_: *mut crate::leanh::LeanObject,
    mut v_ty_5457_: *mut crate::leanh::LeanObject,
    mut v_val_x3f_5458_: *mut crate::leanh::LeanObject,
    mut v_bodyUses_5459_: *mut crate::leanh::LeanObject,
    mut v_subst_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
    mut v_a_5462_: *mut crate::leanh::LeanObject,
    mut v_a_5463_: *mut crate::leanh::LeanObject,
    mut v_a_5464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v_fst_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___y_5477_: u8 = 0;
    let mut v___y_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: u8 = 0;
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5516_: u8 = 0;
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_subst_5460_);
                v___x_5466_ = l_Lean_Elab_Tactic_Do_countUses(
                    v_ty_5457_,
                    v_subst_5460_,
                    v_a_5461_,
                    v_a_5462_,
                    v_a_5463_,
                    v_a_5464_,
                );
                if crate::leanh::lean_obj_tag(v___x_5466_) == 0 {
                    v_a_5467_ = crate::leanh::lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5522_ = (!crate::leanh::lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5522_ == 0 {
                        v___x_5469_ = v___x_5466_;
                        v_isShared_5470_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5467_);
                        crate::leanh::lean_dec(v___x_5466_);
                        v___x_5469_ = crate::leanh::lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_subst_5460_);
                    crate::leanh::lean_dec_ref(v_bodyUses_5459_);
                    crate::leanh::lean_dec(v_val_x3f_5458_);
                    v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5466_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5523_);
                        crate::leanh::lean_dec(v___x_5466_);
                        v___x_5525_ = crate::leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5471_ = crate::leanh::lean_ctor_get(v_a_5467_, 0);
                v_snd_5472_ = crate::leanh::lean_ctor_get(v_a_5467_, 1);
                v_isSharedCheck_5521_ = (!crate::leanh::lean_is_exclusive(v_a_5467_)) as u8;
                if v_isSharedCheck_5521_ == 0 {
                    v___x_5474_ = v_a_5467_;
                    v_isShared_5475_ = v_isSharedCheck_5521_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5472_);
                    crate::leanh::lean_inc(v_fst_5471_);
                    crate::leanh::lean_dec(v_a_5467_);
                    v___x_5474_ = crate::leanh::lean_box(0);
                    v_isShared_5475_ = v_isSharedCheck_5521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_x3f_5458_) == 0 {
                    crate::leanh::lean_dec_ref(v_subst_5460_);
                    v___x_5505_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                    );
                    v_fst_5494_ = v_val_x3f_5458_;
                    v_snd_5495_ = v___x_5505_;
                    state = 6;
                    continue;
                } else {
                    v_val_5506_ = crate::leanh::lean_ctor_get(v_val_x3f_5458_, 0);
                    crate::leanh::lean_inc(v_val_5506_);
                    crate::leanh::lean_dec_ref_known(v_val_x3f_5458_, 1);
                    v___x_5507_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_val_5506_,
                        v_subst_5460_,
                        v_a_5461_,
                        v_a_5462_,
                        v_a_5463_,
                        v_a_5464_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        crate::leanh::lean_inc(v_a_5508_);
                        crate::leanh::lean_dec_ref_known(v___x_5507_, 1);
                        v___f_5509_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
                        v___x_5510_ =
                            l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5509_, v_a_5508_);
                        v_fst_5511_ = crate::leanh::lean_ctor_get(v___x_5510_, 0);
                        crate::leanh::lean_inc(v_fst_5511_);
                        v_snd_5512_ = crate::leanh::lean_ctor_get(v___x_5510_, 1);
                        crate::leanh::lean_inc(v_snd_5512_);
                        crate::leanh::lean_dec_ref(v___x_5510_);
                        v_fst_5494_ = v_fst_5511_;
                        v_snd_5495_ = v_snd_5512_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5474_);
                        crate::leanh::lean_dec(v_snd_5472_);
                        crate::leanh::lean_dec(v_fst_5471_);
                        crate::leanh::lean_del_object(v___x_5469_);
                        crate::leanh::lean_dec_ref(v_bodyUses_5459_);
                        v_a_5513_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5520_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5520_ == 0 {
                            v___x_5515_ = v___x_5507_;
                            v_isShared_5516_ = v_isSharedCheck_5520_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5513_);
                            crate::leanh::lean_dec(v___x_5507_);
                            v___x_5515_ = crate::leanh::lean_box(0);
                            v_isShared_5516_ = v_isSharedCheck_5520_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_5480_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_5479_, v_fvarId_5456_);
                v___x_5481_ = crate::leanh::lean_box(0);
                v___x_5482_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                v___x_5483_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_5477_);
                v___x_5484_ = l_Lean_KVMap_setNat(v___x_5481_, v___x_5482_, v___x_5483_);
                v___x_5485_ = l_Lean_Elab_Tactic_Do_addMData(v___x_5484_, v_fst_5471_);
                if v_isShared_5475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5474_, 1, v___x_5480_);
                    crate::leanh::lean_ctor_set(v___x_5474_, 0, v___y_5478_);
                    v___x_5487_ = v___x_5474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___y_5478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 1, v___x_5480_);
                    v___x_5487_ = v_reuseFailAlloc_5492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5488_, 0, v___x_5485_);
                crate::leanh::lean_ctor_set(v___x_5488_, 1, v___x_5487_);
                if v_isShared_5470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5469_, 0, v___x_5488_);
                    v___x_5490_ = v___x_5469_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5490_;
            }
            6 => {
                v___x_5496_ = 0;
                v___x_5497_ = crate::leanh::lean_box((v___x_5496_) as usize);
                v___x_5498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_5459_, v_fvarId_5456_, v___x_5497_);
                crate::leanh::lean_dec(v___x_5497_);
                v___x_5499_ = (crate::leanh::lean_unbox(v___x_5498_) as u8);
                v___x_5500_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_5499_, v___x_5496_);
                if v___x_5500_ == 0 {
                    v___x_5501_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_5459_, v_snd_5472_);
                    crate::leanh::lean_dec_ref(v_bodyUses_5459_);
                    v___x_5502_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_5501_, v_snd_5495_);
                    crate::leanh::lean_dec_ref(v___x_5501_);
                    v___x_5503_ = (crate::leanh::lean_unbox(v___x_5498_) as u8);
                    crate::leanh::lean_dec(v___x_5498_);
                    v___y_5477_ = v___x_5503_;
                    v___y_5478_ = v_fst_5494_;
                    v___y_5479_ = v___x_5502_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_snd_5495_);
                    crate::leanh::lean_dec(v_snd_5472_);
                    v___x_5504_ = (crate::leanh::lean_unbox(v___x_5498_) as u8);
                    crate::leanh::lean_dec(v___x_5498_);
                    v___y_5477_ = v___x_5504_;
                    v___y_5478_ = v_fst_5494_;
                    v___y_5479_ = v_bodyUses_5459_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_5516_ == 0 {
                    v___x_5518_ = v___x_5515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
                    v___x_5518_ = v_reuseFailAlloc_5519_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5518_;
            }
            9 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(
    mut v_fvarId_5531_: *mut crate::leanh::LeanObject,
    mut v_ty_5532_: *mut crate::leanh::LeanObject,
    mut v_val_x3f_5533_: *mut crate::leanh::LeanObject,
    mut v_bodyUses_5534_: *mut crate::leanh::LeanObject,
    mut v_subst_5535_: *mut crate::leanh::LeanObject,
    mut v_a_5536_: *mut crate::leanh::LeanObject,
    mut v_a_5537_: *mut crate::leanh::LeanObject,
    mut v_a_5538_: *mut crate::leanh::LeanObject,
    mut v_a_5539_: *mut crate::leanh::LeanObject,
    mut v_a_5540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5541_ = l_Lean_Elab_Tactic_Do_countUsesDecl(
        v_fvarId_5531_,
        v_ty_5532_,
        v_val_x3f_5533_,
        v_bodyUses_5534_,
        v_subst_5535_,
        v_a_5536_,
        v_a_5537_,
        v_a_5538_,
        v_a_5539_,
    );
    crate::leanh::lean_dec(v_a_5539_);
    crate::leanh::lean_dec_ref(v_a_5538_);
    crate::leanh::lean_dec(v_a_5537_);
    crate::leanh::lean_dec_ref(v_a_5536_);
    crate::leanh::lean_dec(v_fvarId_5531_);
    return v_res_5541_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___boxed(
    mut v_e_5542_: *mut crate::leanh::LeanObject,
    mut v_subst_5543_: *mut crate::leanh::LeanObject,
    mut v_a_5544_: *mut crate::leanh::LeanObject,
    mut v_a_5545_: *mut crate::leanh::LeanObject,
    mut v_a_5546_: *mut crate::leanh::LeanObject,
    mut v_a_5547_: *mut crate::leanh::LeanObject,
    mut v_a_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5549_ = l_Lean_Elab_Tactic_Do_countUses(
        v_e_5542_,
        v_subst_5543_,
        v_a_5544_,
        v_a_5545_,
        v_a_5546_,
        v_a_5547_,
    );
    crate::leanh::lean_dec(v_a_5547_);
    crate::leanh::lean_dec_ref(v_a_5546_);
    crate::leanh::lean_dec(v_a_5545_);
    crate::leanh::lean_dec_ref(v_a_5544_);
    return v_res_5549_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(
    mut v_00_u03b2_5550_: *mut crate::leanh::LeanObject,
    mut v_m_5551_: *mut crate::leanh::LeanObject,
    mut v_a_5552_: *mut crate::leanh::LeanObject,
    mut v_fallback_5553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_5551_, v_a_5552_, v_fallback_5553_);
    return v___x_5554_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(
    mut v_00_u03b2_5555_: *mut crate::leanh::LeanObject,
    mut v_m_5556_: *mut crate::leanh::LeanObject,
    mut v_a_5557_: *mut crate::leanh::LeanObject,
    mut v_fallback_5558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_5555_, v_m_5556_, v_a_5557_, v_fallback_5558_);
    crate::leanh::lean_dec(v_fallback_5558_);
    crate::leanh::lean_dec(v_a_5557_);
    crate::leanh::lean_dec_ref(v_m_5556_);
    return v_res_5559_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(
    mut v_00_u03b2_5560_: *mut crate::leanh::LeanObject,
    mut v_m_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_5561_, v_a_5562_);
    return v___x_5563_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(
    mut v_00_u03b2_5564_: *mut crate::leanh::LeanObject,
    mut v_m_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5567_ =
        l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(
            v_00_u03b2_5564_,
            v_m_5565_,
            v_a_5566_,
        );
    crate::leanh::lean_dec(v_a_5566_);
    return v_res_5567_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(
    mut v_00_u03b1_5568_: *mut crate::leanh::LeanObject,
    mut v_msg_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5575_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
        v_msg_5569_,
        v___y_5570_,
        v___y_5571_,
        v___y_5572_,
        v___y_5573_,
    );
    return v___x_5575_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(
    mut v_00_u03b1_5576_: *mut crate::leanh::LeanObject,
    mut v_msg_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(
        v_00_u03b1_5576_,
        v_msg_5577_,
        v___y_5578_,
        v___y_5579_,
        v___y_5580_,
        v___y_5581_,
    );
    crate::leanh::lean_dec(v___y_5581_);
    crate::leanh::lean_dec_ref(v___y_5580_);
    crate::leanh::lean_dec(v___y_5579_);
    crate::leanh::lean_dec_ref(v___y_5578_);
    return v_res_5583_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(
    mut v_00_u03b2_5584_: *mut crate::leanh::LeanObject,
    mut v_m_5585_: *mut crate::leanh::LeanObject,
    mut v_a_5586_: *mut crate::leanh::LeanObject,
    mut v_b_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_5585_, v_a_5586_, v_b_5587_);
    return v___x_5588_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5594_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5592_);
    return v___x_5594_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5600_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    crate::leanh::lean_dec(v___y_5598_);
    crate::leanh::lean_dec_ref(v___y_5597_);
    crate::leanh::lean_dec(v___y_5596_);
    crate::leanh::lean_dec_ref(v___y_5595_);
    return v_res_5600_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(
    mut v_00_u03b2_5601_: *mut crate::leanh::LeanObject,
    mut v_a_5602_: *mut crate::leanh::LeanObject,
    mut v_fallback_5603_: *mut crate::leanh::LeanObject,
    mut v_x_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_5602_, v_fallback_5603_, v_x_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_5606_: *mut crate::leanh::LeanObject,
    mut v_a_5607_: *mut crate::leanh::LeanObject,
    mut v_fallback_5608_: *mut crate::leanh::LeanObject,
    mut v_x_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_5606_, v_a_5607_, v_fallback_5608_, v_x_5609_);
    crate::leanh::lean_dec(v_x_5609_);
    crate::leanh::lean_dec(v_fallback_5608_);
    crate::leanh::lean_dec(v_a_5607_);
    return v_res_5610_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(
    mut v_00_u03b2_5611_: *mut crate::leanh::LeanObject,
    mut v_a_5612_: *mut crate::leanh::LeanObject,
    mut v_x_5613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5614_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5612_, v_x_5613_);
    return v___x_5614_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(
    mut v_00_u03b2_5615_: *mut crate::leanh::LeanObject,
    mut v_a_5616_: *mut crate::leanh::LeanObject,
    mut v_x_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_5615_, v_a_5616_, v_x_5617_);
    crate::leanh::lean_dec(v_a_5616_);
    return v_res_5618_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(
    mut v_00_u03b2_5619_: *mut crate::leanh::LeanObject,
    mut v_a_5620_: *mut crate::leanh::LeanObject,
    mut v_b_5621_: *mut crate::leanh::LeanObject,
    mut v_x_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_5620_, v_b_5621_, v_x_5622_);
    return v___x_5623_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(
    mut v_as_5626_: *mut crate::leanh::LeanObject,
    mut v_i_5627_: usize,
    mut v_stop_5628_: usize,
    mut v_b_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: usize = 0;
    let mut v___x_5637_: usize = 0;
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v___y_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5635_ = lean_usize_dec_eq(v_i_5627_, v_stop_5628_);
                if v___x_5635_ == 0 {
                    v___x_5636_ = 1usize;
                    v___x_5637_ = lean_usize_sub(v_i_5627_, v___x_5636_);
                    v___x_5638_ = lean_array_uget_borrowed(v_as_5626_, v___x_5637_);
                    if crate::leanh::lean_obj_tag(v___x_5638_) == 0 {
                        v_i_5627_ = v___x_5637_;
                        state = 0;
                        continue;
                    } else {
                        v_val_5640_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                        v_fst_5641_ = crate::leanh::lean_ctor_get(v_b_5629_, 0);
                        crate::leanh::lean_inc(v_fst_5641_);
                        v_snd_5642_ = crate::leanh::lean_ctor_get(v_b_5629_, 1);
                        crate::leanh::lean_inc(v_snd_5642_);
                        crate::leanh::lean_dec_ref(v_b_5629_);
                        v___x_5643_ = l_Lean_LocalDecl_fvarId(v_val_5640_);
                        v___x_5644_ = l_Lean_LocalDecl_type(v_val_5640_);
                        v___x_5645_ = l_Lean_LocalDecl_value_x3f(v_val_5640_, v___x_5635_);
                        v___x_5646_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0;
                        v___x_5647_ = l_Lean_Elab_Tactic_Do_countUsesDecl(
                            v___x_5643_,
                            v___x_5644_,
                            v___x_5645_,
                            v_snd_5642_,
                            v___x_5646_,
                            v___y_5630_,
                            v___y_5631_,
                            v___y_5632_,
                            v___y_5633_,
                        );
                        crate::leanh::lean_dec(v___x_5643_);
                        if crate::leanh::lean_obj_tag(v___x_5647_) == 0 {
                            v_a_5648_ = crate::leanh::lean_ctor_get(v___x_5647_, 0);
                            crate::leanh::lean_inc(v_a_5648_);
                            crate::leanh::lean_dec_ref_known(v___x_5647_, 1);
                            v_snd_5649_ = crate::leanh::lean_ctor_get(v_a_5648_, 1);
                            crate::leanh::lean_inc(v_snd_5649_);
                            v_fst_5650_ = crate::leanh::lean_ctor_get(v_a_5648_, 0);
                            crate::leanh::lean_inc(v_fst_5650_);
                            crate::leanh::lean_dec(v_a_5648_);
                            v_fst_5651_ = crate::leanh::lean_ctor_get(v_snd_5649_, 0);
                            v_snd_5652_ = crate::leanh::lean_ctor_get(v_snd_5649_, 1);
                            v_isSharedCheck_5667_ =
                                (!crate::leanh::lean_is_exclusive(v_snd_5649_)) as u8;
                            if v_isSharedCheck_5667_ == 0 {
                                v___x_5654_ = v_snd_5649_;
                                v_isShared_5655_ = v_isSharedCheck_5667_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5652_);
                                crate::leanh::lean_inc(v_fst_5651_);
                                crate::leanh::lean_dec(v_snd_5649_);
                                v___x_5654_ = crate::leanh::lean_box(0);
                                v_isShared_5655_ = v_isSharedCheck_5667_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_5641_);
                            v_a_5668_ = crate::leanh::lean_ctor_get(v___x_5647_, 0);
                            v_isSharedCheck_5675_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5647_)) as u8;
                            if v_isSharedCheck_5675_ == 0 {
                                v___x_5670_ = v___x_5647_;
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5668_);
                                crate::leanh::lean_dec(v___x_5647_);
                                v___x_5670_ = crate::leanh::lean_box(0);
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5676_, 0, v_b_5629_);
                    return v___x_5676_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_fst_5651_) == 0 {
                    crate::leanh::lean_inc(v_val_5640_);
                    v___x_5663_ = l_Lean_LocalDecl_setType(v_val_5640_, v_fst_5650_);
                    v___y_5657_ = v___x_5663_;
                    state = 2;
                    continue;
                } else {
                    v_val_5664_ = crate::leanh::lean_ctor_get(v_fst_5651_, 0);
                    crate::leanh::lean_inc(v_val_5664_);
                    crate::leanh::lean_dec_ref_known(v_fst_5651_, 1);
                    crate::leanh::lean_inc(v_val_5640_);
                    v___x_5665_ = l_Lean_LocalDecl_setType(v_val_5640_, v_fst_5650_);
                    v___x_5666_ = l_Lean_LocalDecl_setValue(v___x_5665_, v_val_5664_);
                    v___y_5657_ = v___x_5666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5658_ = lean_array_push(v_fst_5641_, v___y_5657_);
                if v_isShared_5655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5654_, 0, v___x_5658_);
                    v___x_5660_ = v___x_5654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_snd_5652_);
                    v___x_5660_ = v_reuseFailAlloc_5662_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_5627_ = v___x_5637_;
                v_b_5629_ = v___x_5660_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_5671_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(
    mut v_as_5677_: *mut crate::leanh::LeanObject,
    mut v_i_5678_: *mut crate::leanh::LeanObject,
    mut v_stop_5679_: *mut crate::leanh::LeanObject,
    mut v_b_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5686_: usize = 0;
    let mut v_stop_boxed_5687_: usize = 0;
    let mut v_res_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5686_ = crate::leanh::lean_unbox_usize(v_i_5678_);
    crate::leanh::lean_dec(v_i_5678_);
    v_stop_boxed_5687_ = crate::leanh::lean_unbox_usize(v_stop_5679_);
    crate::leanh::lean_dec(v_stop_5679_);
    v_res_5688_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_5677_, v_i_boxed_5686_, v_stop_boxed_5687_, v_b_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    crate::leanh::lean_dec(v___y_5684_);
    crate::leanh::lean_dec_ref(v___y_5683_);
    crate::leanh::lean_dec(v___y_5682_);
    crate::leanh::lean_dec_ref(v___y_5681_);
    crate::leanh::lean_dec_ref(v_as_5677_);
    return v_res_5688_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(
    mut v_x_5689_: *mut crate::leanh::LeanObject,
    mut v_x_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: usize = 0;
    let mut v___x_5707_: usize = 0;
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v_vs_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5713_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: usize = 0;
    let mut v___x_5721_: usize = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5689_) == 0 {
                    v_cs_5696_ = crate::leanh::lean_ctor_get(v_x_5689_, 0);
                    v_isSharedCheck_5709_ = (!crate::leanh::lean_is_exclusive(v_x_5689_)) as u8;
                    if v_isSharedCheck_5709_ == 0 {
                        v___x_5698_ = v_x_5689_;
                        v_isShared_5699_ = v_isSharedCheck_5709_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_5696_);
                        crate::leanh::lean_dec(v_x_5689_);
                        v___x_5698_ = crate::leanh::lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5710_ = crate::leanh::lean_ctor_get(v_x_5689_, 0);
                    v_isSharedCheck_5723_ = (!crate::leanh::lean_is_exclusive(v_x_5689_)) as u8;
                    if v_isSharedCheck_5723_ == 0 {
                        v___x_5712_ = v_x_5689_;
                        v_isShared_5713_ = v_isSharedCheck_5723_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5710_);
                        crate::leanh::lean_dec(v_x_5689_);
                        v___x_5712_ = crate::leanh::lean_box(0);
                        v_isShared_5713_ = v_isSharedCheck_5723_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5700_ = lean_array_get_size(v_cs_5696_);
                v___x_5701_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5702_ = lean_nat_dec_lt(v___x_5701_, v___x_5700_);
                if v___x_5702_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_5696_);
                    if v_isShared_5699_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5698_, 0, v_x_5690_);
                        v___x_5704_ = v___x_5698_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_x_5690_);
                        v___x_5704_ = v_reuseFailAlloc_5705_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5698_);
                    v___x_5706_ = lean_usize_of_nat(v___x_5700_);
                    v___x_5707_ = 0usize;
                    v___x_5708_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_5696_, v___x_5706_, v___x_5707_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                    crate::leanh::lean_dec_ref(v_cs_5696_);
                    return v___x_5708_;
                }
            }
            2 => {
                return v___x_5704_;
            }
            3 => {
                v___x_5714_ = lean_array_get_size(v_vs_5710_);
                v___x_5715_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5716_ = lean_nat_dec_lt(v___x_5715_, v___x_5714_);
                if v___x_5716_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_5710_);
                    if v_isShared_5713_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5712_, 0);
                        crate::leanh::lean_ctor_set(v___x_5712_, 0, v_x_5690_);
                        v___x_5718_ = v___x_5712_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_x_5690_);
                        v___x_5718_ = v_reuseFailAlloc_5719_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5712_);
                    v___x_5720_ = lean_usize_of_nat(v___x_5714_);
                    v___x_5721_ = 0usize;
                    v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_5710_, v___x_5720_, v___x_5721_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                    crate::leanh::lean_dec_ref(v_vs_5710_);
                    return v___x_5722_;
                }
            }
            4 => {
                return v___x_5718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(
    mut v_as_5724_: *mut crate::leanh::LeanObject,
    mut v_i_5725_: usize,
    mut v_stop_5726_: usize,
    mut v_b_5727_: *mut crate::leanh::LeanObject,
    mut v___y_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5733_: u8 = 0;
    let mut v___x_5734_: usize = 0;
    let mut v___x_5735_: usize = 0;
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5733_ = lean_usize_dec_eq(v_i_5725_, v_stop_5726_);
                if v___x_5733_ == 0 {
                    v___x_5734_ = 1usize;
                    v___x_5735_ = lean_usize_sub(v_i_5725_, v___x_5734_);
                    v___x_5736_ = lean_array_uget_borrowed(v_as_5724_, v___x_5735_);
                    crate::leanh::lean_inc(v___x_5736_);
                    v___x_5737_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_5736_, v_b_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
                    if crate::leanh::lean_obj_tag(v___x_5737_) == 0 {
                        v_a_5738_ = crate::leanh::lean_ctor_get(v___x_5737_, 0);
                        crate::leanh::lean_inc(v_a_5738_);
                        crate::leanh::lean_dec_ref_known(v___x_5737_, 1);
                        v_i_5725_ = v___x_5735_;
                        v_b_5727_ = v_a_5738_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5737_;
                    }
                } else {
                    v___x_5740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5740_, 0, v_b_5727_);
                    return v___x_5740_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_as_5741_: *mut crate::leanh::LeanObject,
    mut v_i_5742_: *mut crate::leanh::LeanObject,
    mut v_stop_5743_: *mut crate::leanh::LeanObject,
    mut v_b_5744_: *mut crate::leanh::LeanObject,
    mut v___y_5745_: *mut crate::leanh::LeanObject,
    mut v___y_5746_: *mut crate::leanh::LeanObject,
    mut v___y_5747_: *mut crate::leanh::LeanObject,
    mut v___y_5748_: *mut crate::leanh::LeanObject,
    mut v___y_5749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5750_: usize = 0;
    let mut v_stop_boxed_5751_: usize = 0;
    let mut v_res_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5750_ = crate::leanh::lean_unbox_usize(v_i_5742_);
    crate::leanh::lean_dec(v_i_5742_);
    v_stop_boxed_5751_ = crate::leanh::lean_unbox_usize(v_stop_5743_);
    crate::leanh::lean_dec(v_stop_5743_);
    v_res_5752_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_5741_, v_i_boxed_5750_, v_stop_boxed_5751_, v_b_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
    crate::leanh::lean_dec(v___y_5748_);
    crate::leanh::lean_dec_ref(v___y_5747_);
    crate::leanh::lean_dec(v___y_5746_);
    crate::leanh::lean_dec_ref(v___y_5745_);
    crate::leanh::lean_dec_ref(v_as_5741_);
    return v_res_5752_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(
    mut v_x_5753_: *mut crate::leanh::LeanObject,
    mut v_x_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5760_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_5753_, v_x_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
    crate::leanh::lean_dec(v___y_5758_);
    crate::leanh::lean_dec_ref(v___y_5757_);
    crate::leanh::lean_dec(v___y_5756_);
    crate::leanh::lean_dec_ref(v___y_5755_);
    return v_res_5760_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(
    mut v_t_5761_: *mut crate::leanh::LeanObject,
    mut v_init_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: u8 = 0;
    v_root_5768_ = crate::leanh::lean_ctor_get(v_t_5761_, 0);
    crate::leanh::lean_inc_ref(v_root_5768_);
    v_tail_5769_ = crate::leanh::lean_ctor_get(v_t_5761_, 1);
    crate::leanh::lean_inc_ref(v_tail_5769_);
    crate::leanh::lean_dec_ref(v_t_5761_);
    v___x_5770_ = lean_array_get_size(v_tail_5769_);
    v___x_5771_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5772_ = lean_nat_dec_lt(v___x_5771_, v___x_5770_);
    if v___x_5772_ == 0 {
        let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_tail_5769_);
        v___x_5773_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_5768_, v_init_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
        return v___x_5773_;
    } else {
        let mut v___x_5774_: usize = 0;
        let mut v___x_5775_: usize = 0;
        let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5774_ = lean_usize_of_nat(v___x_5770_);
        v___x_5775_ = 0usize;
        v___x_5776_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_5769_, v___x_5774_, v___x_5775_, v_init_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
        crate::leanh::lean_dec_ref(v_tail_5769_);
        if crate::leanh::lean_obj_tag(v___x_5776_) == 0 {
            let mut v_a_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5777_ = crate::leanh::lean_ctor_get(v___x_5776_, 0);
            crate::leanh::lean_inc(v_a_5777_);
            crate::leanh::lean_dec_ref_known(v___x_5776_, 1);
            v___x_5778_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_5768_, v_a_5777_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
            return v___x_5778_;
        } else {
            crate::leanh::lean_dec_ref(v_root_5768_);
            return v___x_5776_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(
    mut v_t_5779_: *mut crate::leanh::LeanObject,
    mut v_init_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5786_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_5779_, v_init_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
    crate::leanh::lean_dec(v___y_5784_);
    crate::leanh::lean_dec_ref(v___y_5783_);
    crate::leanh::lean_dec(v___y_5782_);
    crate::leanh::lean_dec_ref(v___y_5781_);
    return v_res_5786_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
    mut v_lctx_5787_: *mut crate::leanh::LeanObject,
    mut v_init_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_5794_ = crate::leanh::lean_ctor_get(v_lctx_5787_, 1);
    crate::leanh::lean_inc_ref(v_decls_5794_);
    crate::leanh::lean_dec_ref(v_lctx_5787_);
    v___x_5795_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_5794_, v_init_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_);
    return v___x_5795_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(
    mut v_lctx_5796_: *mut crate::leanh::LeanObject,
    mut v_init_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5803_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
        v_lctx_5796_,
        v_init_5797_,
        v___y_5798_,
        v___y_5799_,
        v___y_5800_,
        v___y_5801_,
    );
    crate::leanh::lean_dec(v___y_5801_);
    crate::leanh::lean_dec_ref(v___y_5800_);
    crate::leanh::lean_dec(v___y_5799_);
    crate::leanh::lean_dec_ref(v___y_5798_);
    return v_res_5803_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(
    mut v_sz_5804_: usize,
    mut v_i_5805_: usize,
    mut v_bs_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5809_: u8 = 0;
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: usize = 0;
    let mut v___x_5817_: usize = 0;
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5822_: u8 = 0;
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5834_: u8 = 0;
    let mut v_unused_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5809_ = lean_usize_dec_lt(v_i_5805_, v_sz_5804_);
                if v___x_5809_ == 0 {
                    v___x_5810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5810_, 0, v_bs_5806_);
                    return v___x_5810_;
                } else {
                    v_v_5811_ = lean_array_uget(v_bs_5806_, v_i_5805_);
                    v___x_5812_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5813_ = lean_array_uset(v_bs_5806_, v_i_5805_, v___x_5812_);
                    if crate::leanh::lean_obj_tag(v_v_5811_) == 0 {
                        v_a_5815_ = v_v_5811_;
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_5834_ = (!crate::leanh::lean_is_exclusive(v_v_5811_)) as u8;
                        if v_isSharedCheck_5834_ == 0 {
                            v_unused_5835_ = crate::leanh::lean_ctor_get(v_v_5811_, 0);
                            crate::leanh::lean_dec(v_unused_5835_);
                            v___x_5821_ = v_v_5811_;
                            v_isShared_5822_ = v_isSharedCheck_5834_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_v_5811_);
                            v___x_5821_ = crate::leanh::lean_box(0);
                            v_isShared_5822_ = v_isSharedCheck_5834_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5816_ = 1usize;
                v___x_5817_ = lean_usize_add(v_i_5805_, v___x_5816_);
                v___x_5818_ = lean_array_uset(v_bs_x27_5813_, v_i_5805_, v_a_5815_);
                v_i_5805_ = v___x_5817_;
                v_bs_5806_ = v___x_5818_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5823_ = lean_st_ref_take(v___y_5807_);
                v___x_5824_ = l_Lean_instInhabitedLocalDecl_default;
                v___x_5825_ = lean_array_get_size(v___x_5823_);
                v___x_5826_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5827_ = lean_nat_sub(v___x_5825_, v___x_5826_);
                v___x_5828_ = lean_array_get(v___x_5824_, v___x_5823_, v___x_5827_);
                crate::leanh::lean_dec(v___x_5827_);
                v___x_5829_ = lean_array_pop(v___x_5823_);
                v___x_5830_ = lean_st_ref_set(v___y_5807_, v___x_5829_);
                if v_isShared_5822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5821_, 0, v___x_5828_);
                    v___x_5832_ = v___x_5821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5828_);
                    v___x_5832_ = v_reuseFailAlloc_5833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_5815_ = v___x_5832_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(
    mut v_sz_5836_: *mut crate::leanh::LeanObject,
    mut v_i_5837_: *mut crate::leanh::LeanObject,
    mut v_bs_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5841_: usize = 0;
    let mut v_i_boxed_5842_: usize = 0;
    let mut v_res_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5841_ = crate::leanh::lean_unbox_usize(v_sz_5836_);
    crate::leanh::lean_dec(v_sz_5836_);
    v_i_boxed_5842_ = crate::leanh::lean_unbox_usize(v_i_5837_);
    crate::leanh::lean_dec(v_i_5837_);
    v_res_5843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_5841_, v_i_boxed_5842_, v_bs_5838_, v___y_5839_);
    crate::leanh::lean_dec(v___y_5839_);
    return v_res_5843_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(
    mut v_x_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
    mut v___y_5848_: *mut crate::leanh::LeanObject,
    mut v___y_5849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v_sz_5855_: usize = 0;
    let mut v___x_5856_: usize = 0;
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5861_: u8 = 0;
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut v_a_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5872_: u8 = 0;
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_vs_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v_sz_5882_: usize = 0;
    let mut v___x_5883_: usize = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_a_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_isSharedCheck_5904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5844_) == 0 {
                    v_cs_5851_ = crate::leanh::lean_ctor_get(v_x_5844_, 0);
                    v_isSharedCheck_5877_ = (!crate::leanh::lean_is_exclusive(v_x_5844_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v___x_5853_ = v_x_5844_;
                        v_isShared_5854_ = v_isSharedCheck_5877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_5851_);
                        crate::leanh::lean_dec(v_x_5844_);
                        v___x_5853_ = crate::leanh::lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5878_ = crate::leanh::lean_ctor_get(v_x_5844_, 0);
                    v_isSharedCheck_5904_ = (!crate::leanh::lean_is_exclusive(v_x_5844_)) as u8;
                    if v_isSharedCheck_5904_ == 0 {
                        v___x_5880_ = v_x_5844_;
                        v_isShared_5881_ = v_isSharedCheck_5904_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5878_);
                        crate::leanh::lean_dec(v_x_5844_);
                        v___x_5880_ = crate::leanh::lean_box(0);
                        v_isShared_5881_ = v_isSharedCheck_5904_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5855_ = lean_array_size(v_cs_5851_);
                v___x_5856_ = 0usize;
                v___x_5857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_5855_, v___x_5856_, v_cs_5851_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_);
                if crate::leanh::lean_obj_tag(v___x_5857_) == 0 {
                    v_a_5858_ = crate::leanh::lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5868_ = (!crate::leanh::lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5868_ == 0 {
                        v___x_5860_ = v___x_5857_;
                        v_isShared_5861_ = v_isSharedCheck_5868_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5858_);
                        crate::leanh::lean_dec(v___x_5857_);
                        v___x_5860_ = crate::leanh::lean_box(0);
                        v_isShared_5861_ = v_isSharedCheck_5868_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5853_);
                    v_a_5869_ = crate::leanh::lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5876_ = (!crate::leanh::lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5876_ == 0 {
                        v___x_5871_ = v___x_5857_;
                        v_isShared_5872_ = v_isSharedCheck_5876_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5869_);
                        crate::leanh::lean_dec(v___x_5857_);
                        v___x_5871_ = crate::leanh::lean_box(0);
                        v_isShared_5872_ = v_isSharedCheck_5876_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5853_, 0, v_a_5858_);
                    v___x_5863_ = v___x_5853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5858_);
                    v___x_5863_ = v_reuseFailAlloc_5867_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5861_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5860_, 0, v___x_5863_);
                    v___x_5865_ = v___x_5860_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5863_);
                    v___x_5865_ = v_reuseFailAlloc_5866_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5865_;
            }
            5 => {
                if v_isShared_5872_ == 0 {
                    v___x_5874_ = v___x_5871_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
                    v___x_5874_ = v_reuseFailAlloc_5875_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5874_;
            }
            7 => {
                v_sz_5882_ = lean_array_size(v_vs_5878_);
                v___x_5883_ = 0usize;
                v___x_5884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_5882_, v___x_5883_, v_vs_5878_, v___y_5845_);
                if crate::leanh::lean_obj_tag(v___x_5884_) == 0 {
                    v_a_5885_ = crate::leanh::lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5895_ = (!crate::leanh::lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5895_ == 0 {
                        v___x_5887_ = v___x_5884_;
                        v_isShared_5888_ = v_isSharedCheck_5895_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5885_);
                        crate::leanh::lean_dec(v___x_5884_);
                        v___x_5887_ = crate::leanh::lean_box(0);
                        v_isShared_5888_ = v_isSharedCheck_5895_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5880_);
                    v_a_5896_ = crate::leanh::lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5903_ = (!crate::leanh::lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5903_ == 0 {
                        v___x_5898_ = v___x_5884_;
                        v_isShared_5899_ = v_isSharedCheck_5903_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5896_);
                        crate::leanh::lean_dec(v___x_5884_);
                        v___x_5898_ = crate::leanh::lean_box(0);
                        v_isShared_5899_ = v_isSharedCheck_5903_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5880_, 0, v_a_5885_);
                    v___x_5890_ = v___x_5880_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5885_);
                    v___x_5890_ = v_reuseFailAlloc_5894_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5887_, 0, v___x_5890_);
                    v___x_5892_ = v___x_5887_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
                    v___x_5892_ = v_reuseFailAlloc_5893_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5892_;
            }
            11 => {
                if v_isShared_5899_ == 0 {
                    v___x_5901_ = v___x_5898_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
                    v___x_5901_ = v_reuseFailAlloc_5902_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(
    mut v_sz_5905_: usize,
    mut v_i_5906_: usize,
    mut v_bs_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
    mut v___y_5912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5914_: u8 = 0;
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: usize = 0;
    let mut v___x_5922_: usize = 0;
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5928_: u8 = 0;
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5914_ = lean_usize_dec_lt(v_i_5906_, v_sz_5905_);
                if v___x_5914_ == 0 {
                    v___x_5915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5915_, 0, v_bs_5907_);
                    return v___x_5915_;
                } else {
                    v_v_5916_ = lean_array_uget_borrowed(v_bs_5907_, v_i_5906_);
                    crate::leanh::lean_inc(v_v_5916_);
                    v___x_5917_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_5916_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
                    if crate::leanh::lean_obj_tag(v___x_5917_) == 0 {
                        v_a_5918_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                        crate::leanh::lean_inc(v_a_5918_);
                        crate::leanh::lean_dec_ref_known(v___x_5917_, 1);
                        v___x_5919_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5920_ = lean_array_uset(v_bs_5907_, v_i_5906_, v___x_5919_);
                        v___x_5921_ = 1usize;
                        v___x_5922_ = lean_usize_add(v_i_5906_, v___x_5921_);
                        v___x_5923_ = lean_array_uset(v_bs_x27_5920_, v_i_5906_, v_a_5918_);
                        v_i_5906_ = v___x_5922_;
                        v_bs_5907_ = v___x_5923_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5907_);
                        v_a_5925_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                        v_isSharedCheck_5932_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5917_)) as u8;
                        if v_isSharedCheck_5932_ == 0 {
                            v___x_5927_ = v___x_5917_;
                            v_isShared_5928_ = v_isSharedCheck_5932_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5925_);
                            crate::leanh::lean_dec(v___x_5917_);
                            v___x_5927_ = crate::leanh::lean_box(0);
                            v_isShared_5928_ = v_isSharedCheck_5932_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5928_ == 0 {
                    v___x_5930_ = v___x_5927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5925_);
                    v___x_5930_ = v_reuseFailAlloc_5931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(
    mut v_sz_5933_: *mut crate::leanh::LeanObject,
    mut v_i_5934_: *mut crate::leanh::LeanObject,
    mut v_bs_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
    mut v___y_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
    mut v___y_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5942_: usize = 0;
    let mut v_i_boxed_5943_: usize = 0;
    let mut v_res_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5942_ = crate::leanh::lean_unbox_usize(v_sz_5933_);
    crate::leanh::lean_dec(v_sz_5933_);
    v_i_boxed_5943_ = crate::leanh::lean_unbox_usize(v_i_5934_);
    crate::leanh::lean_dec(v_i_5934_);
    v_res_5944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_5942_, v_i_boxed_5943_, v_bs_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
    crate::leanh::lean_dec(v___y_5940_);
    crate::leanh::lean_dec_ref(v___y_5939_);
    crate::leanh::lean_dec(v___y_5938_);
    crate::leanh::lean_dec_ref(v___y_5937_);
    crate::leanh::lean_dec(v___y_5936_);
    return v_res_5944_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(
    mut v_x_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
    mut v___y_5951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5952_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
    crate::leanh::lean_dec(v___y_5950_);
    crate::leanh::lean_dec_ref(v___y_5949_);
    crate::leanh::lean_dec(v___y_5948_);
    crate::leanh::lean_dec_ref(v___y_5947_);
    crate::leanh::lean_dec(v___y_5946_);
    return v_res_5952_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(
    mut v_t_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
    mut v___y_5958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5963_: usize = 0;
    let mut v_tailOff_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5970_: usize = 0;
    let mut v___x_5971_: usize = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5976_: u8 = 0;
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_a_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5995_: u8 = 0;
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5999_: u8 = 0;
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5960_ = crate::leanh::lean_ctor_get(v_t_5953_, 0);
                v_tail_5961_ = crate::leanh::lean_ctor_get(v_t_5953_, 1);
                v_size_5962_ = crate::leanh::lean_ctor_get(v_t_5953_, 2);
                v_shift_5963_ = crate::leanh::lean_ctor_get_usize(v_t_5953_, 4);
                v_tailOff_5964_ = crate::leanh::lean_ctor_get(v_t_5953_, 3);
                v_isSharedCheck_6000_ = (!crate::leanh::lean_is_exclusive(v_t_5953_)) as u8;
                if v_isSharedCheck_6000_ == 0 {
                    v___x_5966_ = v_t_5953_;
                    v_isShared_5967_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_5964_);
                    crate::leanh::lean_inc(v_size_5962_);
                    crate::leanh::lean_inc(v_tail_5961_);
                    crate::leanh::lean_inc(v_root_5960_);
                    crate::leanh::lean_dec(v_t_5953_);
                    v___x_5966_ = crate::leanh::lean_box(0);
                    v_isShared_5967_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5968_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_5960_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_);
                if crate::leanh::lean_obj_tag(v___x_5968_) == 0 {
                    v_a_5969_ = crate::leanh::lean_ctor_get(v___x_5968_, 0);
                    crate::leanh::lean_inc(v_a_5969_);
                    crate::leanh::lean_dec_ref_known(v___x_5968_, 1);
                    v_sz_5970_ = lean_array_size(v_tail_5961_);
                    v___x_5971_ = 0usize;
                    v___x_5972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_5970_, v___x_5971_, v_tail_5961_, v___y_5954_);
                    if crate::leanh::lean_obj_tag(v___x_5972_) == 0 {
                        v_a_5973_ = crate::leanh::lean_ctor_get(v___x_5972_, 0);
                        v_isSharedCheck_5983_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5972_)) as u8;
                        if v_isSharedCheck_5983_ == 0 {
                            v___x_5975_ = v___x_5972_;
                            v_isShared_5976_ = v_isSharedCheck_5983_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5973_);
                            crate::leanh::lean_dec(v___x_5972_);
                            v___x_5975_ = crate::leanh::lean_box(0);
                            v_isShared_5976_ = v_isSharedCheck_5983_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5969_);
                        crate::leanh::lean_del_object(v___x_5966_);
                        crate::leanh::lean_dec(v_tailOff_5964_);
                        crate::leanh::lean_dec(v_size_5962_);
                        v_a_5984_ = crate::leanh::lean_ctor_get(v___x_5972_, 0);
                        v_isSharedCheck_5991_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5972_)) as u8;
                        if v_isSharedCheck_5991_ == 0 {
                            v___x_5986_ = v___x_5972_;
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5984_);
                            crate::leanh::lean_dec(v___x_5972_);
                            v___x_5986_ = crate::leanh::lean_box(0);
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5966_);
                    crate::leanh::lean_dec(v_tailOff_5964_);
                    crate::leanh::lean_dec(v_size_5962_);
                    crate::leanh::lean_dec_ref(v_tail_5961_);
                    v_a_5992_ = crate::leanh::lean_ctor_get(v___x_5968_, 0);
                    v_isSharedCheck_5999_ = (!crate::leanh::lean_is_exclusive(v___x_5968_)) as u8;
                    if v_isSharedCheck_5999_ == 0 {
                        v___x_5994_ = v___x_5968_;
                        v_isShared_5995_ = v_isSharedCheck_5999_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5992_);
                        crate::leanh::lean_dec(v___x_5968_);
                        v___x_5994_ = crate::leanh::lean_box(0);
                        v_isShared_5995_ = v_isSharedCheck_5999_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5966_, 1, v_a_5973_);
                    crate::leanh::lean_ctor_set(v___x_5966_, 0, v_a_5969_);
                    v___x_5978_ = v___x_5966_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5982_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 1, v_a_5973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_size_5962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 3, v_tailOff_5964_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_5982_, 4, v_shift_5963_);
                    v___x_5978_ = v_reuseFailAlloc_5982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5975_, 0, v___x_5978_);
                    v___x_5980_ = v___x_5975_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5978_);
                    v___x_5980_ = v_reuseFailAlloc_5981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5980_;
            }
            5 => {
                if v_isShared_5987_ == 0 {
                    v___x_5989_ = v___x_5986_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
                    v___x_5989_ = v_reuseFailAlloc_5990_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5989_;
            }
            7 => {
                if v_isShared_5995_ == 0 {
                    v___x_5997_ = v___x_5994_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
                    v___x_5997_ = v_reuseFailAlloc_5998_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(
    mut v_t_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(
        v_t_6001_,
        v___y_6002_,
        v___y_6003_,
        v___y_6004_,
        v___y_6005_,
        v___y_6006_,
    );
    crate::leanh::lean_dec(v___y_6006_);
    crate::leanh::lean_dec_ref(v___y_6005_);
    crate::leanh::lean_dec(v___y_6004_);
    crate::leanh::lean_dec_ref(v___y_6003_);
    crate::leanh::lean_dec(v___y_6002_);
    return v_res_6008_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesLCtx(
    mut v_ctx_6009_: *mut crate::leanh::LeanObject,
    mut v_targetUses_6010_: *mut crate::leanh::LeanObject,
    mut v_a_6011_: *mut crate::leanh::LeanObject,
    mut v_a_6012_: *mut crate::leanh::LeanObject,
    mut v_a_6013_: *mut crate::leanh::LeanObject,
    mut v_a_6014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6030_: u8 = 0;
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v_a_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6048_: u8 = 0;
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_6016_ = crate::leanh::lean_ctor_get(v_ctx_6009_, 1);
                crate::leanh::lean_inc_ref(v_decls_6016_);
                v_fvarIdToDecl_6017_ = crate::leanh::lean_ctor_get(v_ctx_6009_, 0);
                crate::leanh::lean_inc_ref(v_fvarIdToDecl_6017_);
                v_auxDeclToFullName_6018_ = crate::leanh::lean_ctor_get(v_ctx_6009_, 2);
                crate::leanh::lean_inc(v_auxDeclToFullName_6018_);
                v_size_6019_ = crate::leanh::lean_ctor_get(v_decls_6016_, 2);
                v_decls_6020_ = lean_mk_empty_array_with_capacity(v_size_6019_);
                v___x_6021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6021_, 0, v_decls_6020_);
                crate::leanh::lean_ctor_set(v___x_6021_, 1, v_targetUses_6010_);
                v___x_6022_ =
                    l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
                        v_ctx_6009_,
                        v___x_6021_,
                        v_a_6011_,
                        v_a_6012_,
                        v_a_6013_,
                        v_a_6014_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6022_) == 0 {
                    v_a_6023_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    crate::leanh::lean_inc(v_a_6023_);
                    crate::leanh::lean_dec_ref_known(v___x_6022_, 1);
                    v_fst_6024_ = crate::leanh::lean_ctor_get(v_a_6023_, 0);
                    crate::leanh::lean_inc(v_fst_6024_);
                    crate::leanh::lean_dec(v_a_6023_);
                    v___x_6025_ = lean_st_mk_ref(v_fst_6024_);
                    v___x_6026_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_6016_, v___x_6025_, v_a_6011_, v_a_6012_, v_a_6013_, v_a_6014_);
                    if crate::leanh::lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = crate::leanh::lean_ctor_get(v___x_6026_, 0);
                        v_isSharedCheck_6036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6036_ == 0 {
                            v___x_6029_ = v___x_6026_;
                            v_isShared_6030_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6027_);
                            crate::leanh::lean_dec(v___x_6026_);
                            v___x_6029_ = crate::leanh::lean_box(0);
                            v_isShared_6030_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6025_);
                        crate::leanh::lean_dec(v_auxDeclToFullName_6018_);
                        crate::leanh::lean_dec_ref(v_fvarIdToDecl_6017_);
                        v_a_6037_ = crate::leanh::lean_ctor_get(v___x_6026_, 0);
                        v_isSharedCheck_6044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6039_ = v___x_6026_;
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6037_);
                            crate::leanh::lean_dec(v___x_6026_);
                            v___x_6039_ = crate::leanh::lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_auxDeclToFullName_6018_);
                    crate::leanh::lean_dec_ref(v_fvarIdToDecl_6017_);
                    crate::leanh::lean_dec_ref(v_decls_6016_);
                    v_a_6045_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    v_isSharedCheck_6052_ = (!crate::leanh::lean_is_exclusive(v___x_6022_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v___x_6047_ = v___x_6022_;
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6045_);
                        crate::leanh::lean_dec(v___x_6022_);
                        v___x_6047_ = crate::leanh::lean_box(0);
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6031_ = lean_st_ref_get(v___x_6025_);
                crate::leanh::lean_dec(v___x_6025_);
                crate::leanh::lean_dec(v___x_6031_);
                v___x_6032_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6032_, 0, v_fvarIdToDecl_6017_);
                crate::leanh::lean_ctor_set(v___x_6032_, 1, v_a_6027_);
                crate::leanh::lean_ctor_set(v___x_6032_, 2, v_auxDeclToFullName_6018_);
                if v_isShared_6030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6029_, 0, v___x_6032_);
                    v___x_6034_ = v___x_6029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6032_);
                    v___x_6034_ = v_reuseFailAlloc_6035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6034_;
            }
            3 => {
                if v_isShared_6040_ == 0 {
                    v___x_6042_ = v___x_6039_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6042_;
            }
            5 => {
                if v_isShared_6048_ == 0 {
                    v___x_6050_ = v___x_6047_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
                    v___x_6050_ = v_reuseFailAlloc_6051_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(
    mut v_ctx_6053_: *mut crate::leanh::LeanObject,
    mut v_targetUses_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
    mut v_a_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(
        v_ctx_6053_,
        v_targetUses_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
    );
    crate::leanh::lean_dec(v_a_6058_);
    crate::leanh::lean_dec_ref(v_a_6057_);
    crate::leanh::lean_dec(v_a_6056_);
    crate::leanh::lean_dec_ref(v_a_6055_);
    return v_res_6060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(
    mut v_sz_6061_: usize,
    mut v_i_6062_: usize,
    mut v_bs_6063_: *mut crate::leanh::LeanObject,
    mut v___y_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_6061_, v_i_6062_, v_bs_6063_, v___y_6064_);
    return v___x_6070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(
    mut v_sz_6071_: *mut crate::leanh::LeanObject,
    mut v_i_6072_: *mut crate::leanh::LeanObject,
    mut v_bs_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6080_: usize = 0;
    let mut v_i_boxed_6081_: usize = 0;
    let mut v_res_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6080_ = crate::leanh::lean_unbox_usize(v_sz_6071_);
    crate::leanh::lean_dec(v_sz_6071_);
    v_i_boxed_6081_ = crate::leanh::lean_unbox_usize(v_i_6072_);
    crate::leanh::lean_dec(v_i_6072_);
    v_res_6082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_6080_, v_i_boxed_6081_, v_bs_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    crate::leanh::lean_dec(v___y_6076_);
    crate::leanh::lean_dec_ref(v___y_6075_);
    crate::leanh::lean_dec(v___y_6074_);
    return v_res_6082_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_doNotDup(
    mut v_u_6083_: u8,
    mut v_rhs_6084_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_6085_: u8,
) -> u8 {
    let mut v___x_6086_: u8 = 0;
    let mut v___x_6087_: u8 = 0;
    v___x_6086_ = 2;
    v___x_6087_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_6083_, v___x_6086_);
    if v___x_6087_ == 0 {
        return v___x_6087_;
    } else {
        if v_elimTrivial_6085_ == 0 {
            return v___x_6087_;
        } else {
            let mut v___x_6088_: u8 = 0;
            v___x_6088_ =
                l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_6084_);
            if v___x_6088_ == 0 {
                return v___x_6087_;
            } else {
                let mut v___x_6089_: u8 = 0;
                v___x_6089_ = 0;
                return v___x_6089_;
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_doNotDup___boxed(
    mut v_u_6090_: *mut crate::leanh::LeanObject,
    mut v_rhs_6091_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_6092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_boxed_6093_: u8 = 0;
    let mut v_elimTrivial_boxed_6094_: u8 = 0;
    let mut v_res_6095_: u8 = 0;
    let mut v_r_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_u_boxed_6093_ = (crate::leanh::lean_unbox(v_u_6090_) as u8);
    v_elimTrivial_boxed_6094_ = (crate::leanh::lean_unbox(v_elimTrivial_6092_) as u8);
    v_res_6095_ =
        l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_6093_, v_rhs_6091_, v_elimTrivial_boxed_6094_);
    crate::leanh::lean_dec_ref(v_rhs_6091_);
    v_r_6096_ = crate::leanh::lean_box((v_res_6095_) as usize);
    return v_r_6096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(
    mut v_elimTrivial_6099_: u8,
    mut v_e_6100_: *mut crate::leanh::LeanObject,
    mut v___y_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
    mut v___y_6103_: *mut crate::leanh::LeanObject,
    mut v___y_6104_: *mut crate::leanh::LeanObject,
    mut v___y_6105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_6100_) == 8 {
        let mut v_type_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_type_6107_ = crate::leanh::lean_ctor_get(v_e_6100_, 1);
        if crate::leanh::lean_obj_tag(v_type_6107_) == 10 {
            let mut v_value_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_data_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_uses_6114_: u8 = 0;
            let mut v___x_6115_: u8 = 0;
            v_value_6108_ = crate::leanh::lean_ctor_get(v_e_6100_, 2);
            v_body_6109_ = crate::leanh::lean_ctor_get(v_e_6100_, 3);
            v_data_6110_ = crate::leanh::lean_ctor_get(v_type_6107_, 0);
            v___x_6111_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
            v___x_6112_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6113_ = l_Lean_KVMap_getNat(v_data_6110_, v___x_6111_, v___x_6112_);
            v_uses_6114_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_6113_);
            crate::leanh::lean_dec(v___x_6113_);
            v___x_6115_ =
                l_Lean_Elab_Tactic_Do_doNotDup(v_uses_6114_, v_value_6108_, v_elimTrivial_6099_);
            if v___x_6115_ == 0 {
                let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6116_ = lean_expr_instantiate1(v_body_6109_, v_value_6108_);
                v___x_6117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6117_, 0, v___x_6116_);
                v___x_6118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6118_, 0, v___x_6117_);
                return v___x_6118_;
            } else {
                let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6119_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
                v___x_6120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6120_, 0, v___x_6119_);
                return v___x_6120_;
            }
        } else {
            let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6121_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
            v___x_6122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6122_, 0, v___x_6121_);
            return v___x_6122_;
        }
    } else {
        let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6123_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
        v___x_6124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6124_, 0, v___x_6123_);
        return v___x_6124_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(
    mut v_elimTrivial_6125_: *mut crate::leanh::LeanObject,
    mut v_e_6126_: *mut crate::leanh::LeanObject,
    mut v___y_6127_: *mut crate::leanh::LeanObject,
    mut v___y_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_6133_: u8 = 0;
    let mut v_res_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_6133_ = (crate::leanh::lean_unbox(v_elimTrivial_6125_) as u8);
    v_res_6134_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(
        v_elimTrivial_boxed_6133_,
        v_e_6126_,
        v___y_6127_,
        v___y_6128_,
        v___y_6129_,
        v___y_6130_,
        v___y_6131_,
    );
    crate::leanh::lean_dec(v___y_6131_);
    crate::leanh::lean_dec_ref(v___y_6130_);
    crate::leanh::lean_dec(v___y_6129_);
    crate::leanh::lean_dec_ref(v___y_6128_);
    crate::leanh::lean_dec(v___y_6127_);
    crate::leanh::lean_dec_ref(v_e_6126_);
    return v_res_6134_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(
    mut v_e_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
    mut v___y_6137_: *mut crate::leanh::LeanObject,
    mut v___y_6138_: *mut crate::leanh::LeanObject,
    mut v___y_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6142_, 0, v_e_6135_);
    v___x_6143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6143_, 0, v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(
    mut v_e_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6151_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(
        v_e_6144_,
        v___y_6145_,
        v___y_6146_,
        v___y_6147_,
        v___y_6148_,
        v___y_6149_,
    );
    crate::leanh::lean_dec(v___y_6149_);
    crate::leanh::lean_dec_ref(v___y_6148_);
    crate::leanh::lean_dec(v___y_6147_);
    crate::leanh::lean_dec_ref(v___y_6146_);
    crate::leanh::lean_dec(v___y_6145_);
    return v_res_6151_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6157_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6158_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6158_, 0, v___x_6157_);
    return v___x_6158_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6159_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
    v___x_6160_ = l_Lean_MessageData_ofFormat(v___x_6159_);
    return v___x_6160_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
    v___x_6162_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2;
    v___x_6163_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6163_, 0, v___x_6162_);
    crate::leanh::lean_ctor_set(v___x_6163_, 1, v___x_6161_);
    return v___x_6163_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(
    mut v_ref_6164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6166_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
    v___x_6167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6167_, 0, v_ref_6164_);
    crate::leanh::lean_ctor_set(v___x_6167_, 1, v___x_6166_);
    v___x_6168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6168_, 0, v___x_6167_);
    return v___x_6168_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(
    mut v_ref_6169_: *mut crate::leanh::LeanObject,
    mut v___y_6170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6171_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_6169_);
    return v_res_6171_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(
    mut v_x_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut v_fileName_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6202_: u8 = 0;
    let mut v_cancelTk_x3f_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6204_: u8 = 0;
    let mut v_inheritedTraceOptions_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: u8 = 0;
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6190_ = crate::leanh::lean_ctor_get(v___y_6177_, 0);
                v_fileMap_6191_ = crate::leanh::lean_ctor_get(v___y_6177_, 1);
                v_options_6192_ = crate::leanh::lean_ctor_get(v___y_6177_, 2);
                v_currRecDepth_6193_ = crate::leanh::lean_ctor_get(v___y_6177_, 3);
                v_maxRecDepth_6194_ = crate::leanh::lean_ctor_get(v___y_6177_, 4);
                v_ref_6195_ = crate::leanh::lean_ctor_get(v___y_6177_, 5);
                v_currNamespace_6196_ = crate::leanh::lean_ctor_get(v___y_6177_, 6);
                v_openDecls_6197_ = crate::leanh::lean_ctor_get(v___y_6177_, 7);
                v_initHeartbeats_6198_ = crate::leanh::lean_ctor_get(v___y_6177_, 8);
                v_maxHeartbeats_6199_ = crate::leanh::lean_ctor_get(v___y_6177_, 9);
                v_quotContext_6200_ = crate::leanh::lean_ctor_get(v___y_6177_, 10);
                v_currMacroScope_6201_ = crate::leanh::lean_ctor_get(v___y_6177_, 11);
                v_diag_6202_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6203_ = crate::leanh::lean_ctor_get(v___y_6177_, 12);
                v_suppressElabErrors_6204_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6205_ = crate::leanh::lean_ctor_get(v___y_6177_, 13);
                v___x_6211_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6212_ = lean_nat_dec_eq(v_maxRecDepth_6194_, v___x_6211_);
                if v___x_6212_ == 0 {
                    v___x_6213_ = lean_nat_dec_eq(v_currRecDepth_6193_, v_maxRecDepth_6194_);
                    if v___x_6213_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6172_);
                        crate::leanh::lean_inc(v_ref_6195_);
                        v___x_6214_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_6195_);
                        v___y_6181_ = v___x_6214_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6181_) == 0 {
                    return v___y_6181_;
                } else {
                    v_a_6182_ = crate::leanh::lean_ctor_get(v___y_6181_, 0);
                    v_isSharedCheck_6189_ = (!crate::leanh::lean_is_exclusive(v___y_6181_)) as u8;
                    if v_isSharedCheck_6189_ == 0 {
                        v___x_6184_ = v___y_6181_;
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6182_);
                        crate::leanh::lean_dec(v___y_6181_);
                        v___x_6184_ = crate::leanh::lean_box(0);
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6185_ == 0 {
                    v___x_6187_ = v___x_6184_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
                    v___x_6187_ = v_reuseFailAlloc_6188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6187_;
            }
            4 => {
                v___x_6207_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6208_ = lean_nat_add(v_currRecDepth_6193_, v___x_6207_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6205_);
                crate::leanh::lean_inc(v_cancelTk_x3f_6203_);
                crate::leanh::lean_inc(v_currMacroScope_6201_);
                crate::leanh::lean_inc(v_quotContext_6200_);
                crate::leanh::lean_inc(v_maxHeartbeats_6199_);
                crate::leanh::lean_inc(v_initHeartbeats_6198_);
                crate::leanh::lean_inc(v_openDecls_6197_);
                crate::leanh::lean_inc(v_currNamespace_6196_);
                crate::leanh::lean_inc(v_ref_6195_);
                crate::leanh::lean_inc(v_maxRecDepth_6194_);
                crate::leanh::lean_inc_ref(v_options_6192_);
                crate::leanh::lean_inc_ref(v_fileMap_6191_);
                crate::leanh::lean_inc_ref(v_fileName_6190_);
                v___x_6209_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_6209_, 0, v_fileName_6190_);
                crate::leanh::lean_ctor_set(v___x_6209_, 1, v_fileMap_6191_);
                crate::leanh::lean_ctor_set(v___x_6209_, 2, v_options_6192_);
                crate::leanh::lean_ctor_set(v___x_6209_, 3, v___x_6208_);
                crate::leanh::lean_ctor_set(v___x_6209_, 4, v_maxRecDepth_6194_);
                crate::leanh::lean_ctor_set(v___x_6209_, 5, v_ref_6195_);
                crate::leanh::lean_ctor_set(v___x_6209_, 6, v_currNamespace_6196_);
                crate::leanh::lean_ctor_set(v___x_6209_, 7, v_openDecls_6197_);
                crate::leanh::lean_ctor_set(v___x_6209_, 8, v_initHeartbeats_6198_);
                crate::leanh::lean_ctor_set(v___x_6209_, 9, v_maxHeartbeats_6199_);
                crate::leanh::lean_ctor_set(v___x_6209_, 10, v_quotContext_6200_);
                crate::leanh::lean_ctor_set(v___x_6209_, 11, v_currMacroScope_6201_);
                crate::leanh::lean_ctor_set(v___x_6209_, 12, v_cancelTk_x3f_6203_);
                crate::leanh::lean_ctor_set(v___x_6209_, 13, v_inheritedTraceOptions_6205_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_6202_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6204_,
                );
                crate::leanh::lean_inc(v___y_6178_);
                crate::leanh::lean_inc(v___y_6176_);
                crate::leanh::lean_inc_ref(v___y_6175_);
                crate::leanh::lean_inc(v___y_6174_);
                crate::leanh::lean_inc(v___y_6173_);
                v___x_6210_ = crate::leanh::lean_apply_7(
                    v_x_6172_,
                    v___y_6173_,
                    v___y_6174_,
                    v___y_6175_,
                    v___y_6176_,
                    v___x_6209_,
                    v___y_6178_,
                    crate::leanh::lean_box(0),
                );
                v___y_6181_ = v___x_6210_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(
    mut v_x_6215_: *mut crate::leanh::LeanObject,
    mut v___y_6216_: *mut crate::leanh::LeanObject,
    mut v___y_6217_: *mut crate::leanh::LeanObject,
    mut v___y_6218_: *mut crate::leanh::LeanObject,
    mut v___y_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
    mut v___y_6222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6223_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_);
    crate::leanh::lean_dec(v___y_6221_);
    crate::leanh::lean_dec_ref(v___y_6220_);
    crate::leanh::lean_dec(v___y_6219_);
    crate::leanh::lean_dec_ref(v___y_6218_);
    crate::leanh::lean_dec(v___y_6217_);
    crate::leanh::lean_dec(v___y_6216_);
    return v_res_6223_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(
    mut v_a_6224_: *mut crate::leanh::LeanObject,
    mut v_x_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: u8 = 0;
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6225_) == 0 {
                    v___x_6226_ = crate::leanh::lean_box(0);
                    return v___x_6226_;
                } else {
                    v_key_6227_ = crate::leanh::lean_ctor_get(v_x_6225_, 0);
                    v_value_6228_ = crate::leanh::lean_ctor_get(v_x_6225_, 1);
                    v_tail_6229_ = crate::leanh::lean_ctor_get(v_x_6225_, 2);
                    v___x_6230_ = l_Lean_ExprStructEq_beq(v_key_6227_, v_a_6224_);
                    if v___x_6230_ == 0 {
                        v_x_6225_ = v_tail_6229_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6228_);
                        v___x_6232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6232_, 0, v_value_6228_);
                        return v___x_6232_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(
    mut v_a_6233_: *mut crate::leanh::LeanObject,
    mut v_x_6234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_6233_, v_x_6234_);
    crate::leanh::lean_dec(v_x_6234_);
    crate::leanh::lean_dec_ref(v_a_6233_);
    return v_res_6235_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(
    mut v_m_6236_: *mut crate::leanh::LeanObject,
    mut v_a_6237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: u64 = 0;
    let mut v___x_6241_: u64 = 0;
    let mut v___x_6242_: u64 = 0;
    let mut v_fold_6243_: u64 = 0;
    let mut v___x_6244_: u64 = 0;
    let mut v___x_6245_: u64 = 0;
    let mut v___x_6246_: u64 = 0;
    let mut v___x_6247_: usize = 0;
    let mut v___x_6248_: usize = 0;
    let mut v___x_6249_: usize = 0;
    let mut v___x_6250_: usize = 0;
    let mut v___x_6251_: usize = 0;
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_6238_ = crate::leanh::lean_ctor_get(v_m_6236_, 1);
    v___x_6239_ = lean_array_get_size(v_buckets_6238_);
    v___x_6240_ = l_Lean_ExprStructEq_hash(v_a_6237_);
    v___x_6241_ = 32u64;
    v___x_6242_ = lean_uint64_shift_right(v___x_6240_, v___x_6241_);
    v_fold_6243_ = lean_uint64_xor(v___x_6240_, v___x_6242_);
    v___x_6244_ = 16u64;
    v___x_6245_ = lean_uint64_shift_right(v_fold_6243_, v___x_6244_);
    v___x_6246_ = lean_uint64_xor(v_fold_6243_, v___x_6245_);
    v___x_6247_ = lean_uint64_to_usize(v___x_6246_);
    v___x_6248_ = lean_usize_of_nat(v___x_6239_);
    v___x_6249_ = 1usize;
    v___x_6250_ = lean_usize_sub(v___x_6248_, v___x_6249_);
    v___x_6251_ = lean_usize_land(v___x_6247_, v___x_6250_);
    v___x_6252_ = lean_array_uget_borrowed(v_buckets_6238_, v___x_6251_);
    v___x_6253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_6237_, v___x_6252_);
    return v___x_6253_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_m_6254_: *mut crate::leanh::LeanObject,
    mut v_a_6255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_6254_, v_a_6255_);
    crate::leanh::lean_dec_ref(v_a_6255_);
    crate::leanh::lean_dec_ref(v_m_6254_);
    return v_res_6256_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(
    mut v_k_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v_b_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
    mut v___y_6264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6264_);
    crate::leanh::lean_inc_ref(v___y_6263_);
    crate::leanh::lean_inc(v___y_6262_);
    crate::leanh::lean_inc_ref(v___y_6261_);
    crate::leanh::lean_inc(v___y_6259_);
    crate::leanh::lean_inc(v___y_6258_);
    v___x_6266_ = crate::leanh::lean_apply_8(
        v_k_6257_,
        v_b_6260_,
        v___y_6258_,
        v___y_6259_,
        v___y_6261_,
        v___y_6262_,
        v___y_6263_,
        v___y_6264_,
        crate::leanh::lean_box(0),
    );
    return v___x_6266_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(
    mut v_k_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v_b_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6276_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_6267_, v___y_6268_, v___y_6269_, v_b_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
    crate::leanh::lean_dec(v___y_6274_);
    crate::leanh::lean_dec_ref(v___y_6273_);
    crate::leanh::lean_dec(v___y_6272_);
    crate::leanh::lean_dec_ref(v___y_6271_);
    crate::leanh::lean_dec(v___y_6269_);
    crate::leanh::lean_dec(v___y_6268_);
    return v_res_6276_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(
    mut v_name_6277_: *mut crate::leanh::LeanObject,
    mut v_type_6278_: *mut crate::leanh::LeanObject,
    mut v_val_6279_: *mut crate::leanh::LeanObject,
    mut v_k_6280_: *mut crate::leanh::LeanObject,
    mut v_nondep_6281_: u8,
    mut v_kind_6282_: u8,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6284_);
                crate::leanh::lean_inc(v___y_6283_);
                v___f_6290_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_6290_, 0, v_k_6280_);
                crate::leanh::lean_closure_set(v___f_6290_, 1, v___y_6283_);
                crate::leanh::lean_closure_set(v___f_6290_, 2, v___y_6284_);
                v___x_6291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_6277_,
                    v_type_6278_,
                    v_val_6279_,
                    v___f_6290_,
                    v_nondep_6281_,
                    v_kind_6282_,
                    v___y_6285_,
                    v___y_6286_,
                    v___y_6287_,
                    v___y_6288_,
                );
                if crate::leanh::lean_obj_tag(v___x_6291_) == 0 {
                    return v___x_6291_;
                } else {
                    v_a_6292_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6299_ = (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6299_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6299_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6292_);
                        crate::leanh::lean_dec(v___x_6291_);
                        v___x_6294_ = crate::leanh::lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6295_ == 0 {
                    v___x_6297_ = v___x_6294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6292_);
                    v___x_6297_ = v_reuseFailAlloc_6298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(
    mut v_name_6300_: *mut crate::leanh::LeanObject,
    mut v_type_6301_: *mut crate::leanh::LeanObject,
    mut v_val_6302_: *mut crate::leanh::LeanObject,
    mut v_k_6303_: *mut crate::leanh::LeanObject,
    mut v_nondep_6304_: *mut crate::leanh::LeanObject,
    mut v_kind_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_6313_: u8 = 0;
    let mut v_kind_boxed_6314_: u8 = 0;
    let mut v_res_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6313_ = (crate::leanh::lean_unbox(v_nondep_6304_) as u8);
    v_kind_boxed_6314_ = (crate::leanh::lean_unbox(v_kind_6305_) as u8);
    v_res_6315_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_6300_, v_type_6301_, v_val_6302_, v_k_6303_, v_nondep_boxed_6313_, v_kind_boxed_6314_, v___y_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_, v___y_6311_);
    crate::leanh::lean_dec(v___y_6311_);
    crate::leanh::lean_dec_ref(v___y_6310_);
    crate::leanh::lean_dec(v___y_6309_);
    crate::leanh::lean_dec_ref(v___y_6308_);
    crate::leanh::lean_dec(v___y_6307_);
    crate::leanh::lean_dec(v___y_6306_);
    return v_res_6315_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_name_6316_: *mut crate::leanh::LeanObject,
    mut v_bi_6317_: u8,
    mut v_type_6318_: *mut crate::leanh::LeanObject,
    mut v_k_6319_: *mut crate::leanh::LeanObject,
    mut v_kind_6320_: u8,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6322_);
                crate::leanh::lean_inc(v___y_6321_);
                v___f_6328_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_6328_, 0, v_k_6319_);
                crate::leanh::lean_closure_set(v___f_6328_, 1, v___y_6321_);
                crate::leanh::lean_closure_set(v___f_6328_, 2, v___y_6322_);
                v___x_6329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_6316_,
                    v_bi_6317_,
                    v_type_6318_,
                    v___f_6328_,
                    v_kind_6320_,
                    v___y_6323_,
                    v___y_6324_,
                    v___y_6325_,
                    v___y_6326_,
                );
                if crate::leanh::lean_obj_tag(v___x_6329_) == 0 {
                    return v___x_6329_;
                } else {
                    v_a_6330_ = crate::leanh::lean_ctor_get(v___x_6329_, 0);
                    v_isSharedCheck_6337_ = (!crate::leanh::lean_is_exclusive(v___x_6329_)) as u8;
                    if v_isSharedCheck_6337_ == 0 {
                        v___x_6332_ = v___x_6329_;
                        v_isShared_6333_ = v_isSharedCheck_6337_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6330_);
                        crate::leanh::lean_dec(v___x_6329_);
                        v___x_6332_ = crate::leanh::lean_box(0);
                        v_isShared_6333_ = v_isSharedCheck_6337_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6333_ == 0 {
                    v___x_6335_ = v___x_6332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_a_6330_);
                    v___x_6335_ = v_reuseFailAlloc_6336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_name_6338_: *mut crate::leanh::LeanObject,
    mut v_bi_6339_: *mut crate::leanh::LeanObject,
    mut v_type_6340_: *mut crate::leanh::LeanObject,
    mut v_k_6341_: *mut crate::leanh::LeanObject,
    mut v_kind_6342_: *mut crate::leanh::LeanObject,
    mut v___y_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
    mut v___y_6347_: *mut crate::leanh::LeanObject,
    mut v___y_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6350_: u8 = 0;
    let mut v_kind_boxed_6351_: u8 = 0;
    let mut v_res_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6350_ = (crate::leanh::lean_unbox(v_bi_6339_) as u8);
    v_kind_boxed_6351_ = (crate::leanh::lean_unbox(v_kind_6342_) as u8);
    v_res_6352_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_6338_, v_bi_boxed_6350_, v_type_6340_, v_k_6341_, v_kind_boxed_6351_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
    crate::leanh::lean_dec(v___y_6348_);
    crate::leanh::lean_dec_ref(v___y_6347_);
    crate::leanh::lean_dec(v___y_6346_);
    crate::leanh::lean_dec_ref(v___y_6345_);
    crate::leanh::lean_dec(v___y_6344_);
    crate::leanh::lean_dec(v___y_6343_);
    return v_res_6352_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(
    mut v___x_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
    mut v___y_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6360_, 0, v___x_6353_);
    return v___x_6360_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(
    mut v___x_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_);
    crate::leanh::lean_dec(v___y_6366_);
    crate::leanh::lean_dec_ref(v___y_6365_);
    crate::leanh::lean_dec(v___y_6364_);
    crate::leanh::lean_dec_ref(v___y_6363_);
    crate::leanh::lean_dec(v___y_6362_);
    return v_res_6368_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(
    mut v_00_u03b1_6369_: *mut crate::leanh::LeanObject,
    mut v_x_6370_: *mut crate::leanh::LeanObject,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
    mut v___y_6372_: *mut crate::leanh::LeanObject,
    mut v___y_6373_: *mut crate::leanh::LeanObject,
    mut v___y_6374_: *mut crate::leanh::LeanObject,
    mut v___y_6375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6377_ = crate::leanh::lean_apply_1(v_x_6370_, crate::leanh::lean_box(0));
    v___x_6378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6378_, 0, v___x_6377_);
    return v___x_6378_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_6379_: *mut crate::leanh::LeanObject,
    mut v_x_6380_: *mut crate::leanh::LeanObject,
    mut v___y_6381_: *mut crate::leanh::LeanObject,
    mut v___y_6382_: *mut crate::leanh::LeanObject,
    mut v___y_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_6379_, v_x_6380_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_, v___y_6385_);
    crate::leanh::lean_dec(v___y_6385_);
    crate::leanh::lean_dec_ref(v___y_6384_);
    crate::leanh::lean_dec(v___y_6383_);
    crate::leanh::lean_dec_ref(v___y_6382_);
    crate::leanh::lean_dec(v___y_6381_);
    return v_res_6387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(
    mut v_x_6388_: *mut crate::leanh::LeanObject,
    mut v_x_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: u64 = 0;
    let mut v___x_6398_: u64 = 0;
    let mut v___x_6399_: u64 = 0;
    let mut v_fold_6400_: u64 = 0;
    let mut v___x_6401_: u64 = 0;
    let mut v___x_6402_: u64 = 0;
    let mut v___x_6403_: u64 = 0;
    let mut v___x_6404_: usize = 0;
    let mut v___x_6405_: usize = 0;
    let mut v___x_6406_: usize = 0;
    let mut v___x_6407_: usize = 0;
    let mut v___x_6408_: usize = 0;
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6389_) == 0 {
                    return v_x_6388_;
                } else {
                    v_key_6390_ = crate::leanh::lean_ctor_get(v_x_6389_, 0);
                    v_value_6391_ = crate::leanh::lean_ctor_get(v_x_6389_, 1);
                    v_tail_6392_ = crate::leanh::lean_ctor_get(v_x_6389_, 2);
                    v_isSharedCheck_6415_ = (!crate::leanh::lean_is_exclusive(v_x_6389_)) as u8;
                    if v_isSharedCheck_6415_ == 0 {
                        v___x_6394_ = v_x_6389_;
                        v_isShared_6395_ = v_isSharedCheck_6415_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6392_);
                        crate::leanh::lean_inc(v_value_6391_);
                        crate::leanh::lean_inc(v_key_6390_);
                        crate::leanh::lean_dec(v_x_6389_);
                        v___x_6394_ = crate::leanh::lean_box(0);
                        v_isShared_6395_ = v_isSharedCheck_6415_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6396_ = lean_array_get_size(v_x_6388_);
                v___x_6397_ = l_Lean_ExprStructEq_hash(v_key_6390_);
                v___x_6398_ = 32u64;
                v___x_6399_ = lean_uint64_shift_right(v___x_6397_, v___x_6398_);
                v_fold_6400_ = lean_uint64_xor(v___x_6397_, v___x_6399_);
                v___x_6401_ = 16u64;
                v___x_6402_ = lean_uint64_shift_right(v_fold_6400_, v___x_6401_);
                v___x_6403_ = lean_uint64_xor(v_fold_6400_, v___x_6402_);
                v___x_6404_ = lean_uint64_to_usize(v___x_6403_);
                v___x_6405_ = lean_usize_of_nat(v___x_6396_);
                v___x_6406_ = 1usize;
                v___x_6407_ = lean_usize_sub(v___x_6405_, v___x_6406_);
                v___x_6408_ = lean_usize_land(v___x_6404_, v___x_6407_);
                v___x_6409_ = lean_array_uget_borrowed(v_x_6388_, v___x_6408_);
                crate::leanh::lean_inc(v___x_6409_);
                if v_isShared_6395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6394_, 2, v___x_6409_);
                    v___x_6411_ = v___x_6394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6414_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_key_6390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 1, v_value_6391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 2, v___x_6409_);
                    v___x_6411_ = v_reuseFailAlloc_6414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6412_ = lean_array_uset(v_x_6388_, v___x_6408_, v___x_6411_);
                v_x_6388_ = v___x_6412_;
                v_x_6389_ = v_tail_6392_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(
    mut v_i_6416_: *mut crate::leanh::LeanObject,
    mut v_source_6417_: *mut crate::leanh::LeanObject,
    mut v_target_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v_es_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6419_ = lean_array_get_size(v_source_6417_);
                v___x_6420_ = lean_nat_dec_lt(v_i_6416_, v___x_6419_);
                if v___x_6420_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_6417_);
                    crate::leanh::lean_dec(v_i_6416_);
                    return v_target_6418_;
                } else {
                    v_es_6421_ = lean_array_fget(v_source_6417_, v_i_6416_);
                    v___x_6422_ = crate::leanh::lean_box(0);
                    v_source_6423_ = lean_array_fset(v_source_6417_, v_i_6416_, v___x_6422_);
                    v_target_6424_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_6418_, v_es_6421_);
                    v___x_6425_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6426_ = lean_nat_add(v_i_6416_, v___x_6425_);
                    crate::leanh::lean_dec(v_i_6416_);
                    v_i_6416_ = v___x_6426_;
                    v_source_6417_ = v_source_6423_;
                    v_target_6418_ = v_target_6424_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(
    mut v_data_6428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6429_ = lean_array_get_size(v_data_6428_);
    v___x_6430_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6431_ = lean_nat_mul(v___x_6429_, v___x_6430_);
    v___x_6432_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6433_ = crate::leanh::lean_box(0);
    v___x_6434_ = lean_mk_array(v_nbuckets_6431_, v___x_6433_);
    v___x_6435_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_6432_, v_data_6428_, v___x_6434_);
    return v___x_6435_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(
    mut v_a_6436_: *mut crate::leanh::LeanObject,
    mut v_b_6437_: *mut crate::leanh::LeanObject,
    mut v_x_6438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6445_: u8 = 0;
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6438_) == 0 {
                    crate::leanh::lean_dec(v_b_6437_);
                    crate::leanh::lean_dec_ref(v_a_6436_);
                    return v_x_6438_;
                } else {
                    v_key_6439_ = crate::leanh::lean_ctor_get(v_x_6438_, 0);
                    v_value_6440_ = crate::leanh::lean_ctor_get(v_x_6438_, 1);
                    v_tail_6441_ = crate::leanh::lean_ctor_get(v_x_6438_, 2);
                    v_isSharedCheck_6453_ = (!crate::leanh::lean_is_exclusive(v_x_6438_)) as u8;
                    if v_isSharedCheck_6453_ == 0 {
                        v___x_6443_ = v_x_6438_;
                        v_isShared_6444_ = v_isSharedCheck_6453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6441_);
                        crate::leanh::lean_inc(v_value_6440_);
                        crate::leanh::lean_inc(v_key_6439_);
                        crate::leanh::lean_dec(v_x_6438_);
                        v___x_6443_ = crate::leanh::lean_box(0);
                        v_isShared_6444_ = v_isSharedCheck_6453_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6445_ = l_Lean_ExprStructEq_beq(v_key_6439_, v_a_6436_);
                if v___x_6445_ == 0 {
                    v___x_6446_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_6436_, v_b_6437_, v_tail_6441_);
                    if v_isShared_6444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6443_, 2, v___x_6446_);
                        v___x_6448_ = v___x_6443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6449_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_key_6439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 1, v_value_6440_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 2, v___x_6446_);
                        v___x_6448_ = v_reuseFailAlloc_6449_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_6440_);
                    crate::leanh::lean_dec(v_key_6439_);
                    if v_isShared_6444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6443_, 1, v_b_6437_);
                        crate::leanh::lean_ctor_set(v___x_6443_, 0, v_a_6436_);
                        v___x_6451_ = v___x_6443_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6452_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_a_6436_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6452_, 1, v_b_6437_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6452_, 2, v_tail_6441_);
                        v___x_6451_ = v_reuseFailAlloc_6452_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6448_;
            }
            3 => {
                return v___x_6451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(
    mut v_a_6454_: *mut crate::leanh::LeanObject,
    mut v_x_6455_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6456_: u8 = 0;
    let mut v_key_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6455_) == 0 {
                    v___x_6456_ = 0;
                    return v___x_6456_;
                } else {
                    v_key_6457_ = crate::leanh::lean_ctor_get(v_x_6455_, 0);
                    v_tail_6458_ = crate::leanh::lean_ctor_get(v_x_6455_, 2);
                    v___x_6459_ = l_Lean_ExprStructEq_beq(v_key_6457_, v_a_6454_);
                    if v___x_6459_ == 0 {
                        v_x_6455_ = v_tail_6458_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6459_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(
    mut v_a_6461_: *mut crate::leanh::LeanObject,
    mut v_x_6462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6463_: u8 = 0;
    let mut v_r_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_6461_, v_x_6462_);
    crate::leanh::lean_dec(v_x_6462_);
    crate::leanh::lean_dec_ref(v_a_6461_);
    v_r_6464_ = crate::leanh::lean_box((v_res_6463_) as usize);
    return v_r_6464_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(
    mut v_m_6465_: *mut crate::leanh::LeanObject,
    mut v_a_6466_: *mut crate::leanh::LeanObject,
    mut v_b_6467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6472_: u8 = 0;
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u64 = 0;
    let mut v___x_6475_: u64 = 0;
    let mut v___x_6476_: u64 = 0;
    let mut v_fold_6477_: u64 = 0;
    let mut v___x_6478_: u64 = 0;
    let mut v___x_6479_: u64 = 0;
    let mut v___x_6480_: u64 = 0;
    let mut v___x_6481_: usize = 0;
    let mut v___x_6482_: usize = 0;
    let mut v___x_6483_: usize = 0;
    let mut v___x_6484_: usize = 0;
    let mut v___x_6485_: usize = 0;
    let mut v_bkt_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: u8 = 0;
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: u8 = 0;
    let mut v_val_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6468_ = crate::leanh::lean_ctor_get(v_m_6465_, 0);
                v_buckets_6469_ = crate::leanh::lean_ctor_get(v_m_6465_, 1);
                v_isSharedCheck_6512_ = (!crate::leanh::lean_is_exclusive(v_m_6465_)) as u8;
                if v_isSharedCheck_6512_ == 0 {
                    v___x_6471_ = v_m_6465_;
                    v_isShared_6472_ = v_isSharedCheck_6512_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_6469_);
                    crate::leanh::lean_inc(v_size_6468_);
                    crate::leanh::lean_dec(v_m_6465_);
                    v___x_6471_ = crate::leanh::lean_box(0);
                    v_isShared_6472_ = v_isSharedCheck_6512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6473_ = lean_array_get_size(v_buckets_6469_);
                v___x_6474_ = l_Lean_ExprStructEq_hash(v_a_6466_);
                v___x_6475_ = 32u64;
                v___x_6476_ = lean_uint64_shift_right(v___x_6474_, v___x_6475_);
                v_fold_6477_ = lean_uint64_xor(v___x_6474_, v___x_6476_);
                v___x_6478_ = 16u64;
                v___x_6479_ = lean_uint64_shift_right(v_fold_6477_, v___x_6478_);
                v___x_6480_ = lean_uint64_xor(v_fold_6477_, v___x_6479_);
                v___x_6481_ = lean_uint64_to_usize(v___x_6480_);
                v___x_6482_ = lean_usize_of_nat(v___x_6473_);
                v___x_6483_ = 1usize;
                v___x_6484_ = lean_usize_sub(v___x_6482_, v___x_6483_);
                v___x_6485_ = lean_usize_land(v___x_6481_, v___x_6484_);
                v_bkt_6486_ = lean_array_uget_borrowed(v_buckets_6469_, v___x_6485_);
                v___x_6487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_6466_, v_bkt_6486_);
                if v___x_6487_ == 0 {
                    v___x_6488_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_6489_ = lean_nat_add(v_size_6468_, v___x_6488_);
                    crate::leanh::lean_dec(v_size_6468_);
                    crate::leanh::lean_inc(v_bkt_6486_);
                    v___x_6490_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6490_, 0, v_a_6466_);
                    crate::leanh::lean_ctor_set(v___x_6490_, 1, v_b_6467_);
                    crate::leanh::lean_ctor_set(v___x_6490_, 2, v_bkt_6486_);
                    v_buckets_x27_6491_ =
                        lean_array_uset(v_buckets_6469_, v___x_6485_, v___x_6490_);
                    v___x_6492_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_6493_ = lean_nat_mul(v_size_x27_6489_, v___x_6492_);
                    v___x_6494_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6495_ = lean_nat_div(v___x_6493_, v___x_6494_);
                    crate::leanh::lean_dec(v___x_6493_);
                    v___x_6496_ = lean_array_get_size(v_buckets_x27_6491_);
                    v___x_6497_ = lean_nat_dec_le(v___x_6495_, v___x_6496_);
                    crate::leanh::lean_dec(v___x_6495_);
                    if v___x_6497_ == 0 {
                        v_val_6498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_6491_);
                        if v_isShared_6472_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6471_, 1, v_val_6498_);
                            crate::leanh::lean_ctor_set(v___x_6471_, 0, v_size_x27_6489_);
                            v___x_6500_ = v___x_6471_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6501_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6501_,
                                0,
                                v_size_x27_6489_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6501_, 1, v_val_6498_);
                            v___x_6500_ = v_reuseFailAlloc_6501_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6472_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6471_, 1, v_buckets_x27_6491_);
                            crate::leanh::lean_ctor_set(v___x_6471_, 0, v_size_x27_6489_);
                            v___x_6503_ = v___x_6471_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6504_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6504_,
                                0,
                                v_size_x27_6489_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6504_,
                                1,
                                v_buckets_x27_6491_,
                            );
                            v___x_6503_ = v_reuseFailAlloc_6504_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_6486_);
                    v___x_6505_ = crate::leanh::lean_box(0);
                    v_buckets_x27_6506_ =
                        lean_array_uset(v_buckets_6469_, v___x_6485_, v___x_6505_);
                    v___x_6507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_6466_, v_b_6467_, v_bkt_6486_);
                    v___x_6508_ = lean_array_uset(v_buckets_x27_6506_, v___x_6485_, v___x_6507_);
                    if v_isShared_6472_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6471_, 1, v___x_6508_);
                        v___x_6510_ = v___x_6471_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_size_6468_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 1, v___x_6508_);
                        v___x_6510_ = v_reuseFailAlloc_6511_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6500_;
            }
            3 => {
                return v___x_6503_;
            }
            4 => {
                return v___x_6510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(
    mut v_a_6513_: *mut crate::leanh::LeanObject,
    mut v_e_6514_: *mut crate::leanh::LeanObject,
    mut v_a_6515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6517_ = lean_st_ref_take(v_a_6513_);
    v___x_6518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_6517_, v_e_6514_, v_a_6515_);
    v___x_6519_ = lean_st_ref_set(v_a_6513_, v___x_6518_);
    v___x_6520_ = crate::leanh::lean_box(0);
    return v___x_6520_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(
    mut v_a_6521_: *mut crate::leanh::LeanObject,
    mut v_e_6522_: *mut crate::leanh::LeanObject,
    mut v_a_6523_: *mut crate::leanh::LeanObject,
    mut v___y_6524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6525_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_6521_, v_e_6522_, v_a_6523_);
    crate::leanh::lean_dec(v_a_6521_);
    return v_res_6525_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(
    mut v_fvars_6529_: *mut crate::leanh::LeanObject,
    mut v_pre_6530_: *mut crate::leanh::LeanObject,
    mut v_post_6531_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6532_: u8,
    mut v_skipConstInApp_6533_: u8,
    mut v_skipInstances_6534_: u8,
    mut v_body_6535_: *mut crate::leanh::LeanObject,
    mut v_x_6536_: *mut crate::leanh::LeanObject,
    mut v___y_6537_: *mut crate::leanh::LeanObject,
    mut v___y_6538_: *mut crate::leanh::LeanObject,
    mut v___y_6539_: *mut crate::leanh::LeanObject,
    mut v___y_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6544_ = lean_array_push(v_fvars_6529_, v_x_6536_);
    v___x_6545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_6530_, v_post_6531_, v_usedLetOnly_6532_, v_skipConstInApp_6533_, v_skipInstances_6534_, v___x_6544_, v_body_6535_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_);
    return v___x_6545_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(
    mut v_fvars_6546_: *mut crate::leanh::LeanObject,
    mut v_pre_6547_: *mut crate::leanh::LeanObject,
    mut v_post_6548_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6549_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_6550_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_6551_: *mut crate::leanh::LeanObject,
    mut v_body_6552_: *mut crate::leanh::LeanObject,
    mut v_x_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
    mut v___y_6556_: *mut crate::leanh::LeanObject,
    mut v___y_6557_: *mut crate::leanh::LeanObject,
    mut v___y_6558_: *mut crate::leanh::LeanObject,
    mut v___y_6559_: *mut crate::leanh::LeanObject,
    mut v___y_6560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6561_: u8 = 0;
    let mut v_skipConstInApp_boxed_6562_: u8 = 0;
    let mut v_skipInstances_boxed_6563_: u8 = 0;
    let mut v_res_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6561_ = (crate::leanh::lean_unbox(v_usedLetOnly_6549_) as u8);
    v_skipConstInApp_boxed_6562_ = (crate::leanh::lean_unbox(v_skipConstInApp_6550_) as u8);
    v_skipInstances_boxed_6563_ = (crate::leanh::lean_unbox(v_skipInstances_6551_) as u8);
    v_res_6564_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_6546_, v_pre_6547_, v_post_6548_, v_usedLetOnly_boxed_6561_, v_skipConstInApp_boxed_6562_, v_skipInstances_boxed_6563_, v_body_6552_, v_x_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
    crate::leanh::lean_dec(v___y_6559_);
    crate::leanh::lean_dec_ref(v___y_6558_);
    crate::leanh::lean_dec(v___y_6557_);
    crate::leanh::lean_dec_ref(v___y_6556_);
    crate::leanh::lean_dec(v___y_6555_);
    crate::leanh::lean_dec(v___y_6554_);
    return v_res_6564_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(
    mut v_pre_6565_: *mut crate::leanh::LeanObject,
    mut v_post_6566_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6567_: u8,
    mut v_skipConstInApp_6568_: u8,
    mut v_skipInstances_6569_: u8,
    mut v_e_6570_: *mut crate::leanh::LeanObject,
    mut v_a_6571_: *mut crate::leanh::LeanObject,
    mut v___y_6572_: *mut crate::leanh::LeanObject,
    mut v___y_6573_: *mut crate::leanh::LeanObject,
    mut v___y_6574_: *mut crate::leanh::LeanObject,
    mut v___y_6575_: *mut crate::leanh::LeanObject,
    mut v___y_6576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6582_: u8 = 0;
    let mut v_e_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6597_: u8 = 0;
    let mut v_a_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6601_: u8 = 0;
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_6566_);
                crate::leanh::lean_inc(v___y_6576_);
                crate::leanh::lean_inc_ref(v___y_6575_);
                crate::leanh::lean_inc(v___y_6574_);
                crate::leanh::lean_inc_ref(v___y_6573_);
                crate::leanh::lean_inc(v___y_6572_);
                crate::leanh::lean_inc_ref(v_e_6570_);
                v___x_6578_ = crate::leanh::lean_apply_7(
                    v_post_6566_,
                    v_e_6570_,
                    v___y_6572_,
                    v___y_6573_,
                    v___y_6574_,
                    v___y_6575_,
                    v___y_6576_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6578_) == 0 {
                    v_a_6579_ = crate::leanh::lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6597_ = (!crate::leanh::lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6597_ == 0 {
                        v___x_6581_ = v___x_6578_;
                        v_isShared_6582_ = v_isSharedCheck_6597_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6579_);
                        crate::leanh::lean_dec(v___x_6578_);
                        v___x_6581_ = crate::leanh::lean_box(0);
                        v_isShared_6582_ = v_isSharedCheck_6597_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6570_);
                    crate::leanh::lean_dec_ref(v_post_6566_);
                    crate::leanh::lean_dec_ref(v_pre_6565_);
                    v_a_6598_ = crate::leanh::lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6605_ = (!crate::leanh::lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6605_ == 0 {
                        v___x_6600_ = v___x_6578_;
                        v_isShared_6601_ = v_isSharedCheck_6605_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6598_);
                        crate::leanh::lean_dec(v___x_6578_);
                        v___x_6600_ = crate::leanh::lean_box(0);
                        v_isShared_6601_ = v_isSharedCheck_6605_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6579_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_6570_);
                    crate::leanh::lean_dec_ref(v_post_6566_);
                    crate::leanh::lean_dec_ref(v_pre_6565_);
                    v_e_6583_ = crate::leanh::lean_ctor_get(v_a_6579_, 0);
                    crate::leanh::lean_inc_ref(v_e_6583_);
                    crate::leanh::lean_dec_ref_known(v_a_6579_, 1);
                    if v_isShared_6582_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6581_, 0, v_e_6583_);
                        v___x_6585_ = v___x_6581_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_e_6583_);
                        v___x_6585_ = v_reuseFailAlloc_6586_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6581_);
                    crate::leanh::lean_dec_ref(v_e_6570_);
                    v_e_6587_ = crate::leanh::lean_ctor_get(v_a_6579_, 0);
                    crate::leanh::lean_inc_ref(v_e_6587_);
                    crate::leanh::lean_dec_ref_known(v_a_6579_, 1);
                    v___x_6588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6565_, v_post_6566_, v_usedLetOnly_6567_, v_skipConstInApp_6568_, v_skipInstances_6569_, v_e_6587_, v_a_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
                    return v___x_6588_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_6566_);
                    crate::leanh::lean_dec_ref(v_pre_6565_);
                    v_e_x3f_6589_ = crate::leanh::lean_ctor_get(v_a_6579_, 0);
                    crate::leanh::lean_inc(v_e_x3f_6589_);
                    crate::leanh::lean_dec_ref_known(v_a_6579_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_6589_) == 0 {
                        if v_isShared_6582_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6581_, 0, v_e_6570_);
                            v___x_6591_ = v___x_6581_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6592_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6592_, 0, v_e_6570_);
                            v___x_6591_ = v_reuseFailAlloc_6592_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6570_);
                        v_val_6593_ = crate::leanh::lean_ctor_get(v_e_x3f_6589_, 0);
                        crate::leanh::lean_inc(v_val_6593_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_6589_, 1);
                        if v_isShared_6582_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6581_, 0, v_val_6593_);
                            v___x_6595_ = v___x_6581_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6596_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6596_, 0, v_val_6593_);
                            v___x_6595_ = v_reuseFailAlloc_6596_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_6585_;
            }
            3 => {
                return v___x_6591_;
            }
            4 => {
                return v___x_6595_;
            }
            5 => {
                if v_isShared_6601_ == 0 {
                    v___x_6603_ = v___x_6600_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_a_6598_);
                    v___x_6603_ = v_reuseFailAlloc_6604_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(
    mut v_pre_6606_: *mut crate::leanh::LeanObject,
    mut v_post_6607_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6608_: u8,
    mut v_skipConstInApp_6609_: u8,
    mut v_skipInstances_6610_: u8,
    mut v_fvars_6611_: *mut crate::leanh::LeanObject,
    mut v_e_6612_: *mut crate::leanh::LeanObject,
    mut v_a_6613_: *mut crate::leanh::LeanObject,
    mut v___y_6614_: *mut crate::leanh::LeanObject,
    mut v___y_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
    mut v___y_6617_: *mut crate::leanh::LeanObject,
    mut v___y_6618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_6612_) == 6 {
        let mut v_binderName_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_6623_: u8 = 0;
        let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_6620_ = crate::leanh::lean_ctor_get(v_e_6612_, 0);
        crate::leanh::lean_inc(v_binderName_6620_);
        v_binderType_6621_ = crate::leanh::lean_ctor_get(v_e_6612_, 1);
        crate::leanh::lean_inc_ref(v_binderType_6621_);
        v_body_6622_ = crate::leanh::lean_ctor_get(v_e_6612_, 2);
        crate::leanh::lean_inc_ref(v_body_6622_);
        v_binderInfo_6623_ = crate::leanh::lean_ctor_get_uint8(
            v_e_6612_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_6612_, 3);
        v___x_6624_ = lean_expr_instantiate_rev(v_binderType_6621_, v_fvars_6611_);
        crate::leanh::lean_dec_ref(v_binderType_6621_);
        crate::leanh::lean_inc_ref(v_post_6607_);
        crate::leanh::lean_inc_ref(v_pre_6606_);
        v___x_6625_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v___x_6624_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
        if crate::leanh::lean_obj_tag(v___x_6625_) == 0 {
            let mut v_a_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6631_: u8 = 0;
            let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6626_ = crate::leanh::lean_ctor_get(v___x_6625_, 0);
            crate::leanh::lean_inc(v_a_6626_);
            crate::leanh::lean_dec_ref_known(v___x_6625_, 1);
            v___x_6627_ = crate::leanh::lean_box((v_usedLetOnly_6608_) as usize);
            v___x_6628_ = crate::leanh::lean_box((v_skipConstInApp_6609_) as usize);
            v___x_6629_ = crate::leanh::lean_box((v_skipInstances_6610_) as usize);
            v___f_6630_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
            crate::leanh::lean_closure_set(v___f_6630_, 0, v_fvars_6611_);
            crate::leanh::lean_closure_set(v___f_6630_, 1, v_pre_6606_);
            crate::leanh::lean_closure_set(v___f_6630_, 2, v_post_6607_);
            crate::leanh::lean_closure_set(v___f_6630_, 3, v___x_6627_);
            crate::leanh::lean_closure_set(v___f_6630_, 4, v___x_6628_);
            crate::leanh::lean_closure_set(v___f_6630_, 5, v___x_6629_);
            crate::leanh::lean_closure_set(v___f_6630_, 6, v_body_6622_);
            v___x_6631_ = 0;
            v___x_6632_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_6620_, v_binderInfo_6623_, v_a_6626_, v___f_6630_, v___x_6631_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
            return v___x_6632_;
        } else {
            crate::leanh::lean_dec_ref(v_body_6622_);
            crate::leanh::lean_dec(v_binderName_6620_);
            crate::leanh::lean_dec_ref(v_fvars_6611_);
            crate::leanh::lean_dec_ref(v_post_6607_);
            crate::leanh::lean_dec_ref(v_pre_6606_);
            return v___x_6625_;
        }
    } else {
        let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6633_ = lean_expr_instantiate_rev(v_e_6612_, v_fvars_6611_);
        crate::leanh::lean_dec_ref(v_e_6612_);
        crate::leanh::lean_inc_ref(v_post_6607_);
        crate::leanh::lean_inc_ref(v_pre_6606_);
        v___x_6634_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v___x_6633_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
        if crate::leanh::lean_obj_tag(v___x_6634_) == 0 {
            let mut v_a_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6636_: u8 = 0;
            let mut v___x_6637_: u8 = 0;
            let mut v___x_6638_: u8 = 0;
            let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6635_ = crate::leanh::lean_ctor_get(v___x_6634_, 0);
            crate::leanh::lean_inc(v_a_6635_);
            crate::leanh::lean_dec_ref_known(v___x_6634_, 1);
            v___x_6636_ = 0;
            v___x_6637_ = 1;
            v___x_6638_ = 1;
            v___x_6639_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_6611_,
                v_a_6635_,
                v___x_6636_,
                v_usedLetOnly_6608_,
                v___x_6636_,
                v___x_6637_,
                v___x_6638_,
                v___y_6615_,
                v___y_6616_,
                v___y_6617_,
                v___y_6618_,
            );
            crate::leanh::lean_dec_ref(v_fvars_6611_);
            if crate::leanh::lean_obj_tag(v___x_6639_) == 0 {
                let mut v_a_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_6640_ = crate::leanh::lean_ctor_get(v___x_6639_, 0);
                crate::leanh::lean_inc(v_a_6640_);
                crate::leanh::lean_dec_ref_known(v___x_6639_, 1);
                v___x_6641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v_a_6640_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
                return v___x_6641_;
            } else {
                crate::leanh::lean_dec_ref(v_post_6607_);
                crate::leanh::lean_dec_ref(v_pre_6606_);
                return v___x_6639_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_6611_);
            crate::leanh::lean_dec_ref(v_post_6607_);
            crate::leanh::lean_dec_ref(v_pre_6606_);
            return v___x_6634_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(
    mut v_fvars_6642_: *mut crate::leanh::LeanObject,
    mut v_pre_6643_: *mut crate::leanh::LeanObject,
    mut v_post_6644_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6645_: u8,
    mut v_skipConstInApp_6646_: u8,
    mut v_skipInstances_6647_: u8,
    mut v_body_6648_: *mut crate::leanh::LeanObject,
    mut v_x_6649_: *mut crate::leanh::LeanObject,
    mut v___y_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6657_ = lean_array_push(v_fvars_6642_, v_x_6649_);
    v___x_6658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_6643_, v_post_6644_, v_usedLetOnly_6645_, v_skipConstInApp_6646_, v_skipInstances_6647_, v___x_6657_, v_body_6648_, v___y_6650_, v___y_6651_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
    return v___x_6658_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(
    mut v_fvars_6659_: *mut crate::leanh::LeanObject,
    mut v_pre_6660_: *mut crate::leanh::LeanObject,
    mut v_post_6661_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6662_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_6663_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_6664_: *mut crate::leanh::LeanObject,
    mut v_body_6665_: *mut crate::leanh::LeanObject,
    mut v_x_6666_: *mut crate::leanh::LeanObject,
    mut v___y_6667_: *mut crate::leanh::LeanObject,
    mut v___y_6668_: *mut crate::leanh::LeanObject,
    mut v___y_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
    mut v___y_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
    mut v___y_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6674_: u8 = 0;
    let mut v_skipConstInApp_boxed_6675_: u8 = 0;
    let mut v_skipInstances_boxed_6676_: u8 = 0;
    let mut v_res_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6674_ = (crate::leanh::lean_unbox(v_usedLetOnly_6662_) as u8);
    v_skipConstInApp_boxed_6675_ = (crate::leanh::lean_unbox(v_skipConstInApp_6663_) as u8);
    v_skipInstances_boxed_6676_ = (crate::leanh::lean_unbox(v_skipInstances_6664_) as u8);
    v_res_6677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_6659_, v_pre_6660_, v_post_6661_, v_usedLetOnly_boxed_6674_, v_skipConstInApp_boxed_6675_, v_skipInstances_boxed_6676_, v_body_6665_, v_x_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
    crate::leanh::lean_dec(v___y_6672_);
    crate::leanh::lean_dec_ref(v___y_6671_);
    crate::leanh::lean_dec(v___y_6670_);
    crate::leanh::lean_dec_ref(v___y_6669_);
    crate::leanh::lean_dec(v___y_6668_);
    crate::leanh::lean_dec(v___y_6667_);
    return v_res_6677_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(
    mut v_pre_6678_: *mut crate::leanh::LeanObject,
    mut v_post_6679_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6680_: u8,
    mut v_skipConstInApp_6681_: u8,
    mut v_skipInstances_6682_: u8,
    mut v_fvars_6683_: *mut crate::leanh::LeanObject,
    mut v_e_6684_: *mut crate::leanh::LeanObject,
    mut v_a_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
    mut v___y_6687_: *mut crate::leanh::LeanObject,
    mut v___y_6688_: *mut crate::leanh::LeanObject,
    mut v___y_6689_: *mut crate::leanh::LeanObject,
    mut v___y_6690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_6684_) == 8 {
        let mut v_declName_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_6696_: u8 = 0;
        let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_6692_ = crate::leanh::lean_ctor_get(v_e_6684_, 0);
        crate::leanh::lean_inc(v_declName_6692_);
        v_type_6693_ = crate::leanh::lean_ctor_get(v_e_6684_, 1);
        crate::leanh::lean_inc_ref(v_type_6693_);
        v_value_6694_ = crate::leanh::lean_ctor_get(v_e_6684_, 2);
        crate::leanh::lean_inc_ref(v_value_6694_);
        v_body_6695_ = crate::leanh::lean_ctor_get(v_e_6684_, 3);
        crate::leanh::lean_inc_ref(v_body_6695_);
        v_nondep_6696_ = crate::leanh::lean_ctor_get_uint8(
            v_e_6684_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_6684_, 4);
        v___x_6697_ = lean_expr_instantiate_rev(v_type_6693_, v_fvars_6683_);
        crate::leanh::lean_dec_ref(v_type_6693_);
        crate::leanh::lean_inc_ref(v_post_6679_);
        crate::leanh::lean_inc_ref(v_pre_6678_);
        v___x_6698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6697_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
        if crate::leanh::lean_obj_tag(v___x_6698_) == 0 {
            let mut v_a_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6699_ = crate::leanh::lean_ctor_get(v___x_6698_, 0);
            crate::leanh::lean_inc(v_a_6699_);
            crate::leanh::lean_dec_ref_known(v___x_6698_, 1);
            v___x_6700_ = lean_expr_instantiate_rev(v_value_6694_, v_fvars_6683_);
            crate::leanh::lean_dec_ref(v_value_6694_);
            crate::leanh::lean_inc_ref(v_post_6679_);
            crate::leanh::lean_inc_ref(v_pre_6678_);
            v___x_6701_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6700_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
            if crate::leanh::lean_obj_tag(v___x_6701_) == 0 {
                let mut v_a_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6707_: u8 = 0;
                let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_6702_ = crate::leanh::lean_ctor_get(v___x_6701_, 0);
                crate::leanh::lean_inc(v_a_6702_);
                crate::leanh::lean_dec_ref_known(v___x_6701_, 1);
                v___x_6703_ = crate::leanh::lean_box((v_usedLetOnly_6680_) as usize);
                v___x_6704_ = crate::leanh::lean_box((v_skipConstInApp_6681_) as usize);
                v___x_6705_ = crate::leanh::lean_box((v_skipInstances_6682_) as usize);
                v___f_6706_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
                crate::leanh::lean_closure_set(v___f_6706_, 0, v_fvars_6683_);
                crate::leanh::lean_closure_set(v___f_6706_, 1, v_pre_6678_);
                crate::leanh::lean_closure_set(v___f_6706_, 2, v_post_6679_);
                crate::leanh::lean_closure_set(v___f_6706_, 3, v___x_6703_);
                crate::leanh::lean_closure_set(v___f_6706_, 4, v___x_6704_);
                crate::leanh::lean_closure_set(v___f_6706_, 5, v___x_6705_);
                crate::leanh::lean_closure_set(v___f_6706_, 6, v_body_6695_);
                v___x_6707_ = 0;
                v___x_6708_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_6692_, v_a_6699_, v_a_6702_, v___f_6706_, v_nondep_6696_, v___x_6707_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
                return v___x_6708_;
            } else {
                crate::leanh::lean_dec(v_a_6699_);
                crate::leanh::lean_dec_ref(v_body_6695_);
                crate::leanh::lean_dec(v_declName_6692_);
                crate::leanh::lean_dec_ref(v_fvars_6683_);
                crate::leanh::lean_dec_ref(v_post_6679_);
                crate::leanh::lean_dec_ref(v_pre_6678_);
                return v___x_6701_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_body_6695_);
            crate::leanh::lean_dec_ref(v_value_6694_);
            crate::leanh::lean_dec(v_declName_6692_);
            crate::leanh::lean_dec_ref(v_fvars_6683_);
            crate::leanh::lean_dec_ref(v_post_6679_);
            crate::leanh::lean_dec_ref(v_pre_6678_);
            return v___x_6698_;
        }
    } else {
        let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6709_ = lean_expr_instantiate_rev(v_e_6684_, v_fvars_6683_);
        crate::leanh::lean_dec_ref(v_e_6684_);
        crate::leanh::lean_inc_ref(v_post_6679_);
        crate::leanh::lean_inc_ref(v_pre_6678_);
        v___x_6710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6709_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
        if crate::leanh::lean_obj_tag(v___x_6710_) == 0 {
            let mut v_a_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6712_: u8 = 0;
            let mut v___x_6713_: u8 = 0;
            let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6711_ = crate::leanh::lean_ctor_get(v___x_6710_, 0);
            crate::leanh::lean_inc(v_a_6711_);
            crate::leanh::lean_dec_ref_known(v___x_6710_, 1);
            v___x_6712_ = 0;
            v___x_6713_ = 1;
            v___x_6714_ = l_Lean_Meta_mkLetFVars(
                v_fvars_6683_,
                v_a_6711_,
                v_usedLetOnly_6680_,
                v___x_6712_,
                v___x_6713_,
                v___y_6687_,
                v___y_6688_,
                v___y_6689_,
                v___y_6690_,
            );
            crate::leanh::lean_dec_ref(v_fvars_6683_);
            if crate::leanh::lean_obj_tag(v___x_6714_) == 0 {
                let mut v_a_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_6715_ = crate::leanh::lean_ctor_get(v___x_6714_, 0);
                crate::leanh::lean_inc(v_a_6715_);
                crate::leanh::lean_dec_ref_known(v___x_6714_, 1);
                v___x_6716_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v_a_6715_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
                return v___x_6716_;
            } else {
                crate::leanh::lean_dec_ref(v_post_6679_);
                crate::leanh::lean_dec_ref(v_pre_6678_);
                return v___x_6714_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_6683_);
            crate::leanh::lean_dec_ref(v_post_6679_);
            crate::leanh::lean_dec_ref(v_pre_6678_);
            return v___x_6710_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6717_ = crate::leanh::lean_box(0);
    v_dummy_6718_ = l_Lean_Expr_sort___override(v___x_6717_);
    return v_dummy_6718_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(
    mut v_pre_6719_: *mut crate::leanh::LeanObject,
    mut v_post_6720_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6721_: u8,
    mut v_skipConstInApp_6722_: u8,
    mut v_skipInstances_6723_: u8,
    mut v_sz_6724_: usize,
    mut v_i_6725_: usize,
    mut v_bs_6726_: *mut crate::leanh::LeanObject,
    mut v___y_6727_: *mut crate::leanh::LeanObject,
    mut v___y_6728_: *mut crate::leanh::LeanObject,
    mut v___y_6729_: *mut crate::leanh::LeanObject,
    mut v___y_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6734_: u8 = 0;
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: usize = 0;
    let mut v___x_6742_: usize = 0;
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6734_ = lean_usize_dec_lt(v_i_6725_, v_sz_6724_);
                if v___x_6734_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_6720_);
                    crate::leanh::lean_dec_ref(v_pre_6719_);
                    v___x_6735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6735_, 0, v_bs_6726_);
                    return v___x_6735_;
                } else {
                    v_v_6736_ = lean_array_uget_borrowed(v_bs_6726_, v_i_6725_);
                    crate::leanh::lean_inc(v_v_6736_);
                    crate::leanh::lean_inc_ref(v_post_6720_);
                    crate::leanh::lean_inc_ref(v_pre_6719_);
                    v___x_6737_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6719_, v_post_6720_, v_usedLetOnly_6721_, v_skipConstInApp_6722_, v_skipInstances_6723_, v_v_6736_, v___y_6727_, v___y_6728_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_);
                    if crate::leanh::lean_obj_tag(v___x_6737_) == 0 {
                        v_a_6738_ = crate::leanh::lean_ctor_get(v___x_6737_, 0);
                        crate::leanh::lean_inc(v_a_6738_);
                        crate::leanh::lean_dec_ref_known(v___x_6737_, 1);
                        v___x_6739_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6740_ = lean_array_uset(v_bs_6726_, v_i_6725_, v___x_6739_);
                        v___x_6741_ = 1usize;
                        v___x_6742_ = lean_usize_add(v_i_6725_, v___x_6741_);
                        v___x_6743_ = lean_array_uset(v_bs_x27_6740_, v_i_6725_, v_a_6738_);
                        v_i_6725_ = v___x_6742_;
                        v_bs_6726_ = v___x_6743_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_6726_);
                        crate::leanh::lean_dec_ref(v_post_6720_);
                        crate::leanh::lean_dec_ref(v_pre_6719_);
                        v_a_6745_ = crate::leanh::lean_ctor_get(v___x_6737_, 0);
                        v_isSharedCheck_6752_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6737_)) as u8;
                        if v_isSharedCheck_6752_ == 0 {
                            v___x_6747_ = v___x_6737_;
                            v_isShared_6748_ = v_isSharedCheck_6752_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6745_);
                            crate::leanh::lean_dec(v___x_6737_);
                            v___x_6747_ = crate::leanh::lean_box(0);
                            v_isShared_6748_ = v_isSharedCheck_6752_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6748_ == 0 {
                    v___x_6750_ = v___x_6747_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_a_6745_);
                    v___x_6750_ = v_reuseFailAlloc_6751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(
    mut v_pre_6753_: *mut crate::leanh::LeanObject,
    mut v_post_6754_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6755_: u8,
    mut v_skipConstInApp_6756_: u8,
    mut v_skipInstances_6757_: u8,
    mut v___x_6758_: *mut crate::leanh::LeanObject,
    mut v___y_6759_: *mut crate::leanh::LeanObject,
    mut v_b_6760_: *mut crate::leanh::LeanObject,
    mut v_a_6761_: *mut crate::leanh::LeanObject,
    mut v___y_6762_: *mut crate::leanh::LeanObject,
    mut v___y_6763_: *mut crate::leanh::LeanObject,
    mut v___y_6764_: *mut crate::leanh::LeanObject,
    mut v___y_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6772_: u8 = 0;
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6778_: u8 = 0;
    let mut v_a_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6753_, v_post_6754_, v_usedLetOnly_6755_, v_skipConstInApp_6756_, v_skipInstances_6757_, v___x_6758_, v___y_6759_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_);
                if crate::leanh::lean_obj_tag(v___x_6768_) == 0 {
                    v_a_6769_ = crate::leanh::lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6778_ = (!crate::leanh::lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6778_ == 0 {
                        v___x_6771_ = v___x_6768_;
                        v_isShared_6772_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6769_);
                        crate::leanh::lean_dec(v___x_6768_);
                        v___x_6771_ = crate::leanh::lean_box(0);
                        v_isShared_6772_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_6760_);
                    v_a_6779_ = crate::leanh::lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6786_ = (!crate::leanh::lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6786_ == 0 {
                        v___x_6781_ = v___x_6768_;
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6779_);
                        crate::leanh::lean_dec(v___x_6768_);
                        v___x_6781_ = crate::leanh::lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6773_ = lean_array_fset(v_b_6760_, v_a_6761_, v_a_6769_);
                v___x_6774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6774_, 0, v___x_6773_);
                if v_isShared_6772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6771_, 0, v___x_6774_);
                    v___x_6776_ = v___x_6771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6777_, 0, v___x_6774_);
                    v___x_6776_ = v_reuseFailAlloc_6777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6776_;
            }
            3 => {
                if v_isShared_6782_ == 0 {
                    v___x_6784_ = v___x_6781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_a_6779_);
                    v___x_6784_ = v_reuseFailAlloc_6785_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(
    mut v_pre_6787_: *mut crate::leanh::LeanObject,
    mut v_post_6788_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6789_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_6790_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_6791_: *mut crate::leanh::LeanObject,
    mut v___x_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v_b_6794_: *mut crate::leanh::LeanObject,
    mut v_a_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
    mut v___y_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6802_: u8 = 0;
    let mut v_skipConstInApp_boxed_6803_: u8 = 0;
    let mut v_skipInstances_boxed_6804_: u8 = 0;
    let mut v_res_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6802_ = (crate::leanh::lean_unbox(v_usedLetOnly_6789_) as u8);
    v_skipConstInApp_boxed_6803_ = (crate::leanh::lean_unbox(v_skipConstInApp_6790_) as u8);
    v_skipInstances_boxed_6804_ = (crate::leanh::lean_unbox(v_skipInstances_6791_) as u8);
    v_res_6805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_6787_, v_post_6788_, v_usedLetOnly_boxed_6802_, v_skipConstInApp_boxed_6803_, v_skipInstances_boxed_6804_, v___x_6792_, v___y_6793_, v_b_6794_, v_a_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_);
    crate::leanh::lean_dec(v___y_6800_);
    crate::leanh::lean_dec_ref(v___y_6799_);
    crate::leanh::lean_dec(v___y_6798_);
    crate::leanh::lean_dec_ref(v___y_6797_);
    crate::leanh::lean_dec(v___y_6796_);
    crate::leanh::lean_dec(v_a_6795_);
    crate::leanh::lean_dec(v___y_6793_);
    return v_res_6805_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(
    mut v_upperBound_6806_: *mut crate::leanh::LeanObject,
    mut v___x_6807_: *mut crate::leanh::LeanObject,
    mut v_pre_6808_: *mut crate::leanh::LeanObject,
    mut v_post_6809_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6810_: u8,
    mut v_skipConstInApp_6811_: u8,
    mut v_skipInstances_6812_: u8,
    mut v_a_6813_: *mut crate::leanh::LeanObject,
    mut v_b_6814_: *mut crate::leanh::LeanObject,
    mut v___y_6815_: *mut crate::leanh::LeanObject,
    mut v___y_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
    mut v___y_6818_: *mut crate::leanh::LeanObject,
    mut v___y_6819_: *mut crate::leanh::LeanObject,
    mut v___y_6820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6828_: u8 = 0;
    let mut v_a_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6837_: u8 = 0;
    let mut v_a_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6841_: u8 = 0;
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_6856_: u8 = 0;
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6846_ = lean_nat_dec_lt(v_a_6813_, v_upperBound_6806_);
                if v___x_6846_ == 0 {
                    crate::leanh::lean_dec(v_a_6813_);
                    crate::leanh::lean_dec_ref(v_post_6809_);
                    crate::leanh::lean_dec_ref(v_pre_6808_);
                    v___x_6847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6847_, 0, v_b_6814_);
                    return v___x_6847_;
                } else {
                    v___x_6848_ = lean_array_fget_borrowed(v_b_6814_, v_a_6813_);
                    v___x_6849_ = lean_array_get_size(v___x_6807_);
                    v___x_6850_ = lean_nat_dec_lt(v_a_6813_, v___x_6849_);
                    if v___x_6850_ == 0 {
                        crate::leanh::lean_inc(v___x_6848_);
                        v___x_6851_ = crate::leanh::lean_box((v_usedLetOnly_6810_) as usize);
                        v___x_6852_ = crate::leanh::lean_box((v_skipConstInApp_6811_) as usize);
                        v___x_6853_ = crate::leanh::lean_box((v_skipInstances_6812_) as usize);
                        crate::leanh::lean_inc(v_a_6813_);
                        crate::leanh::lean_inc(v___y_6815_);
                        crate::leanh::lean_inc_ref(v_post_6809_);
                        crate::leanh::lean_inc_ref(v_pre_6808_);
                        v___f_6854_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                        crate::leanh::lean_closure_set(v___f_6854_, 0, v_pre_6808_);
                        crate::leanh::lean_closure_set(v___f_6854_, 1, v_post_6809_);
                        crate::leanh::lean_closure_set(v___f_6854_, 2, v___x_6851_);
                        crate::leanh::lean_closure_set(v___f_6854_, 3, v___x_6852_);
                        crate::leanh::lean_closure_set(v___f_6854_, 4, v___x_6853_);
                        crate::leanh::lean_closure_set(v___f_6854_, 5, v___x_6848_);
                        crate::leanh::lean_closure_set(v___f_6854_, 6, v___y_6815_);
                        crate::leanh::lean_closure_set(v___f_6854_, 7, v_b_6814_);
                        crate::leanh::lean_closure_set(v___f_6854_, 8, v_a_6813_);
                        v___y_6823_ = v___f_6854_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6855_ = lean_array_fget_borrowed(v___x_6807_, v_a_6813_);
                        v_isInstance_6856_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_6855_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_6856_ == 0 {
                            crate::leanh::lean_inc(v___x_6848_);
                            v___x_6857_ = crate::leanh::lean_box((v_usedLetOnly_6810_) as usize);
                            v___x_6858_ = crate::leanh::lean_box((v_skipConstInApp_6811_) as usize);
                            v___x_6859_ = crate::leanh::lean_box((v_skipInstances_6812_) as usize);
                            crate::leanh::lean_inc(v_a_6813_);
                            crate::leanh::lean_inc(v___y_6815_);
                            crate::leanh::lean_inc_ref(v_post_6809_);
                            crate::leanh::lean_inc_ref(v_pre_6808_);
                            v___f_6860_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                            crate::leanh::lean_closure_set(v___f_6860_, 0, v_pre_6808_);
                            crate::leanh::lean_closure_set(v___f_6860_, 1, v_post_6809_);
                            crate::leanh::lean_closure_set(v___f_6860_, 2, v___x_6857_);
                            crate::leanh::lean_closure_set(v___f_6860_, 3, v___x_6858_);
                            crate::leanh::lean_closure_set(v___f_6860_, 4, v___x_6859_);
                            crate::leanh::lean_closure_set(v___f_6860_, 5, v___x_6848_);
                            crate::leanh::lean_closure_set(v___f_6860_, 6, v___y_6815_);
                            crate::leanh::lean_closure_set(v___f_6860_, 7, v_b_6814_);
                            crate::leanh::lean_closure_set(v___f_6860_, 8, v_a_6813_);
                            v___y_6823_ = v___f_6860_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6861_, 0, v_b_6814_);
                            v___f_6862_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 7, 1);
                            crate::leanh::lean_closure_set(v___f_6862_, 0, v___x_6861_);
                            v___y_6823_ = v___f_6862_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_6820_);
                crate::leanh::lean_inc_ref(v___y_6819_);
                crate::leanh::lean_inc(v___y_6818_);
                crate::leanh::lean_inc_ref(v___y_6817_);
                crate::leanh::lean_inc(v___y_6816_);
                v___x_6824_ = crate::leanh::lean_apply_6(
                    v___y_6823_,
                    v___y_6816_,
                    v___y_6817_,
                    v___y_6818_,
                    v___y_6819_,
                    v___y_6820_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6824_) == 0 {
                    v_a_6825_ = crate::leanh::lean_ctor_get(v___x_6824_, 0);
                    v_isSharedCheck_6837_ = (!crate::leanh::lean_is_exclusive(v___x_6824_)) as u8;
                    if v_isSharedCheck_6837_ == 0 {
                        v___x_6827_ = v___x_6824_;
                        v_isShared_6828_ = v_isSharedCheck_6837_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6825_);
                        crate::leanh::lean_dec(v___x_6824_);
                        v___x_6827_ = crate::leanh::lean_box(0);
                        v_isShared_6828_ = v_isSharedCheck_6837_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6813_);
                    crate::leanh::lean_dec_ref(v_post_6809_);
                    crate::leanh::lean_dec_ref(v_pre_6808_);
                    v_a_6838_ = crate::leanh::lean_ctor_get(v___x_6824_, 0);
                    v_isSharedCheck_6845_ = (!crate::leanh::lean_is_exclusive(v___x_6824_)) as u8;
                    if v_isSharedCheck_6845_ == 0 {
                        v___x_6840_ = v___x_6824_;
                        v_isShared_6841_ = v_isSharedCheck_6845_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6838_);
                        crate::leanh::lean_dec(v___x_6824_);
                        v___x_6840_ = crate::leanh::lean_box(0);
                        v_isShared_6841_ = v_isSharedCheck_6845_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6825_) == 0 {
                    crate::leanh::lean_dec(v_a_6813_);
                    crate::leanh::lean_dec_ref(v_post_6809_);
                    crate::leanh::lean_dec_ref(v_pre_6808_);
                    v_a_6829_ = crate::leanh::lean_ctor_get(v_a_6825_, 0);
                    crate::leanh::lean_inc(v_a_6829_);
                    crate::leanh::lean_dec_ref_known(v_a_6825_, 1);
                    if v_isShared_6828_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6827_, 0, v_a_6829_);
                        v___x_6831_ = v___x_6827_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6829_);
                        v___x_6831_ = v_reuseFailAlloc_6832_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6827_);
                    v_a_6833_ = crate::leanh::lean_ctor_get(v_a_6825_, 0);
                    crate::leanh::lean_inc(v_a_6833_);
                    crate::leanh::lean_dec_ref_known(v_a_6825_, 1);
                    v___x_6834_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6835_ = lean_nat_add(v_a_6813_, v___x_6834_);
                    crate::leanh::lean_dec(v_a_6813_);
                    v_a_6813_ = v___x_6835_;
                    v_b_6814_ = v_a_6833_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_6831_;
            }
            4 => {
                if v_isShared_6841_ == 0 {
                    v___x_6843_ = v___x_6840_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_a_6838_);
                    v___x_6843_ = v_reuseFailAlloc_6844_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(
    mut v_skipInstances_6863_: u8,
    mut v_pre_6864_: *mut crate::leanh::LeanObject,
    mut v_post_6865_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6866_: u8,
    mut v_skipConstInApp_6867_: u8,
    mut v_x_6868_: *mut crate::leanh::LeanObject,
    mut v_x_6869_: *mut crate::leanh::LeanObject,
    mut v_x_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
    mut v___y_6876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6886_: usize = 0;
    let mut v___x_6887_: usize = 0;
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6895_: u8 = 0;
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6899_: u8 = 0;
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6912_: u8 = 0;
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6916_: u8 = 0;
    let mut v_a_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6924_: u8 = 0;
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6868_) == 5 {
                    v_fn_6928_ = crate::leanh::lean_ctor_get(v_x_6868_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6928_);
                    v_arg_6929_ = crate::leanh::lean_ctor_get(v_x_6868_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6929_);
                    crate::leanh::lean_dec_ref_known(v_x_6868_, 2);
                    v___x_6930_ = lean_array_set(v_x_6869_, v_x_6870_, v_arg_6929_);
                    v___x_6931_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6932_ = lean_nat_sub(v_x_6870_, v___x_6931_);
                    crate::leanh::lean_dec(v_x_6870_);
                    v_x_6868_ = v_fn_6928_;
                    v_x_6869_ = v___x_6930_;
                    v_x_6870_ = v___x_6932_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_6870_);
                    if v_skipConstInApp_6867_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_6934_ = l_Lean_Expr_isConst(v_x_6868_);
                        if v___x_6934_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_6879_ = v_x_6868_;
                            v___y_6880_ = v___y_6871_;
                            v___y_6881_ = v___y_6872_;
                            v___y_6882_ = v___y_6873_;
                            v___y_6883_ = v___y_6874_;
                            v___y_6884_ = v___y_6875_;
                            v___y_6885_ = v___y_6876_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_6863_ == 0 {
                    v_sz_6886_ = lean_array_size(v_x_6869_);
                    v___x_6887_ = 0usize;
                    crate::leanh::lean_inc_ref(v_post_6865_);
                    crate::leanh::lean_inc_ref(v_pre_6864_);
                    v___x_6888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v_sz_6886_, v___x_6887_, v_x_6869_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                    if crate::leanh::lean_obj_tag(v___x_6888_) == 0 {
                        v_a_6889_ = crate::leanh::lean_ctor_get(v___x_6888_, 0);
                        crate::leanh::lean_inc(v_a_6889_);
                        crate::leanh::lean_dec_ref_known(v___x_6888_, 1);
                        v___x_6890_ = l_Lean_mkAppN(v_f_6879_, v_a_6889_);
                        crate::leanh::lean_dec(v_a_6889_);
                        v___x_6891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6890_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                        return v___x_6891_;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_6879_);
                        crate::leanh::lean_dec_ref(v_post_6865_);
                        crate::leanh::lean_dec_ref(v_pre_6864_);
                        v_a_6892_ = crate::leanh::lean_ctor_get(v___x_6888_, 0);
                        v_isSharedCheck_6899_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6888_)) as u8;
                        if v_isSharedCheck_6899_ == 0 {
                            v___x_6894_ = v___x_6888_;
                            v_isShared_6895_ = v_isSharedCheck_6899_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6892_);
                            crate::leanh::lean_dec(v___x_6888_);
                            v___x_6894_ = crate::leanh::lean_box(0);
                            v_isShared_6895_ = v_isSharedCheck_6899_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_6900_ = lean_array_get_size(v_x_6869_);
                    crate::leanh::lean_inc_ref(v_f_6879_);
                    v___x_6901_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_6879_,
                        v___x_6900_,
                        v___y_6882_,
                        v___y_6883_,
                        v___y_6884_,
                        v___y_6885_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6901_) == 0 {
                        v_a_6902_ = crate::leanh::lean_ctor_get(v___x_6901_, 0);
                        crate::leanh::lean_inc(v_a_6902_);
                        crate::leanh::lean_dec_ref_known(v___x_6901_, 1);
                        v_paramInfo_6903_ = crate::leanh::lean_ctor_get(v_a_6902_, 0);
                        crate::leanh::lean_inc_ref(v_paramInfo_6903_);
                        crate::leanh::lean_dec(v_a_6902_);
                        v___x_6904_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_post_6865_);
                        crate::leanh::lean_inc_ref(v_pre_6864_);
                        v___x_6905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_6900_, v_paramInfo_6903_, v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6904_, v_x_6869_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                        crate::leanh::lean_dec_ref(v_paramInfo_6903_);
                        if crate::leanh::lean_obj_tag(v___x_6905_) == 0 {
                            v_a_6906_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                            crate::leanh::lean_inc(v_a_6906_);
                            crate::leanh::lean_dec_ref_known(v___x_6905_, 1);
                            v___x_6907_ = l_Lean_mkAppN(v_f_6879_, v_a_6906_);
                            crate::leanh::lean_dec(v_a_6906_);
                            v___x_6908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6907_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                            return v___x_6908_;
                        } else {
                            crate::leanh::lean_dec_ref(v_f_6879_);
                            crate::leanh::lean_dec_ref(v_post_6865_);
                            crate::leanh::lean_dec_ref(v_pre_6864_);
                            v_a_6909_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                            v_isSharedCheck_6916_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6905_)) as u8;
                            if v_isSharedCheck_6916_ == 0 {
                                v___x_6911_ = v___x_6905_;
                                v_isShared_6912_ = v_isSharedCheck_6916_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6909_);
                                crate::leanh::lean_dec(v___x_6905_);
                                v___x_6911_ = crate::leanh::lean_box(0);
                                v_isShared_6912_ = v_isSharedCheck_6916_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_6879_);
                        crate::leanh::lean_dec_ref(v_x_6869_);
                        crate::leanh::lean_dec_ref(v_post_6865_);
                        crate::leanh::lean_dec_ref(v_pre_6864_);
                        v_a_6917_ = crate::leanh::lean_ctor_get(v___x_6901_, 0);
                        v_isSharedCheck_6924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6901_)) as u8;
                        if v_isSharedCheck_6924_ == 0 {
                            v___x_6919_ = v___x_6901_;
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6917_);
                            crate::leanh::lean_dec(v___x_6901_);
                            v___x_6919_ = crate::leanh::lean_box(0);
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_6895_ == 0 {
                    v___x_6897_ = v___x_6894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 0, v_a_6892_);
                    v___x_6897_ = v_reuseFailAlloc_6898_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6897_;
            }
            4 => {
                if v_isShared_6912_ == 0 {
                    v___x_6914_ = v___x_6911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 0, v_a_6909_);
                    v___x_6914_ = v_reuseFailAlloc_6915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6914_;
            }
            6 => {
                if v_isShared_6920_ == 0 {
                    v___x_6922_ = v___x_6919_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6917_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6922_;
            }
            8 => {
                crate::leanh::lean_inc_ref(v_post_6865_);
                crate::leanh::lean_inc_ref(v_pre_6864_);
                v___x_6926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v_x_6868_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                if crate::leanh::lean_obj_tag(v___x_6926_) == 0 {
                    v_a_6927_ = crate::leanh::lean_ctor_get(v___x_6926_, 0);
                    crate::leanh::lean_inc(v_a_6927_);
                    crate::leanh::lean_dec_ref_known(v___x_6926_, 1);
                    v_f_6879_ = v_a_6927_;
                    v___y_6880_ = v___y_6871_;
                    v___y_6881_ = v___y_6872_;
                    v___y_6882_ = v___y_6873_;
                    v___y_6883_ = v___y_6874_;
                    v___y_6884_ = v___y_6875_;
                    v___y_6885_ = v___y_6876_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_6869_);
                    crate::leanh::lean_dec_ref(v_post_6865_);
                    crate::leanh::lean_dec_ref(v_pre_6864_);
                    return v___x_6926_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(
    mut v___x_6935_: *mut crate::leanh::LeanObject,
    mut v_pre_6936_: *mut crate::leanh::LeanObject,
    mut v_e_6937_: *mut crate::leanh::LeanObject,
    mut v_post_6938_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6939_: u8,
    mut v_skipConstInApp_6940_: u8,
    mut v_skipInstances_6941_: u8,
    mut v___y_6942_: *mut crate::leanh::LeanObject,
    mut v___y_6943_: *mut crate::leanh::LeanObject,
    mut v___y_6944_: *mut crate::leanh::LeanObject,
    mut v___y_6945_: *mut crate::leanh::LeanObject,
    mut v___y_6946_: *mut crate::leanh::LeanObject,
    mut v___y_6947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6954_: u8 = 0;
    let mut v___y_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: usize = 0;
    let mut v___x_6974_: usize = 0;
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: usize = 0;
    let mut v___x_6985_: usize = 0;
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_a_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v_a_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7011_: u8 = 0;
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6949_ = l_Lean_Core_checkSystem(v___x_6935_, v___y_6946_, v___y_6947_);
                if crate::leanh::lean_obj_tag(v___x_6949_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6949_, 1);
                    crate::leanh::lean_inc_ref(v_pre_6936_);
                    crate::leanh::lean_inc(v___y_6947_);
                    crate::leanh::lean_inc_ref(v___y_6946_);
                    crate::leanh::lean_inc(v___y_6945_);
                    crate::leanh::lean_inc_ref(v___y_6944_);
                    crate::leanh::lean_inc(v___y_6943_);
                    crate::leanh::lean_inc_ref(v_e_6937_);
                    v___x_6950_ = crate::leanh::lean_apply_7(
                        v_pre_6936_,
                        v_e_6937_,
                        v___y_6943_,
                        v___y_6944_,
                        v___y_6945_,
                        v___y_6946_,
                        v___y_6947_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6950_) == 0 {
                        v_a_6951_ = crate::leanh::lean_ctor_get(v___x_6950_, 0);
                        v_isSharedCheck_6999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6950_)) as u8;
                        if v_isSharedCheck_6999_ == 0 {
                            v___x_6953_ = v___x_6950_;
                            v_isShared_6954_ = v_isSharedCheck_6999_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6951_);
                            crate::leanh::lean_dec(v___x_6950_);
                            v___x_6953_ = crate::leanh::lean_box(0);
                            v_isShared_6954_ = v_isSharedCheck_6999_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_6938_);
                        crate::leanh::lean_dec_ref(v_e_6937_);
                        crate::leanh::lean_dec_ref(v_pre_6936_);
                        v_a_7000_ = crate::leanh::lean_ctor_get(v___x_6950_, 0);
                        v_isSharedCheck_7007_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6950_)) as u8;
                        if v_isSharedCheck_7007_ == 0 {
                            v___x_7002_ = v___x_6950_;
                            v_isShared_7003_ = v_isSharedCheck_7007_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7000_);
                            crate::leanh::lean_dec(v___x_6950_);
                            v___x_7002_ = crate::leanh::lean_box(0);
                            v_isShared_7003_ = v_isSharedCheck_7007_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_6938_);
                    crate::leanh::lean_dec_ref(v_e_6937_);
                    crate::leanh::lean_dec_ref(v_pre_6936_);
                    v_a_7008_ = crate::leanh::lean_ctor_get(v___x_6949_, 0);
                    v_isSharedCheck_7015_ = (!crate::leanh::lean_is_exclusive(v___x_6949_)) as u8;
                    if v_isSharedCheck_7015_ == 0 {
                        v___x_7010_ = v___x_6949_;
                        v_isShared_7011_ = v_isSharedCheck_7015_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7008_);
                        crate::leanh::lean_dec(v___x_6949_);
                        v___x_7010_ = crate::leanh::lean_box(0);
                        v_isShared_7011_ = v_isSharedCheck_7015_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6951_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_6938_);
                    crate::leanh::lean_dec_ref(v_e_6937_);
                    crate::leanh::lean_dec_ref(v_pre_6936_);
                    v_e_6991_ = crate::leanh::lean_ctor_get(v_a_6951_, 0);
                    crate::leanh::lean_inc_ref(v_e_6991_);
                    crate::leanh::lean_dec_ref_known(v_a_6951_, 1);
                    if v_isShared_6954_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6953_, 0, v_e_6991_);
                        v___x_6993_ = v___x_6953_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6994_, 0, v_e_6991_);
                        v___x_6993_ = v_reuseFailAlloc_6994_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6953_);
                    crate::leanh::lean_dec_ref(v_e_6937_);
                    v_e_6995_ = crate::leanh::lean_ctor_get(v_a_6951_, 0);
                    crate::leanh::lean_inc_ref(v_e_6995_);
                    crate::leanh::lean_dec_ref_known(v_a_6951_, 1);
                    v___x_6996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_e_6995_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6996_;
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_6953_);
                    v_e_x3f_6997_ = crate::leanh::lean_ctor_get(v_a_6951_, 0);
                    crate::leanh::lean_inc(v_e_x3f_6997_);
                    crate::leanh::lean_dec_ref_known(v_a_6951_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_6997_) == 0 {
                        v___y_6956_ = v_e_6937_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6937_);
                        v_val_6998_ = crate::leanh::lean_ctor_get(v_e_x3f_6997_, 0);
                        crate::leanh::lean_inc(v_val_6998_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_6997_, 1);
                        v___y_6956_ = v_val_6998_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match crate::leanh::lean_obj_tag(v___y_6956_) {
                7 => {
                    v___x_6957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0;
                    v___x_6958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6957_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6958_;
                }
                6 => {
                    v___x_6959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0;
                    v___x_6960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6959_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6960_;
                }
                8 => {
                    v___x_6961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0;
                    v___x_6962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6961_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6962_;
                }
                5 => {
                    v_dummy_6963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once), _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
                    v_nargs_6964_ = l_Lean_Expr_getAppNumArgs(v___y_6956_);
                    crate::leanh::lean_inc(v_nargs_6964_);
                    v___x_6965_ = lean_mk_array(v_nargs_6964_, v_dummy_6963_);
                    v___x_6966_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6967_ = lean_nat_sub(v_nargs_6964_, v___x_6966_);
                    crate::leanh::lean_dec(v_nargs_6964_);
                    v___x_6968_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_6941_, v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v___y_6956_, v___x_6965_, v___x_6967_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6968_;
                }
                10 => {
                    v_data_6969_ = crate::leanh::lean_ctor_get(v___y_6956_, 0);
                    v_expr_6970_ = crate::leanh::lean_ctor_get(v___y_6956_, 1);
                    crate::leanh::lean_inc_ref(v_expr_6970_);
                    crate::leanh::lean_inc_ref(v_post_6938_);
                    crate::leanh::lean_inc_ref(v_pre_6936_);
                    v___x_6971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_expr_6970_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    if crate::leanh::lean_obj_tag(v___x_6971_) == 0 {
                        v_a_6972_ = crate::leanh::lean_ctor_get(v___x_6971_, 0);
                        crate::leanh::lean_inc(v_a_6972_);
                        crate::leanh::lean_dec_ref_known(v___x_6971_, 1);
                        v___x_6973_ = lean_ptr_addr(v_expr_6970_);
                        v___x_6974_ = lean_ptr_addr(v_a_6972_);
                        v___x_6975_ = lean_usize_dec_eq(v___x_6973_, v___x_6974_);
                        if v___x_6975_ == 0 {
                            crate::leanh::lean_inc(v_data_6969_);
                            crate::leanh::lean_dec_ref_known(v___y_6956_, 2);
                            v___x_6976_ = l_Lean_Expr_mdata___override(v_data_6969_, v_a_6972_);
                            v___x_6977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6976_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6977_;
                        } else {
                            crate::leanh::lean_dec(v_a_6972_);
                            v___x_6978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6978_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6956_, 2);
                        crate::leanh::lean_dec_ref(v_post_6938_);
                        crate::leanh::lean_dec_ref(v_pre_6936_);
                        return v___x_6971_;
                    }
                }
                11 => {
                    v_typeName_6979_ = crate::leanh::lean_ctor_get(v___y_6956_, 0);
                    v_idx_6980_ = crate::leanh::lean_ctor_get(v___y_6956_, 1);
                    v_struct_6981_ = crate::leanh::lean_ctor_get(v___y_6956_, 2);
                    crate::leanh::lean_inc_ref(v_struct_6981_);
                    crate::leanh::lean_inc_ref(v_post_6938_);
                    crate::leanh::lean_inc_ref(v_pre_6936_);
                    v___x_6982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_struct_6981_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    if crate::leanh::lean_obj_tag(v___x_6982_) == 0 {
                        v_a_6983_ = crate::leanh::lean_ctor_get(v___x_6982_, 0);
                        crate::leanh::lean_inc(v_a_6983_);
                        crate::leanh::lean_dec_ref_known(v___x_6982_, 1);
                        v___x_6984_ = lean_ptr_addr(v_struct_6981_);
                        v___x_6985_ = lean_ptr_addr(v_a_6983_);
                        v___x_6986_ = lean_usize_dec_eq(v___x_6984_, v___x_6985_);
                        if v___x_6986_ == 0 {
                            crate::leanh::lean_inc(v_idx_6980_);
                            crate::leanh::lean_inc(v_typeName_6979_);
                            crate::leanh::lean_dec_ref_known(v___y_6956_, 3);
                            v___x_6987_ = l_Lean_Expr_proj___override(
                                v_typeName_6979_,
                                v_idx_6980_,
                                v_a_6983_,
                            );
                            v___x_6988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6987_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6988_;
                        } else {
                            crate::leanh::lean_dec(v_a_6983_);
                            v___x_6989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6989_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6956_, 3);
                        crate::leanh::lean_dec_ref(v_post_6938_);
                        crate::leanh::lean_dec_ref(v_pre_6936_);
                        return v___x_6982_;
                    }
                }
                _ => {
                    v___x_6990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6990_;
                }
            },
            3 => {
                return v___x_6993_;
            }
            4 => {
                if v_isShared_7003_ == 0 {
                    v___x_7005_ = v___x_7002_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_a_7000_);
                    v___x_7005_ = v_reuseFailAlloc_7006_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7005_;
            }
            6 => {
                if v_isShared_7011_ == 0 {
                    v___x_7013_ = v___x_7010_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_a_7008_);
                    v___x_7013_ = v_reuseFailAlloc_7014_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(
    mut v___x_7016_: *mut crate::leanh::LeanObject,
    mut v_pre_7017_: *mut crate::leanh::LeanObject,
    mut v_e_7018_: *mut crate::leanh::LeanObject,
    mut v_post_7019_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7020_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7021_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7022_: *mut crate::leanh::LeanObject,
    mut v___y_7023_: *mut crate::leanh::LeanObject,
    mut v___y_7024_: *mut crate::leanh::LeanObject,
    mut v___y_7025_: *mut crate::leanh::LeanObject,
    mut v___y_7026_: *mut crate::leanh::LeanObject,
    mut v___y_7027_: *mut crate::leanh::LeanObject,
    mut v___y_7028_: *mut crate::leanh::LeanObject,
    mut v___y_7029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7030_: u8 = 0;
    let mut v_skipConstInApp_boxed_7031_: u8 = 0;
    let mut v_skipInstances_boxed_7032_: u8 = 0;
    let mut v_res_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7030_ = (crate::leanh::lean_unbox(v_usedLetOnly_7020_) as u8);
    v_skipConstInApp_boxed_7031_ = (crate::leanh::lean_unbox(v_skipConstInApp_7021_) as u8);
    v_skipInstances_boxed_7032_ = (crate::leanh::lean_unbox(v_skipInstances_7022_) as u8);
    v_res_7033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_7016_, v_pre_7017_, v_e_7018_, v_post_7019_, v_usedLetOnly_boxed_7030_, v_skipConstInApp_boxed_7031_, v_skipInstances_boxed_7032_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_);
    crate::leanh::lean_dec(v___y_7028_);
    crate::leanh::lean_dec_ref(v___y_7027_);
    crate::leanh::lean_dec(v___y_7026_);
    crate::leanh::lean_dec_ref(v___y_7025_);
    crate::leanh::lean_dec(v___y_7024_);
    crate::leanh::lean_dec(v___y_7023_);
    return v_res_7033_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(
    mut v_pre_7034_: *mut crate::leanh::LeanObject,
    mut v_post_7035_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7036_: u8,
    mut v_skipConstInApp_7037_: u8,
    mut v_skipInstances_7038_: u8,
    mut v_e_7039_: *mut crate::leanh::LeanObject,
    mut v_a_7040_: *mut crate::leanh::LeanObject,
    mut v___y_7041_: *mut crate::leanh::LeanObject,
    mut v___y_7042_: *mut crate::leanh::LeanObject,
    mut v___y_7043_: *mut crate::leanh::LeanObject,
    mut v___y_7044_: *mut crate::leanh::LeanObject,
    mut v___y_7045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7052_: u8 = 0;
    let mut v___x_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7065_: u8 = 0;
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7069_: u8 = 0;
    let mut v_unused_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7074_: u8 = 0;
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut v_val_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut v_a_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7087_: u8 = 0;
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_7040_);
                v___x_7047_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_7047_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7047_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7047_, 2, v_a_7040_);
                v___x_7048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7047_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                if crate::leanh::lean_obj_tag(v___x_7048_) == 0 {
                    v_a_7049_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                    v_isSharedCheck_7083_ = (!crate::leanh::lean_is_exclusive(v___x_7048_)) as u8;
                    if v_isSharedCheck_7083_ == 0 {
                        v___x_7051_ = v___x_7048_;
                        v_isShared_7052_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7049_);
                        crate::leanh::lean_dec(v___x_7048_);
                        v___x_7051_ = crate::leanh::lean_box(0);
                        v_isShared_7052_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7039_);
                    crate::leanh::lean_dec_ref(v_post_7035_);
                    crate::leanh::lean_dec_ref(v_pre_7034_);
                    v_a_7084_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                    v_isSharedCheck_7091_ = (!crate::leanh::lean_is_exclusive(v___x_7048_)) as u8;
                    if v_isSharedCheck_7091_ == 0 {
                        v___x_7086_ = v___x_7048_;
                        v_isShared_7087_ = v_isSharedCheck_7091_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7084_);
                        crate::leanh::lean_dec(v___x_7048_);
                        v___x_7086_ = crate::leanh::lean_box(0);
                        v_isShared_7087_ = v_isSharedCheck_7091_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_7049_, v_e_7039_);
                crate::leanh::lean_dec(v_a_7049_);
                if crate::leanh::lean_obj_tag(v___x_7053_) == 0 {
                    crate::leanh::lean_del_object(v___x_7051_);
                    v___x_7054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0;
                    v___x_7055_ = crate::leanh::lean_box((v_usedLetOnly_7036_) as usize);
                    v___x_7056_ = crate::leanh::lean_box((v_skipConstInApp_7037_) as usize);
                    v___x_7057_ = crate::leanh::lean_box((v_skipInstances_7038_) as usize);
                    crate::leanh::lean_inc_ref(v_e_7039_);
                    v___f_7058_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
                    crate::leanh::lean_closure_set(v___f_7058_, 0, v___x_7054_);
                    crate::leanh::lean_closure_set(v___f_7058_, 1, v_pre_7034_);
                    crate::leanh::lean_closure_set(v___f_7058_, 2, v_e_7039_);
                    crate::leanh::lean_closure_set(v___f_7058_, 3, v_post_7035_);
                    crate::leanh::lean_closure_set(v___f_7058_, 4, v___x_7055_);
                    crate::leanh::lean_closure_set(v___f_7058_, 5, v___x_7056_);
                    crate::leanh::lean_closure_set(v___f_7058_, 6, v___x_7057_);
                    v___x_7059_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_7058_, v_a_7040_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                    if crate::leanh::lean_obj_tag(v___x_7059_) == 0 {
                        v_a_7060_ = crate::leanh::lean_ctor_get(v___x_7059_, 0);
                        crate::leanh::lean_inc_n(v_a_7060_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_7059_, 1);
                        crate::leanh::lean_inc(v_a_7040_);
                        v___f_7061_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_7061_, 0, v_a_7040_);
                        crate::leanh::lean_closure_set(v___f_7061_, 1, v_e_7039_);
                        crate::leanh::lean_closure_set(v___f_7061_, 2, v_a_7060_);
                        v___x_7062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_7061_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                        if crate::leanh::lean_obj_tag(v___x_7062_) == 0 {
                            v_isSharedCheck_7069_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7062_)) as u8;
                            if v_isSharedCheck_7069_ == 0 {
                                v_unused_7070_ = crate::leanh::lean_ctor_get(v___x_7062_, 0);
                                crate::leanh::lean_dec(v_unused_7070_);
                                v___x_7064_ = v___x_7062_;
                                v_isShared_7065_ = v_isSharedCheck_7069_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7062_);
                                v___x_7064_ = crate::leanh::lean_box(0);
                                v_isShared_7065_ = v_isSharedCheck_7069_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7060_);
                            v_a_7071_ = crate::leanh::lean_ctor_get(v___x_7062_, 0);
                            v_isSharedCheck_7078_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7062_)) as u8;
                            if v_isSharedCheck_7078_ == 0 {
                                v___x_7073_ = v___x_7062_;
                                v_isShared_7074_ = v_isSharedCheck_7078_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7071_);
                                crate::leanh::lean_dec(v___x_7062_);
                                v___x_7073_ = crate::leanh::lean_box(0);
                                v_isShared_7074_ = v_isSharedCheck_7078_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7039_);
                        return v___x_7059_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7039_);
                    crate::leanh::lean_dec_ref(v_post_7035_);
                    crate::leanh::lean_dec_ref(v_pre_7034_);
                    v_val_7079_ = crate::leanh::lean_ctor_get(v___x_7053_, 0);
                    crate::leanh::lean_inc(v_val_7079_);
                    crate::leanh::lean_dec_ref_known(v___x_7053_, 1);
                    if v_isShared_7052_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7051_, 0, v_val_7079_);
                        v___x_7081_ = v___x_7051_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_val_7079_);
                        v___x_7081_ = v_reuseFailAlloc_7082_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7064_, 0, v_a_7060_);
                    v___x_7067_ = v___x_7064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7068_, 0, v_a_7060_);
                    v___x_7067_ = v_reuseFailAlloc_7068_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7067_;
            }
            4 => {
                if v_isShared_7074_ == 0 {
                    v___x_7076_ = v___x_7073_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_a_7071_);
                    v___x_7076_ = v_reuseFailAlloc_7077_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7076_;
            }
            6 => {
                return v___x_7081_;
            }
            7 => {
                if v_isShared_7087_ == 0 {
                    v___x_7089_ = v___x_7086_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 0, v_a_7084_);
                    v___x_7089_ = v_reuseFailAlloc_7090_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(
    mut v_fvars_7092_: *mut crate::leanh::LeanObject,
    mut v_pre_7093_: *mut crate::leanh::LeanObject,
    mut v_post_7094_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7095_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7096_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7097_: *mut crate::leanh::LeanObject,
    mut v_body_7098_: *mut crate::leanh::LeanObject,
    mut v_x_7099_: *mut crate::leanh::LeanObject,
    mut v___y_7100_: *mut crate::leanh::LeanObject,
    mut v___y_7101_: *mut crate::leanh::LeanObject,
    mut v___y_7102_: *mut crate::leanh::LeanObject,
    mut v___y_7103_: *mut crate::leanh::LeanObject,
    mut v___y_7104_: *mut crate::leanh::LeanObject,
    mut v___y_7105_: *mut crate::leanh::LeanObject,
    mut v___y_7106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7107_: u8 = 0;
    let mut v_skipConstInApp_boxed_7108_: u8 = 0;
    let mut v_skipInstances_boxed_7109_: u8 = 0;
    let mut v_res_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7107_ = (crate::leanh::lean_unbox(v_usedLetOnly_7095_) as u8);
    v_skipConstInApp_boxed_7108_ = (crate::leanh::lean_unbox(v_skipConstInApp_7096_) as u8);
    v_skipInstances_boxed_7109_ = (crate::leanh::lean_unbox(v_skipInstances_7097_) as u8);
    v_res_7110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_7092_, v_pre_7093_, v_post_7094_, v_usedLetOnly_boxed_7107_, v_skipConstInApp_boxed_7108_, v_skipInstances_boxed_7109_, v_body_7098_, v_x_7099_, v___y_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_, v___y_7105_);
    crate::leanh::lean_dec(v___y_7105_);
    crate::leanh::lean_dec_ref(v___y_7104_);
    crate::leanh::lean_dec(v___y_7103_);
    crate::leanh::lean_dec_ref(v___y_7102_);
    crate::leanh::lean_dec(v___y_7101_);
    crate::leanh::lean_dec(v___y_7100_);
    return v_res_7110_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(
    mut v_pre_7111_: *mut crate::leanh::LeanObject,
    mut v_post_7112_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7113_: u8,
    mut v_skipConstInApp_7114_: u8,
    mut v_skipInstances_7115_: u8,
    mut v_fvars_7116_: *mut crate::leanh::LeanObject,
    mut v_e_7117_: *mut crate::leanh::LeanObject,
    mut v_a_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
    mut v___y_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_7117_) == 7 {
        let mut v_binderName_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7128_: u8 = 0;
        let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7125_ = crate::leanh::lean_ctor_get(v_e_7117_, 0);
        crate::leanh::lean_inc(v_binderName_7125_);
        v_binderType_7126_ = crate::leanh::lean_ctor_get(v_e_7117_, 1);
        crate::leanh::lean_inc_ref(v_binderType_7126_);
        v_body_7127_ = crate::leanh::lean_ctor_get(v_e_7117_, 2);
        crate::leanh::lean_inc_ref(v_body_7127_);
        v_binderInfo_7128_ = crate::leanh::lean_ctor_get_uint8(
            v_e_7117_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_7117_, 3);
        v___x_7129_ = lean_expr_instantiate_rev(v_binderType_7126_, v_fvars_7116_);
        crate::leanh::lean_dec_ref(v_binderType_7126_);
        crate::leanh::lean_inc_ref(v_post_7112_);
        crate::leanh::lean_inc_ref(v_pre_7111_);
        v___x_7130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v___x_7129_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
        if crate::leanh::lean_obj_tag(v___x_7130_) == 0 {
            let mut v_a_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7136_: u8 = 0;
            let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7131_ = crate::leanh::lean_ctor_get(v___x_7130_, 0);
            crate::leanh::lean_inc(v_a_7131_);
            crate::leanh::lean_dec_ref_known(v___x_7130_, 1);
            v___x_7132_ = crate::leanh::lean_box((v_usedLetOnly_7113_) as usize);
            v___x_7133_ = crate::leanh::lean_box((v_skipConstInApp_7114_) as usize);
            v___x_7134_ = crate::leanh::lean_box((v_skipInstances_7115_) as usize);
            v___f_7135_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
            crate::leanh::lean_closure_set(v___f_7135_, 0, v_fvars_7116_);
            crate::leanh::lean_closure_set(v___f_7135_, 1, v_pre_7111_);
            crate::leanh::lean_closure_set(v___f_7135_, 2, v_post_7112_);
            crate::leanh::lean_closure_set(v___f_7135_, 3, v___x_7132_);
            crate::leanh::lean_closure_set(v___f_7135_, 4, v___x_7133_);
            crate::leanh::lean_closure_set(v___f_7135_, 5, v___x_7134_);
            crate::leanh::lean_closure_set(v___f_7135_, 6, v_body_7127_);
            v___x_7136_ = 0;
            v___x_7137_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_7125_, v_binderInfo_7128_, v_a_7131_, v___f_7135_, v___x_7136_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
            return v___x_7137_;
        } else {
            crate::leanh::lean_dec_ref(v_body_7127_);
            crate::leanh::lean_dec(v_binderName_7125_);
            crate::leanh::lean_dec_ref(v_fvars_7116_);
            crate::leanh::lean_dec_ref(v_post_7112_);
            crate::leanh::lean_dec_ref(v_pre_7111_);
            return v___x_7130_;
        }
    } else {
        let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7138_ = lean_expr_instantiate_rev(v_e_7117_, v_fvars_7116_);
        crate::leanh::lean_dec_ref(v_e_7117_);
        crate::leanh::lean_inc_ref(v_post_7112_);
        crate::leanh::lean_inc_ref(v_pre_7111_);
        v___x_7139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v___x_7138_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
        if crate::leanh::lean_obj_tag(v___x_7139_) == 0 {
            let mut v_a_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7141_: u8 = 0;
            let mut v___x_7142_: u8 = 0;
            let mut v___x_7143_: u8 = 0;
            let mut v___x_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7140_ = crate::leanh::lean_ctor_get(v___x_7139_, 0);
            crate::leanh::lean_inc(v_a_7140_);
            crate::leanh::lean_dec_ref_known(v___x_7139_, 1);
            v___x_7141_ = 0;
            v___x_7142_ = 1;
            v___x_7143_ = 1;
            v___x_7144_ = l_Lean_Meta_mkForallFVars(
                v_fvars_7116_,
                v_a_7140_,
                v___x_7141_,
                v_usedLetOnly_7113_,
                v___x_7142_,
                v___x_7143_,
                v___y_7120_,
                v___y_7121_,
                v___y_7122_,
                v___y_7123_,
            );
            crate::leanh::lean_dec_ref(v_fvars_7116_);
            if crate::leanh::lean_obj_tag(v___x_7144_) == 0 {
                let mut v_a_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_7145_ = crate::leanh::lean_ctor_get(v___x_7144_, 0);
                crate::leanh::lean_inc(v_a_7145_);
                crate::leanh::lean_dec_ref_known(v___x_7144_, 1);
                v___x_7146_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v_a_7145_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
                return v___x_7146_;
            } else {
                crate::leanh::lean_dec_ref(v_post_7112_);
                crate::leanh::lean_dec_ref(v_pre_7111_);
                return v___x_7144_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_7116_);
            crate::leanh::lean_dec_ref(v_post_7112_);
            crate::leanh::lean_dec_ref(v_pre_7111_);
            return v___x_7139_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(
    mut v_fvars_7147_: *mut crate::leanh::LeanObject,
    mut v_pre_7148_: *mut crate::leanh::LeanObject,
    mut v_post_7149_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7150_: u8,
    mut v_skipConstInApp_7151_: u8,
    mut v_skipInstances_7152_: u8,
    mut v_body_7153_: *mut crate::leanh::LeanObject,
    mut v_x_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
    mut v___y_7157_: *mut crate::leanh::LeanObject,
    mut v___y_7158_: *mut crate::leanh::LeanObject,
    mut v___y_7159_: *mut crate::leanh::LeanObject,
    mut v___y_7160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7162_ = lean_array_push(v_fvars_7147_, v_x_7154_);
    v___x_7163_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_7148_, v_post_7149_, v_usedLetOnly_7150_, v_skipConstInApp_7151_, v_skipInstances_7152_, v___x_7162_, v_body_7153_, v___y_7155_, v___y_7156_, v___y_7157_, v___y_7158_, v___y_7159_, v___y_7160_);
    return v___x_7163_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(
    mut v_pre_7164_: *mut crate::leanh::LeanObject,
    mut v_post_7165_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7166_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7167_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7168_: *mut crate::leanh::LeanObject,
    mut v_e_7169_: *mut crate::leanh::LeanObject,
    mut v_a_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
    mut v___y_7173_: *mut crate::leanh::LeanObject,
    mut v___y_7174_: *mut crate::leanh::LeanObject,
    mut v___y_7175_: *mut crate::leanh::LeanObject,
    mut v___y_7176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7177_: u8 = 0;
    let mut v_skipConstInApp_boxed_7178_: u8 = 0;
    let mut v_skipInstances_boxed_7179_: u8 = 0;
    let mut v_res_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7177_ = (crate::leanh::lean_unbox(v_usedLetOnly_7166_) as u8);
    v_skipConstInApp_boxed_7178_ = (crate::leanh::lean_unbox(v_skipConstInApp_7167_) as u8);
    v_skipInstances_boxed_7179_ = (crate::leanh::lean_unbox(v_skipInstances_7168_) as u8);
    v_res_7180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_7164_, v_post_7165_, v_usedLetOnly_boxed_7177_, v_skipConstInApp_boxed_7178_, v_skipInstances_boxed_7179_, v_e_7169_, v_a_7170_, v___y_7171_, v___y_7172_, v___y_7173_, v___y_7174_, v___y_7175_);
    crate::leanh::lean_dec(v___y_7175_);
    crate::leanh::lean_dec_ref(v___y_7174_);
    crate::leanh::lean_dec(v___y_7173_);
    crate::leanh::lean_dec_ref(v___y_7172_);
    crate::leanh::lean_dec(v___y_7171_);
    crate::leanh::lean_dec(v_a_7170_);
    return v_res_7180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(
    mut v_pre_7181_: *mut crate::leanh::LeanObject,
    mut v_post_7182_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7183_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7184_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7185_: *mut crate::leanh::LeanObject,
    mut v_sz_7186_: *mut crate::leanh::LeanObject,
    mut v_i_7187_: *mut crate::leanh::LeanObject,
    mut v_bs_7188_: *mut crate::leanh::LeanObject,
    mut v___y_7189_: *mut crate::leanh::LeanObject,
    mut v___y_7190_: *mut crate::leanh::LeanObject,
    mut v___y_7191_: *mut crate::leanh::LeanObject,
    mut v___y_7192_: *mut crate::leanh::LeanObject,
    mut v___y_7193_: *mut crate::leanh::LeanObject,
    mut v___y_7194_: *mut crate::leanh::LeanObject,
    mut v___y_7195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7196_: u8 = 0;
    let mut v_skipConstInApp_boxed_7197_: u8 = 0;
    let mut v_skipInstances_boxed_7198_: u8 = 0;
    let mut v_sz_boxed_7199_: usize = 0;
    let mut v_i_boxed_7200_: usize = 0;
    let mut v_res_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7196_ = (crate::leanh::lean_unbox(v_usedLetOnly_7183_) as u8);
    v_skipConstInApp_boxed_7197_ = (crate::leanh::lean_unbox(v_skipConstInApp_7184_) as u8);
    v_skipInstances_boxed_7198_ = (crate::leanh::lean_unbox(v_skipInstances_7185_) as u8);
    v_sz_boxed_7199_ = crate::leanh::lean_unbox_usize(v_sz_7186_);
    crate::leanh::lean_dec(v_sz_7186_);
    v_i_boxed_7200_ = crate::leanh::lean_unbox_usize(v_i_7187_);
    crate::leanh::lean_dec(v_i_7187_);
    v_res_7201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_7181_, v_post_7182_, v_usedLetOnly_boxed_7196_, v_skipConstInApp_boxed_7197_, v_skipInstances_boxed_7198_, v_sz_boxed_7199_, v_i_boxed_7200_, v_bs_7188_, v___y_7189_, v___y_7190_, v___y_7191_, v___y_7192_, v___y_7193_, v___y_7194_);
    crate::leanh::lean_dec(v___y_7194_);
    crate::leanh::lean_dec_ref(v___y_7193_);
    crate::leanh::lean_dec(v___y_7192_);
    crate::leanh::lean_dec_ref(v___y_7191_);
    crate::leanh::lean_dec(v___y_7190_);
    crate::leanh::lean_dec(v___y_7189_);
    return v_res_7201_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(
    mut v_pre_7202_: *mut crate::leanh::LeanObject,
    mut v_post_7203_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7204_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7205_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7206_: *mut crate::leanh::LeanObject,
    mut v_e_7207_: *mut crate::leanh::LeanObject,
    mut v_a_7208_: *mut crate::leanh::LeanObject,
    mut v___y_7209_: *mut crate::leanh::LeanObject,
    mut v___y_7210_: *mut crate::leanh::LeanObject,
    mut v___y_7211_: *mut crate::leanh::LeanObject,
    mut v___y_7212_: *mut crate::leanh::LeanObject,
    mut v___y_7213_: *mut crate::leanh::LeanObject,
    mut v___y_7214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7215_: u8 = 0;
    let mut v_skipConstInApp_boxed_7216_: u8 = 0;
    let mut v_skipInstances_boxed_7217_: u8 = 0;
    let mut v_res_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7215_ = (crate::leanh::lean_unbox(v_usedLetOnly_7204_) as u8);
    v_skipConstInApp_boxed_7216_ = (crate::leanh::lean_unbox(v_skipConstInApp_7205_) as u8);
    v_skipInstances_boxed_7217_ = (crate::leanh::lean_unbox(v_skipInstances_7206_) as u8);
    v_res_7218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7202_, v_post_7203_, v_usedLetOnly_boxed_7215_, v_skipConstInApp_boxed_7216_, v_skipInstances_boxed_7217_, v_e_7207_, v_a_7208_, v___y_7209_, v___y_7210_, v___y_7211_, v___y_7212_, v___y_7213_);
    crate::leanh::lean_dec(v___y_7213_);
    crate::leanh::lean_dec_ref(v___y_7212_);
    crate::leanh::lean_dec(v___y_7211_);
    crate::leanh::lean_dec_ref(v___y_7210_);
    crate::leanh::lean_dec(v___y_7209_);
    crate::leanh::lean_dec(v_a_7208_);
    return v_res_7218_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(
    mut v_pre_7219_: *mut crate::leanh::LeanObject,
    mut v_post_7220_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7221_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7222_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7223_: *mut crate::leanh::LeanObject,
    mut v_fvars_7224_: *mut crate::leanh::LeanObject,
    mut v_e_7225_: *mut crate::leanh::LeanObject,
    mut v_a_7226_: *mut crate::leanh::LeanObject,
    mut v___y_7227_: *mut crate::leanh::LeanObject,
    mut v___y_7228_: *mut crate::leanh::LeanObject,
    mut v___y_7229_: *mut crate::leanh::LeanObject,
    mut v___y_7230_: *mut crate::leanh::LeanObject,
    mut v___y_7231_: *mut crate::leanh::LeanObject,
    mut v___y_7232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7233_: u8 = 0;
    let mut v_skipConstInApp_boxed_7234_: u8 = 0;
    let mut v_skipInstances_boxed_7235_: u8 = 0;
    let mut v_res_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7233_ = (crate::leanh::lean_unbox(v_usedLetOnly_7221_) as u8);
    v_skipConstInApp_boxed_7234_ = (crate::leanh::lean_unbox(v_skipConstInApp_7222_) as u8);
    v_skipInstances_boxed_7235_ = (crate::leanh::lean_unbox(v_skipInstances_7223_) as u8);
    v_res_7236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_7219_, v_post_7220_, v_usedLetOnly_boxed_7233_, v_skipConstInApp_boxed_7234_, v_skipInstances_boxed_7235_, v_fvars_7224_, v_e_7225_, v_a_7226_, v___y_7227_, v___y_7228_, v___y_7229_, v___y_7230_, v___y_7231_);
    crate::leanh::lean_dec(v___y_7231_);
    crate::leanh::lean_dec_ref(v___y_7230_);
    crate::leanh::lean_dec(v___y_7229_);
    crate::leanh::lean_dec_ref(v___y_7228_);
    crate::leanh::lean_dec(v___y_7227_);
    crate::leanh::lean_dec(v_a_7226_);
    return v_res_7236_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(
    mut v_pre_7237_: *mut crate::leanh::LeanObject,
    mut v_post_7238_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7239_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7240_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7241_: *mut crate::leanh::LeanObject,
    mut v_fvars_7242_: *mut crate::leanh::LeanObject,
    mut v_e_7243_: *mut crate::leanh::LeanObject,
    mut v_a_7244_: *mut crate::leanh::LeanObject,
    mut v___y_7245_: *mut crate::leanh::LeanObject,
    mut v___y_7246_: *mut crate::leanh::LeanObject,
    mut v___y_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7251_: u8 = 0;
    let mut v_skipConstInApp_boxed_7252_: u8 = 0;
    let mut v_skipInstances_boxed_7253_: u8 = 0;
    let mut v_res_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7251_ = (crate::leanh::lean_unbox(v_usedLetOnly_7239_) as u8);
    v_skipConstInApp_boxed_7252_ = (crate::leanh::lean_unbox(v_skipConstInApp_7240_) as u8);
    v_skipInstances_boxed_7253_ = (crate::leanh::lean_unbox(v_skipInstances_7241_) as u8);
    v_res_7254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_7237_, v_post_7238_, v_usedLetOnly_boxed_7251_, v_skipConstInApp_boxed_7252_, v_skipInstances_boxed_7253_, v_fvars_7242_, v_e_7243_, v_a_7244_, v___y_7245_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_);
    crate::leanh::lean_dec(v___y_7249_);
    crate::leanh::lean_dec_ref(v___y_7248_);
    crate::leanh::lean_dec(v___y_7247_);
    crate::leanh::lean_dec_ref(v___y_7246_);
    crate::leanh::lean_dec(v___y_7245_);
    crate::leanh::lean_dec(v_a_7244_);
    return v_res_7254_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(
    mut v_pre_7255_: *mut crate::leanh::LeanObject,
    mut v_post_7256_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7257_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7258_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7259_: *mut crate::leanh::LeanObject,
    mut v_fvars_7260_: *mut crate::leanh::LeanObject,
    mut v_e_7261_: *mut crate::leanh::LeanObject,
    mut v_a_7262_: *mut crate::leanh::LeanObject,
    mut v___y_7263_: *mut crate::leanh::LeanObject,
    mut v___y_7264_: *mut crate::leanh::LeanObject,
    mut v___y_7265_: *mut crate::leanh::LeanObject,
    mut v___y_7266_: *mut crate::leanh::LeanObject,
    mut v___y_7267_: *mut crate::leanh::LeanObject,
    mut v___y_7268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7269_: u8 = 0;
    let mut v_skipConstInApp_boxed_7270_: u8 = 0;
    let mut v_skipInstances_boxed_7271_: u8 = 0;
    let mut v_res_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7269_ = (crate::leanh::lean_unbox(v_usedLetOnly_7257_) as u8);
    v_skipConstInApp_boxed_7270_ = (crate::leanh::lean_unbox(v_skipConstInApp_7258_) as u8);
    v_skipInstances_boxed_7271_ = (crate::leanh::lean_unbox(v_skipInstances_7259_) as u8);
    v_res_7272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_7255_, v_post_7256_, v_usedLetOnly_boxed_7269_, v_skipConstInApp_boxed_7270_, v_skipInstances_boxed_7271_, v_fvars_7260_, v_e_7261_, v_a_7262_, v___y_7263_, v___y_7264_, v___y_7265_, v___y_7266_, v___y_7267_);
    crate::leanh::lean_dec(v___y_7267_);
    crate::leanh::lean_dec_ref(v___y_7266_);
    crate::leanh::lean_dec(v___y_7265_);
    crate::leanh::lean_dec_ref(v___y_7264_);
    crate::leanh::lean_dec(v___y_7263_);
    crate::leanh::lean_dec(v_a_7262_);
    return v_res_7272_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_upperBound_7273_: *mut crate::leanh::LeanObject,
    mut v___x_7274_: *mut crate::leanh::LeanObject,
    mut v_pre_7275_: *mut crate::leanh::LeanObject,
    mut v_post_7276_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7277_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7278_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7279_: *mut crate::leanh::LeanObject,
    mut v_a_7280_: *mut crate::leanh::LeanObject,
    mut v_b_7281_: *mut crate::leanh::LeanObject,
    mut v___y_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
    mut v___y_7284_: *mut crate::leanh::LeanObject,
    mut v___y_7285_: *mut crate::leanh::LeanObject,
    mut v___y_7286_: *mut crate::leanh::LeanObject,
    mut v___y_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7289_: u8 = 0;
    let mut v_skipConstInApp_boxed_7290_: u8 = 0;
    let mut v_skipInstances_boxed_7291_: u8 = 0;
    let mut v_res_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7289_ = (crate::leanh::lean_unbox(v_usedLetOnly_7277_) as u8);
    v_skipConstInApp_boxed_7290_ = (crate::leanh::lean_unbox(v_skipConstInApp_7278_) as u8);
    v_skipInstances_boxed_7291_ = (crate::leanh::lean_unbox(v_skipInstances_7279_) as u8);
    v_res_7292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_7273_, v___x_7274_, v_pre_7275_, v_post_7276_, v_usedLetOnly_boxed_7289_, v_skipConstInApp_boxed_7290_, v_skipInstances_boxed_7291_, v_a_7280_, v_b_7281_, v___y_7282_, v___y_7283_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_);
    crate::leanh::lean_dec(v___y_7287_);
    crate::leanh::lean_dec_ref(v___y_7286_);
    crate::leanh::lean_dec(v___y_7285_);
    crate::leanh::lean_dec_ref(v___y_7284_);
    crate::leanh::lean_dec(v___y_7283_);
    crate::leanh::lean_dec(v___y_7282_);
    crate::leanh::lean_dec_ref(v___x_7274_);
    crate::leanh::lean_dec(v_upperBound_7273_);
    return v_res_7292_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(
    mut v_skipInstances_7293_: *mut crate::leanh::LeanObject,
    mut v_pre_7294_: *mut crate::leanh::LeanObject,
    mut v_post_7295_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7296_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7297_: *mut crate::leanh::LeanObject,
    mut v_x_7298_: *mut crate::leanh::LeanObject,
    mut v_x_7299_: *mut crate::leanh::LeanObject,
    mut v_x_7300_: *mut crate::leanh::LeanObject,
    mut v___y_7301_: *mut crate::leanh::LeanObject,
    mut v___y_7302_: *mut crate::leanh::LeanObject,
    mut v___y_7303_: *mut crate::leanh::LeanObject,
    mut v___y_7304_: *mut crate::leanh::LeanObject,
    mut v___y_7305_: *mut crate::leanh::LeanObject,
    mut v___y_7306_: *mut crate::leanh::LeanObject,
    mut v___y_7307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipInstances_boxed_7308_: u8 = 0;
    let mut v_usedLetOnly_boxed_7309_: u8 = 0;
    let mut v_skipConstInApp_boxed_7310_: u8 = 0;
    let mut v_res_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7308_ = (crate::leanh::lean_unbox(v_skipInstances_7293_) as u8);
    v_usedLetOnly_boxed_7309_ = (crate::leanh::lean_unbox(v_usedLetOnly_7296_) as u8);
    v_skipConstInApp_boxed_7310_ = (crate::leanh::lean_unbox(v_skipConstInApp_7297_) as u8);
    v_res_7311_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_7308_, v_pre_7294_, v_post_7295_, v_usedLetOnly_boxed_7309_, v_skipConstInApp_boxed_7310_, v_x_7298_, v_x_7299_, v_x_7300_, v___y_7301_, v___y_7302_, v___y_7303_, v___y_7304_, v___y_7305_, v___y_7306_);
    crate::leanh::lean_dec(v___y_7306_);
    crate::leanh::lean_dec_ref(v___y_7305_);
    crate::leanh::lean_dec(v___y_7304_);
    crate::leanh::lean_dec_ref(v___y_7303_);
    crate::leanh::lean_dec(v___y_7302_);
    crate::leanh::lean_dec(v___y_7301_);
    return v_res_7311_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(
    mut v_00_u03b1_7312_: *mut crate::leanh::LeanObject,
    mut v_x_7313_: *mut crate::leanh::LeanObject,
    mut v___y_7314_: *mut crate::leanh::LeanObject,
    mut v___y_7315_: *mut crate::leanh::LeanObject,
    mut v___y_7316_: *mut crate::leanh::LeanObject,
    mut v___y_7317_: *mut crate::leanh::LeanObject,
    mut v___y_7318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7320_ = crate::leanh::lean_apply_1(v_x_7313_, crate::leanh::lean_box(0));
    v___x_7321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7321_, 0, v___x_7320_);
    return v___x_7321_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(
    mut v_00_u03b1_7322_: *mut crate::leanh::LeanObject,
    mut v_x_7323_: *mut crate::leanh::LeanObject,
    mut v___y_7324_: *mut crate::leanh::LeanObject,
    mut v___y_7325_: *mut crate::leanh::LeanObject,
    mut v___y_7326_: *mut crate::leanh::LeanObject,
    mut v___y_7327_: *mut crate::leanh::LeanObject,
    mut v___y_7328_: *mut crate::leanh::LeanObject,
    mut v___y_7329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7330_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(
        v_00_u03b1_7322_,
        v_x_7323_,
        v___y_7324_,
        v___y_7325_,
        v___y_7326_,
        v___y_7327_,
        v___y_7328_,
    );
    crate::leanh::lean_dec(v___y_7328_);
    crate::leanh::lean_dec_ref(v___y_7327_);
    crate::leanh::lean_dec(v___y_7326_);
    crate::leanh::lean_dec_ref(v___y_7325_);
    crate::leanh::lean_dec(v___y_7324_);
    return v_res_7330_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7331_ = crate::leanh::lean_box(0);
    v___x_7332_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_7333_ = lean_mk_array(v___x_7332_, v___x_7331_);
    return v___x_7333_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7334_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
    v___x_7335_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7336_, 0, v___x_7335_);
    crate::leanh::lean_ctor_set(v___x_7336_, 1, v___x_7334_);
    return v___x_7336_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7337_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
    v___x_7338_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_7338_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7338_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7338_, 2, v___x_7337_);
    return v___x_7338_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(
    mut v_input_7339_: *mut crate::leanh::LeanObject,
    mut v_pre_7340_: *mut crate::leanh::LeanObject,
    mut v_post_7341_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7342_: u8,
    mut v_skipConstInApp_7343_: u8,
    mut v___y_7344_: *mut crate::leanh::LeanObject,
    mut v___y_7345_: *mut crate::leanh::LeanObject,
    mut v___y_7346_: *mut crate::leanh::LeanObject,
    mut v___y_7347_: *mut crate::leanh::LeanObject,
    mut v___y_7348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: u8 = 0;
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7360_: u8 = 0;
    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7364_: u8 = 0;
    let mut v_unused_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7350_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
                v___x_7351_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7350_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                v_a_7352_ = crate::leanh::lean_ctor_get(v___x_7351_, 0);
                crate::leanh::lean_inc(v_a_7352_);
                crate::leanh::lean_dec_ref(v___x_7351_);
                v___x_7353_ = 0;
                v___x_7354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7340_, v_post_7341_, v_usedLetOnly_7342_, v_skipConstInApp_7343_, v___x_7353_, v_input_7339_, v_a_7352_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                if crate::leanh::lean_obj_tag(v___x_7354_) == 0 {
                    v_a_7355_ = crate::leanh::lean_ctor_get(v___x_7354_, 0);
                    crate::leanh::lean_inc(v_a_7355_);
                    crate::leanh::lean_dec_ref_known(v___x_7354_, 1);
                    v___x_7356_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_7356_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7356_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7356_, 2, v_a_7352_);
                    v___x_7357_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7356_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                    v_isSharedCheck_7364_ = (!crate::leanh::lean_is_exclusive(v___x_7357_)) as u8;
                    if v_isSharedCheck_7364_ == 0 {
                        v_unused_7365_ = crate::leanh::lean_ctor_get(v___x_7357_, 0);
                        crate::leanh::lean_dec(v_unused_7365_);
                        v___x_7359_ = v___x_7357_;
                        v_isShared_7360_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7357_);
                        v___x_7359_ = crate::leanh::lean_box(0);
                        v_isShared_7360_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7352_);
                    return v___x_7354_;
                }
            }
            1 => {
                if v_isShared_7360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7359_, 0, v_a_7355_);
                    v___x_7362_ = v___x_7359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7363_, 0, v_a_7355_);
                    v___x_7362_ = v_reuseFailAlloc_7363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(
    mut v_input_7366_: *mut crate::leanh::LeanObject,
    mut v_pre_7367_: *mut crate::leanh::LeanObject,
    mut v_post_7368_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7369_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7370_: *mut crate::leanh::LeanObject,
    mut v___y_7371_: *mut crate::leanh::LeanObject,
    mut v___y_7372_: *mut crate::leanh::LeanObject,
    mut v___y_7373_: *mut crate::leanh::LeanObject,
    mut v___y_7374_: *mut crate::leanh::LeanObject,
    mut v___y_7375_: *mut crate::leanh::LeanObject,
    mut v___y_7376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7377_: u8 = 0;
    let mut v_skipConstInApp_boxed_7378_: u8 = 0;
    let mut v_res_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7377_ = (crate::leanh::lean_unbox(v_usedLetOnly_7369_) as u8);
    v_skipConstInApp_boxed_7378_ = (crate::leanh::lean_unbox(v_skipConstInApp_7370_) as u8);
    v_res_7379_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(
        v_input_7366_,
        v_pre_7367_,
        v_post_7368_,
        v_usedLetOnly_boxed_7377_,
        v_skipConstInApp_boxed_7378_,
        v___y_7371_,
        v___y_7372_,
        v___y_7373_,
        v___y_7374_,
        v___y_7375_,
    );
    crate::leanh::lean_dec(v___y_7375_);
    crate::leanh::lean_dec_ref(v___y_7374_);
    crate::leanh::lean_dec(v___y_7373_);
    crate::leanh::lean_dec_ref(v___y_7372_);
    crate::leanh::lean_dec(v___y_7371_);
    return v_res_7379_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore(
    mut v_e_7381_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_7382_: u8,
    mut v_a_7383_: *mut crate::leanh::LeanObject,
    mut v_a_7384_: *mut crate::leanh::LeanObject,
    mut v_a_7385_: *mut crate::leanh::LeanObject,
    mut v_a_7386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: u8 = 0;
    let mut v___x_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7398_: u8 = 0;
    let mut v___x_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7388_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once),
                    _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                );
                v___x_7389_ = lean_st_mk_ref(v___x_7388_);
                v___x_7390_ = crate::leanh::lean_box((v_elimTrivial_7382_) as usize);
                v_pre_7391_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed as *mut core::ffi::c_void,
                    8,
                    1,
                );
                crate::leanh::lean_closure_set(v_pre_7391_, 0, v___x_7390_);
                v___f_7392_ = l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0;
                v___x_7393_ = 0;
                v___x_7394_ =
                    l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(
                        v_e_7381_,
                        v_pre_7391_,
                        v___f_7392_,
                        v___x_7393_,
                        v___x_7393_,
                        v___x_7389_,
                        v_a_7383_,
                        v_a_7384_,
                        v_a_7385_,
                        v_a_7386_,
                    );
                if crate::leanh::lean_obj_tag(v___x_7394_) == 0 {
                    v_a_7395_ = crate::leanh::lean_ctor_get(v___x_7394_, 0);
                    v_isSharedCheck_7403_ = (!crate::leanh::lean_is_exclusive(v___x_7394_)) as u8;
                    if v_isSharedCheck_7403_ == 0 {
                        v___x_7397_ = v___x_7394_;
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7395_);
                        crate::leanh::lean_dec(v___x_7394_);
                        v___x_7397_ = crate::leanh::lean_box(0);
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7389_);
                    return v___x_7394_;
                }
            }
            1 => {
                v___x_7399_ = lean_st_ref_get(v___x_7389_);
                crate::leanh::lean_dec(v___x_7389_);
                crate::leanh::lean_dec(v___x_7399_);
                if v_isShared_7398_ == 0 {
                    v___x_7401_ = v___x_7397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7402_, 0, v_a_7395_);
                    v___x_7401_ = v_reuseFailAlloc_7402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(
    mut v_e_7404_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_7405_: *mut crate::leanh::LeanObject,
    mut v_a_7406_: *mut crate::leanh::LeanObject,
    mut v_a_7407_: *mut crate::leanh::LeanObject,
    mut v_a_7408_: *mut crate::leanh::LeanObject,
    mut v_a_7409_: *mut crate::leanh::LeanObject,
    mut v_a_7410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_7411_: u8 = 0;
    let mut v_res_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7411_ = (crate::leanh::lean_unbox(v_elimTrivial_7405_) as u8);
    v_res_7412_ = l_Lean_Elab_Tactic_Do_elimLetsCore(
        v_e_7404_,
        v_elimTrivial_boxed_7411_,
        v_a_7406_,
        v_a_7407_,
        v_a_7408_,
        v_a_7409_,
    );
    crate::leanh::lean_dec(v_a_7409_);
    crate::leanh::lean_dec_ref(v_a_7408_);
    crate::leanh::lean_dec(v_a_7407_);
    crate::leanh::lean_dec_ref(v_a_7406_);
    return v_res_7412_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(
    mut v_upperBound_7413_: *mut crate::leanh::LeanObject,
    mut v___x_7414_: *mut crate::leanh::LeanObject,
    mut v_pre_7415_: *mut crate::leanh::LeanObject,
    mut v_post_7416_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7417_: u8,
    mut v_skipConstInApp_7418_: u8,
    mut v_skipInstances_7419_: u8,
    mut v___x_7420_: *mut crate::leanh::LeanObject,
    mut v_inst_7421_: *mut crate::leanh::LeanObject,
    mut v_R_7422_: *mut crate::leanh::LeanObject,
    mut v_a_7423_: *mut crate::leanh::LeanObject,
    mut v_b_7424_: *mut crate::leanh::LeanObject,
    mut v_c_7425_: *mut crate::leanh::LeanObject,
    mut v___y_7426_: *mut crate::leanh::LeanObject,
    mut v___y_7427_: *mut crate::leanh::LeanObject,
    mut v___y_7428_: *mut crate::leanh::LeanObject,
    mut v___y_7429_: *mut crate::leanh::LeanObject,
    mut v___y_7430_: *mut crate::leanh::LeanObject,
    mut v___y_7431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_7413_, v___x_7414_, v_pre_7415_, v_post_7416_, v_usedLetOnly_7417_, v_skipConstInApp_7418_, v_skipInstances_7419_, v_a_7423_, v_b_7424_, v___y_7426_, v___y_7427_, v___y_7428_, v___y_7429_, v___y_7430_, v___y_7431_);
    return v___x_7433_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_7434_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_7435_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_pre_7436_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_post_7437_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_7438_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_7439_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_7440_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_7441_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_7442_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_R_7443_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_7444_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_b_7445_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_c_7446_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7447_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7448_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7449_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7450_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_7451_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_7452_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_7453_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_usedLetOnly_boxed_7454_: u8 = 0;
    let mut v_skipConstInApp_boxed_7455_: u8 = 0;
    let mut v_skipInstances_boxed_7456_: u8 = 0;
    let mut v_res_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7454_ = (crate::leanh::lean_unbox(v_usedLetOnly_7438_) as u8);
    v_skipConstInApp_boxed_7455_ = (crate::leanh::lean_unbox(v_skipConstInApp_7439_) as u8);
    v_skipInstances_boxed_7456_ = (crate::leanh::lean_unbox(v_skipInstances_7440_) as u8);
    v_res_7457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_7434_, v___x_7435_, v_pre_7436_, v_post_7437_, v_usedLetOnly_boxed_7454_, v_skipConstInApp_boxed_7455_, v_skipInstances_boxed_7456_, v___x_7441_, v_inst_7442_, v_R_7443_, v_a_7444_, v_b_7445_, v_c_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_, v___y_7452_);
    crate::leanh::lean_dec(v___y_7452_);
    crate::leanh::lean_dec_ref(v___y_7451_);
    crate::leanh::lean_dec(v___y_7450_);
    crate::leanh::lean_dec_ref(v___y_7449_);
    crate::leanh::lean_dec(v___y_7448_);
    crate::leanh::lean_dec(v___y_7447_);
    crate::leanh::lean_dec(v___x_7441_);
    crate::leanh::lean_dec_ref(v___x_7435_);
    crate::leanh::lean_dec(v_upperBound_7434_);
    return v_res_7457_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(
    mut v_00_u03b2_7458_: *mut crate::leanh::LeanObject,
    mut v_m_7459_: *mut crate::leanh::LeanObject,
    mut v_a_7460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_7459_, v_a_7460_);
    return v___x_7461_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_7462_: *mut crate::leanh::LeanObject,
    mut v_m_7463_: *mut crate::leanh::LeanObject,
    mut v_a_7464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_7462_, v_m_7463_, v_a_7464_);
    crate::leanh::lean_dec_ref(v_a_7464_);
    crate::leanh::lean_dec_ref(v_m_7463_);
    return v_res_7465_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_7466_: *mut crate::leanh::LeanObject,
    mut v_name_7467_: *mut crate::leanh::LeanObject,
    mut v_bi_7468_: u8,
    mut v_type_7469_: *mut crate::leanh::LeanObject,
    mut v_k_7470_: *mut crate::leanh::LeanObject,
    mut v_kind_7471_: u8,
    mut v___y_7472_: *mut crate::leanh::LeanObject,
    mut v___y_7473_: *mut crate::leanh::LeanObject,
    mut v___y_7474_: *mut crate::leanh::LeanObject,
    mut v___y_7475_: *mut crate::leanh::LeanObject,
    mut v___y_7476_: *mut crate::leanh::LeanObject,
    mut v___y_7477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_7467_, v_bi_7468_, v_type_7469_, v_k_7470_, v_kind_7471_, v___y_7472_, v___y_7473_, v___y_7474_, v___y_7475_, v___y_7476_, v___y_7477_);
    return v___x_7479_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_7480_: *mut crate::leanh::LeanObject,
    mut v_name_7481_: *mut crate::leanh::LeanObject,
    mut v_bi_7482_: *mut crate::leanh::LeanObject,
    mut v_type_7483_: *mut crate::leanh::LeanObject,
    mut v_k_7484_: *mut crate::leanh::LeanObject,
    mut v_kind_7485_: *mut crate::leanh::LeanObject,
    mut v___y_7486_: *mut crate::leanh::LeanObject,
    mut v___y_7487_: *mut crate::leanh::LeanObject,
    mut v___y_7488_: *mut crate::leanh::LeanObject,
    mut v___y_7489_: *mut crate::leanh::LeanObject,
    mut v___y_7490_: *mut crate::leanh::LeanObject,
    mut v___y_7491_: *mut crate::leanh::LeanObject,
    mut v___y_7492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_7493_: u8 = 0;
    let mut v_kind_boxed_7494_: u8 = 0;
    let mut v_res_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_7493_ = (crate::leanh::lean_unbox(v_bi_7482_) as u8);
    v_kind_boxed_7494_ = (crate::leanh::lean_unbox(v_kind_7485_) as u8);
    v_res_7495_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_7480_, v_name_7481_, v_bi_boxed_7493_, v_type_7483_, v_k_7484_, v_kind_boxed_7494_, v___y_7486_, v___y_7487_, v___y_7488_, v___y_7489_, v___y_7490_, v___y_7491_);
    crate::leanh::lean_dec(v___y_7491_);
    crate::leanh::lean_dec_ref(v___y_7490_);
    crate::leanh::lean_dec(v___y_7489_);
    crate::leanh::lean_dec_ref(v___y_7488_);
    crate::leanh::lean_dec(v___y_7487_);
    crate::leanh::lean_dec(v___y_7486_);
    return v_res_7495_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(
    mut v_00_u03b1_7496_: *mut crate::leanh::LeanObject,
    mut v_name_7497_: *mut crate::leanh::LeanObject,
    mut v_type_7498_: *mut crate::leanh::LeanObject,
    mut v_val_7499_: *mut crate::leanh::LeanObject,
    mut v_k_7500_: *mut crate::leanh::LeanObject,
    mut v_nondep_7501_: u8,
    mut v_kind_7502_: u8,
    mut v___y_7503_: *mut crate::leanh::LeanObject,
    mut v___y_7504_: *mut crate::leanh::LeanObject,
    mut v___y_7505_: *mut crate::leanh::LeanObject,
    mut v___y_7506_: *mut crate::leanh::LeanObject,
    mut v___y_7507_: *mut crate::leanh::LeanObject,
    mut v___y_7508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7510_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_7497_, v_type_7498_, v_val_7499_, v_k_7500_, v_nondep_7501_, v_kind_7502_, v___y_7503_, v___y_7504_, v___y_7505_, v___y_7506_, v___y_7507_, v___y_7508_);
    return v___x_7510_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(
    mut v_00_u03b1_7511_: *mut crate::leanh::LeanObject,
    mut v_name_7512_: *mut crate::leanh::LeanObject,
    mut v_type_7513_: *mut crate::leanh::LeanObject,
    mut v_val_7514_: *mut crate::leanh::LeanObject,
    mut v_k_7515_: *mut crate::leanh::LeanObject,
    mut v_nondep_7516_: *mut crate::leanh::LeanObject,
    mut v_kind_7517_: *mut crate::leanh::LeanObject,
    mut v___y_7518_: *mut crate::leanh::LeanObject,
    mut v___y_7519_: *mut crate::leanh::LeanObject,
    mut v___y_7520_: *mut crate::leanh::LeanObject,
    mut v___y_7521_: *mut crate::leanh::LeanObject,
    mut v___y_7522_: *mut crate::leanh::LeanObject,
    mut v___y_7523_: *mut crate::leanh::LeanObject,
    mut v___y_7524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_7525_: u8 = 0;
    let mut v_kind_boxed_7526_: u8 = 0;
    let mut v_res_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7525_ = (crate::leanh::lean_unbox(v_nondep_7516_) as u8);
    v_kind_boxed_7526_ = (crate::leanh::lean_unbox(v_kind_7517_) as u8);
    v_res_7527_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_7511_, v_name_7512_, v_type_7513_, v_val_7514_, v_k_7515_, v_nondep_boxed_7525_, v_kind_boxed_7526_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_, v___y_7523_);
    crate::leanh::lean_dec(v___y_7523_);
    crate::leanh::lean_dec_ref(v___y_7522_);
    crate::leanh::lean_dec(v___y_7521_);
    crate::leanh::lean_dec_ref(v___y_7520_);
    crate::leanh::lean_dec(v___y_7519_);
    crate::leanh::lean_dec(v___y_7518_);
    return v_res_7527_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(
    mut v_00_u03b1_7528_: *mut crate::leanh::LeanObject,
    mut v_ref_7529_: *mut crate::leanh::LeanObject,
    mut v___y_7530_: *mut crate::leanh::LeanObject,
    mut v___y_7531_: *mut crate::leanh::LeanObject,
    mut v___y_7532_: *mut crate::leanh::LeanObject,
    mut v___y_7533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7535_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_7529_);
    return v___x_7535_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(
    mut v_00_u03b1_7536_: *mut crate::leanh::LeanObject,
    mut v_ref_7537_: *mut crate::leanh::LeanObject,
    mut v___y_7538_: *mut crate::leanh::LeanObject,
    mut v___y_7539_: *mut crate::leanh::LeanObject,
    mut v___y_7540_: *mut crate::leanh::LeanObject,
    mut v___y_7541_: *mut crate::leanh::LeanObject,
    mut v___y_7542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7543_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_7536_, v_ref_7537_, v___y_7538_, v___y_7539_, v___y_7540_, v___y_7541_);
    crate::leanh::lean_dec(v___y_7541_);
    crate::leanh::lean_dec_ref(v___y_7540_);
    crate::leanh::lean_dec(v___y_7539_);
    crate::leanh::lean_dec_ref(v___y_7538_);
    return v_res_7543_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(
    mut v_00_u03b1_7544_: *mut crate::leanh::LeanObject,
    mut v_x_7545_: *mut crate::leanh::LeanObject,
    mut v___y_7546_: *mut crate::leanh::LeanObject,
    mut v___y_7547_: *mut crate::leanh::LeanObject,
    mut v___y_7548_: *mut crate::leanh::LeanObject,
    mut v___y_7549_: *mut crate::leanh::LeanObject,
    mut v___y_7550_: *mut crate::leanh::LeanObject,
    mut v___y_7551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
    return v___x_7553_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(
    mut v_00_u03b1_7554_: *mut crate::leanh::LeanObject,
    mut v_x_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
    mut v___y_7557_: *mut crate::leanh::LeanObject,
    mut v___y_7558_: *mut crate::leanh::LeanObject,
    mut v___y_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
    mut v___y_7561_: *mut crate::leanh::LeanObject,
    mut v___y_7562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7563_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_7554_, v_x_7555_, v___y_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_, v___y_7561_);
    crate::leanh::lean_dec(v___y_7561_);
    crate::leanh::lean_dec_ref(v___y_7560_);
    crate::leanh::lean_dec(v___y_7559_);
    crate::leanh::lean_dec_ref(v___y_7558_);
    crate::leanh::lean_dec(v___y_7557_);
    crate::leanh::lean_dec(v___y_7556_);
    return v_res_7563_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(
    mut v_00_u03b2_7564_: *mut crate::leanh::LeanObject,
    mut v_m_7565_: *mut crate::leanh::LeanObject,
    mut v_a_7566_: *mut crate::leanh::LeanObject,
    mut v_b_7567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_7565_, v_a_7566_, v_b_7567_);
    return v___x_7568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(
    mut v_00_u03b2_7569_: *mut crate::leanh::LeanObject,
    mut v_a_7570_: *mut crate::leanh::LeanObject,
    mut v_x_7571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_7570_, v_x_7571_);
    return v___x_7572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(
    mut v_00_u03b2_7573_: *mut crate::leanh::LeanObject,
    mut v_a_7574_: *mut crate::leanh::LeanObject,
    mut v_x_7575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_7573_, v_a_7574_, v_x_7575_);
    crate::leanh::lean_dec(v_x_7575_);
    crate::leanh::lean_dec_ref(v_a_7574_);
    return v_res_7576_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(
    mut v_00_u03b2_7577_: *mut crate::leanh::LeanObject,
    mut v_a_7578_: *mut crate::leanh::LeanObject,
    mut v_x_7579_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7580_: u8 = 0;
    v___x_7580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_7578_, v_x_7579_);
    return v___x_7580_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(
    mut v_00_u03b2_7581_: *mut crate::leanh::LeanObject,
    mut v_a_7582_: *mut crate::leanh::LeanObject,
    mut v_x_7583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7584_: u8 = 0;
    let mut v_r_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_7581_, v_a_7582_, v_x_7583_);
    crate::leanh::lean_dec(v_x_7583_);
    crate::leanh::lean_dec_ref(v_a_7582_);
    v_r_7585_ = crate::leanh::lean_box((v_res_7584_) as usize);
    return v_r_7585_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(
    mut v_00_u03b2_7586_: *mut crate::leanh::LeanObject,
    mut v_data_7587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_7587_);
    return v___x_7588_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(
    mut v_00_u03b2_7589_: *mut crate::leanh::LeanObject,
    mut v_a_7590_: *mut crate::leanh::LeanObject,
    mut v_b_7591_: *mut crate::leanh::LeanObject,
    mut v_x_7592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7593_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_7590_, v_b_7591_, v_x_7592_);
    return v___x_7593_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(
    mut v_00_u03b2_7594_: *mut crate::leanh::LeanObject,
    mut v_i_7595_: *mut crate::leanh::LeanObject,
    mut v_source_7596_: *mut crate::leanh::LeanObject,
    mut v_target_7597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7598_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_7595_, v_source_7596_, v_target_7597_);
    return v___x_7598_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(
    mut v_00_u03b2_7599_: *mut crate::leanh::LeanObject,
    mut v_x_7600_: *mut crate::leanh::LeanObject,
    mut v_x_7601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7602_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_7600_, v_x_7601_);
    return v___x_7602_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
    mut v_mvarId_7603_: *mut crate::leanh::LeanObject,
    mut v_x_7604_: *mut crate::leanh::LeanObject,
    mut v___y_7605_: *mut crate::leanh::LeanObject,
    mut v___y_7606_: *mut crate::leanh::LeanObject,
    mut v___y_7607_: *mut crate::leanh::LeanObject,
    mut v___y_7608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7614_: u8 = 0;
    let mut v___x_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7618_: u8 = 0;
    let mut v_a_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7622_: u8 = 0;
    let mut v___x_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_7603_,
                    v_x_7604_,
                    v___y_7605_,
                    v___y_7606_,
                    v___y_7607_,
                    v___y_7608_,
                );
                if crate::leanh::lean_obj_tag(v___x_7610_) == 0 {
                    v_a_7611_ = crate::leanh::lean_ctor_get(v___x_7610_, 0);
                    v_isSharedCheck_7618_ = (!crate::leanh::lean_is_exclusive(v___x_7610_)) as u8;
                    if v_isSharedCheck_7618_ == 0 {
                        v___x_7613_ = v___x_7610_;
                        v_isShared_7614_ = v_isSharedCheck_7618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7611_);
                        crate::leanh::lean_dec(v___x_7610_);
                        v___x_7613_ = crate::leanh::lean_box(0);
                        v_isShared_7614_ = v_isSharedCheck_7618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7619_ = crate::leanh::lean_ctor_get(v___x_7610_, 0);
                    v_isSharedCheck_7626_ = (!crate::leanh::lean_is_exclusive(v___x_7610_)) as u8;
                    if v_isSharedCheck_7626_ == 0 {
                        v___x_7621_ = v___x_7610_;
                        v_isShared_7622_ = v_isSharedCheck_7626_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7619_);
                        crate::leanh::lean_dec(v___x_7610_);
                        v___x_7621_ = crate::leanh::lean_box(0);
                        v_isShared_7622_ = v_isSharedCheck_7626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7614_ == 0 {
                    v___x_7616_ = v___x_7613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 0, v_a_7611_);
                    v___x_7616_ = v_reuseFailAlloc_7617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7616_;
            }
            3 => {
                if v_isShared_7622_ == 0 {
                    v___x_7624_ = v___x_7621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7625_, 0, v_a_7619_);
                    v___x_7624_ = v_reuseFailAlloc_7625_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(
    mut v_mvarId_7627_: *mut crate::leanh::LeanObject,
    mut v_x_7628_: *mut crate::leanh::LeanObject,
    mut v___y_7629_: *mut crate::leanh::LeanObject,
    mut v___y_7630_: *mut crate::leanh::LeanObject,
    mut v___y_7631_: *mut crate::leanh::LeanObject,
    mut v___y_7632_: *mut crate::leanh::LeanObject,
    mut v___y_7633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7634_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
        v_mvarId_7627_,
        v_x_7628_,
        v___y_7629_,
        v___y_7630_,
        v___y_7631_,
        v___y_7632_,
    );
    crate::leanh::lean_dec(v___y_7632_);
    crate::leanh::lean_dec_ref(v___y_7631_);
    crate::leanh::lean_dec(v___y_7630_);
    crate::leanh::lean_dec_ref(v___y_7629_);
    return v_res_7634_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(
    mut v_00_u03b1_7635_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7636_: *mut crate::leanh::LeanObject,
    mut v_x_7637_: *mut crate::leanh::LeanObject,
    mut v___y_7638_: *mut crate::leanh::LeanObject,
    mut v___y_7639_: *mut crate::leanh::LeanObject,
    mut v___y_7640_: *mut crate::leanh::LeanObject,
    mut v___y_7641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7643_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
        v_mvarId_7636_,
        v_x_7637_,
        v___y_7638_,
        v___y_7639_,
        v___y_7640_,
        v___y_7641_,
    );
    return v___x_7643_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(
    mut v_00_u03b1_7644_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7645_: *mut crate::leanh::LeanObject,
    mut v_x_7646_: *mut crate::leanh::LeanObject,
    mut v___y_7647_: *mut crate::leanh::LeanObject,
    mut v___y_7648_: *mut crate::leanh::LeanObject,
    mut v___y_7649_: *mut crate::leanh::LeanObject,
    mut v___y_7650_: *mut crate::leanh::LeanObject,
    mut v___y_7651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7652_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(
        v_00_u03b1_7644_,
        v_mvarId_7645_,
        v_x_7646_,
        v___y_7647_,
        v___y_7648_,
        v___y_7649_,
        v___y_7650_,
    );
    crate::leanh::lean_dec(v___y_7650_);
    crate::leanh::lean_dec_ref(v___y_7649_);
    crate::leanh::lean_dec(v___y_7648_);
    crate::leanh::lean_dec_ref(v___y_7647_);
    return v_res_7652_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(
    mut v_elimTrivial_7653_: u8,
    mut v_as_7654_: *mut crate::leanh::LeanObject,
    mut v_sz_7655_: usize,
    mut v_i_7656_: usize,
    mut v_b_7657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7659_: u8 = 0;
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7664_: u8 = 0;
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: usize = 0;
    let mut v___x_7671_: usize = 0;
    let mut v_reuseFailAlloc_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7680_: u8 = 0;
    let mut v___x_7681_: u8 = 0;
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: u8 = 0;
    let mut v___x_7690_: u8 = 0;
    let mut v___x_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7707_: u8 = 0;
    let mut v_isSharedCheck_7708_: u8 = 0;
    let mut v_unused_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7659_ = lean_usize_dec_lt(v_i_7656_, v_sz_7655_);
                if v___x_7659_ == 0 {
                    v___x_7660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7660_, 0, v_b_7657_);
                    return v___x_7660_;
                } else {
                    v_snd_7661_ = crate::leanh::lean_ctor_get(v_b_7657_, 1);
                    v_isSharedCheck_7708_ = (!crate::leanh::lean_is_exclusive(v_b_7657_)) as u8;
                    if v_isSharedCheck_7708_ == 0 {
                        v_unused_7709_ = crate::leanh::lean_ctor_get(v_b_7657_, 0);
                        crate::leanh::lean_dec(v_unused_7709_);
                        v___x_7663_ = v_b_7657_;
                        v_isShared_7664_ = v_isSharedCheck_7708_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7661_);
                        crate::leanh::lean_dec(v_b_7657_);
                        v___x_7663_ = crate::leanh::lean_box(0);
                        v_isShared_7664_ = v_isSharedCheck_7708_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7665_ = crate::leanh::lean_box(0);
                v_a_7674_ = lean_array_uget_borrowed(v_as_7654_, v_i_7656_);
                if crate::leanh::lean_obj_tag(v_a_7674_) == 0 {
                    v_a_7667_ = v_snd_7661_;
                    state = 2;
                    continue;
                } else {
                    v_val_7675_ = crate::leanh::lean_ctor_get(v_a_7674_, 0);
                    v_fst_7676_ = crate::leanh::lean_ctor_get(v_snd_7661_, 0);
                    v_snd_7677_ = crate::leanh::lean_ctor_get(v_snd_7661_, 1);
                    v_isSharedCheck_7707_ = (!crate::leanh::lean_is_exclusive(v_snd_7661_)) as u8;
                    if v_isSharedCheck_7707_ == 0 {
                        v___x_7679_ = v_snd_7661_;
                        v_isShared_7680_ = v_isSharedCheck_7707_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7677_);
                        crate::leanh::lean_inc(v_fst_7676_);
                        crate::leanh::lean_dec(v_snd_7661_);
                        v___x_7679_ = crate::leanh::lean_box(0);
                        v_isShared_7680_ = v_isSharedCheck_7707_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7663_, 1, v_a_7667_);
                    crate::leanh::lean_ctor_set(v___x_7663_, 0, v___x_7665_);
                    v___x_7669_ = v___x_7663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7673_, 0, v___x_7665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7673_, 1, v_a_7667_);
                    v___x_7669_ = v_reuseFailAlloc_7673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7670_ = 1usize;
                v___x_7671_ = lean_usize_add(v_i_7656_, v___x_7670_);
                v_i_7656_ = v___x_7671_;
                v_b_7657_ = v___x_7669_;
                state = 0;
                continue;
            }
            4 => {
                v___x_7681_ = 0;
                v___x_7682_ = l_Lean_LocalDecl_value_x3f(v_val_7675_, v___x_7681_);
                if crate::leanh::lean_obj_tag(v___x_7682_) == 1 {
                    v_val_7683_ = crate::leanh::lean_ctor_get(v___x_7682_, 0);
                    crate::leanh::lean_inc(v_val_7683_);
                    crate::leanh::lean_dec_ref_known(v___x_7682_, 1);
                    v___x_7684_ = l_Lean_LocalDecl_type(v_val_7675_);
                    if crate::leanh::lean_obj_tag(v___x_7684_) == 10 {
                        v_data_7685_ = crate::leanh::lean_ctor_get(v___x_7684_, 0);
                        crate::leanh::lean_inc(v_data_7685_);
                        crate::leanh::lean_dec_ref_known(v___x_7684_, 2);
                        v___x_7686_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7687_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7688_ = l_Lean_KVMap_getNat(v_data_7685_, v___x_7686_, v___x_7687_);
                        crate::leanh::lean_dec(v_data_7685_);
                        v___x_7689_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7688_);
                        crate::leanh::lean_dec(v___x_7688_);
                        v___x_7690_ = l_Lean_Elab_Tactic_Do_doNotDup(
                            v___x_7689_,
                            v_val_7683_,
                            v_elimTrivial_7653_,
                        );
                        if v___x_7690_ == 0 {
                            v___x_7691_ = l_Lean_LocalDecl_fvarId(v_val_7675_);
                            v___x_7692_ = l_Lean_mkFVar(v___x_7691_);
                            v___x_7693_ = lean_array_push(v_fst_7676_, v___x_7692_);
                            v___x_7694_ = lean_array_push(v_snd_7677_, v_val_7683_);
                            if v_isShared_7680_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7679_, 1, v___x_7694_);
                                crate::leanh::lean_ctor_set(v___x_7679_, 0, v___x_7693_);
                                v___x_7696_ = v___x_7679_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7697_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7697_, 0, v___x_7693_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7697_, 1, v___x_7694_);
                                v___x_7696_ = v_reuseFailAlloc_7697_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7683_);
                            if v_isShared_7680_ == 0 {
                                v___x_7699_ = v___x_7679_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7700_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7700_, 0, v_fst_7676_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7700_, 1, v_snd_7677_);
                                v___x_7699_ = v_reuseFailAlloc_7700_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7684_);
                        crate::leanh::lean_dec(v_val_7683_);
                        if v_isShared_7680_ == 0 {
                            v___x_7702_ = v___x_7679_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7703_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7703_, 0, v_fst_7676_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7703_, 1, v_snd_7677_);
                            v___x_7702_ = v_reuseFailAlloc_7703_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7682_);
                    if v_isShared_7680_ == 0 {
                        v___x_7705_ = v___x_7679_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7706_, 0, v_fst_7676_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7706_, 1, v_snd_7677_);
                        v___x_7705_ = v_reuseFailAlloc_7706_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_a_7667_ = v___x_7696_;
                state = 2;
                continue;
            }
            6 => {
                v_a_7667_ = v___x_7699_;
                state = 2;
                continue;
            }
            7 => {
                v_a_7667_ = v___x_7702_;
                state = 2;
                continue;
            }
            8 => {
                v_a_7667_ = v___x_7705_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_elimTrivial_7710_: *mut crate::leanh::LeanObject,
    mut v_as_7711_: *mut crate::leanh::LeanObject,
    mut v_sz_7712_: *mut crate::leanh::LeanObject,
    mut v_i_7713_: *mut crate::leanh::LeanObject,
    mut v_b_7714_: *mut crate::leanh::LeanObject,
    mut v___y_7715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_7716_: u8 = 0;
    let mut v_sz_boxed_7717_: usize = 0;
    let mut v_i_boxed_7718_: usize = 0;
    let mut v_res_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7716_ = (crate::leanh::lean_unbox(v_elimTrivial_7710_) as u8);
    v_sz_boxed_7717_ = crate::leanh::lean_unbox_usize(v_sz_7712_);
    crate::leanh::lean_dec(v_sz_7712_);
    v_i_boxed_7718_ = crate::leanh::lean_unbox_usize(v_i_7713_);
    crate::leanh::lean_dec(v_i_7713_);
    v_res_7719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_7716_, v_as_7711_, v_sz_boxed_7717_, v_i_boxed_7718_, v_b_7714_);
    crate::leanh::lean_dec_ref(v_as_7711_);
    return v_res_7719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(
    mut v_elimTrivial_7720_: u8,
    mut v_as_7721_: *mut crate::leanh::LeanObject,
    mut v_sz_7722_: usize,
    mut v_i_7723_: usize,
    mut v_b_7724_: *mut crate::leanh::LeanObject,
    mut v___y_7725_: *mut crate::leanh::LeanObject,
    mut v___y_7726_: *mut crate::leanh::LeanObject,
    mut v___y_7727_: *mut crate::leanh::LeanObject,
    mut v___y_7728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7730_: u8 = 0;
    let mut v___x_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7735_: u8 = 0;
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: usize = 0;
    let mut v___x_7742_: usize = 0;
    let mut v___x_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7751_: u8 = 0;
    let mut v___x_7752_: u8 = 0;
    let mut v___x_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: u8 = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7778_: u8 = 0;
    let mut v_isSharedCheck_7779_: u8 = 0;
    let mut v_unused_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7730_ = lean_usize_dec_lt(v_i_7723_, v_sz_7722_);
                if v___x_7730_ == 0 {
                    v___x_7731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7731_, 0, v_b_7724_);
                    return v___x_7731_;
                } else {
                    v_snd_7732_ = crate::leanh::lean_ctor_get(v_b_7724_, 1);
                    v_isSharedCheck_7779_ = (!crate::leanh::lean_is_exclusive(v_b_7724_)) as u8;
                    if v_isSharedCheck_7779_ == 0 {
                        v_unused_7780_ = crate::leanh::lean_ctor_get(v_b_7724_, 0);
                        crate::leanh::lean_dec(v_unused_7780_);
                        v___x_7734_ = v_b_7724_;
                        v_isShared_7735_ = v_isSharedCheck_7779_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7732_);
                        crate::leanh::lean_dec(v_b_7724_);
                        v___x_7734_ = crate::leanh::lean_box(0);
                        v_isShared_7735_ = v_isSharedCheck_7779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7736_ = crate::leanh::lean_box(0);
                v_a_7745_ = lean_array_uget_borrowed(v_as_7721_, v_i_7723_);
                if crate::leanh::lean_obj_tag(v_a_7745_) == 0 {
                    v_a_7738_ = v_snd_7732_;
                    state = 2;
                    continue;
                } else {
                    v_val_7746_ = crate::leanh::lean_ctor_get(v_a_7745_, 0);
                    v_fst_7747_ = crate::leanh::lean_ctor_get(v_snd_7732_, 0);
                    v_snd_7748_ = crate::leanh::lean_ctor_get(v_snd_7732_, 1);
                    v_isSharedCheck_7778_ = (!crate::leanh::lean_is_exclusive(v_snd_7732_)) as u8;
                    if v_isSharedCheck_7778_ == 0 {
                        v___x_7750_ = v_snd_7732_;
                        v_isShared_7751_ = v_isSharedCheck_7778_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7748_);
                        crate::leanh::lean_inc(v_fst_7747_);
                        crate::leanh::lean_dec(v_snd_7732_);
                        v___x_7750_ = crate::leanh::lean_box(0);
                        v_isShared_7751_ = v_isSharedCheck_7778_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7734_, 1, v_a_7738_);
                    crate::leanh::lean_ctor_set(v___x_7734_, 0, v___x_7736_);
                    v___x_7740_ = v___x_7734_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7744_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7744_, 0, v___x_7736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7744_, 1, v_a_7738_);
                    v___x_7740_ = v_reuseFailAlloc_7744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7741_ = 1usize;
                v___x_7742_ = lean_usize_add(v_i_7723_, v___x_7741_);
                v___x_7743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_7720_, v_as_7721_, v_sz_7722_, v___x_7742_, v___x_7740_);
                return v___x_7743_;
            }
            4 => {
                v___x_7752_ = 0;
                v___x_7753_ = l_Lean_LocalDecl_value_x3f(v_val_7746_, v___x_7752_);
                if crate::leanh::lean_obj_tag(v___x_7753_) == 1 {
                    v_val_7754_ = crate::leanh::lean_ctor_get(v___x_7753_, 0);
                    crate::leanh::lean_inc(v_val_7754_);
                    crate::leanh::lean_dec_ref_known(v___x_7753_, 1);
                    v___x_7755_ = l_Lean_LocalDecl_type(v_val_7746_);
                    if crate::leanh::lean_obj_tag(v___x_7755_) == 10 {
                        v_data_7756_ = crate::leanh::lean_ctor_get(v___x_7755_, 0);
                        crate::leanh::lean_inc(v_data_7756_);
                        crate::leanh::lean_dec_ref_known(v___x_7755_, 2);
                        v___x_7757_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7758_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7759_ = l_Lean_KVMap_getNat(v_data_7756_, v___x_7757_, v___x_7758_);
                        crate::leanh::lean_dec(v_data_7756_);
                        v___x_7760_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7759_);
                        crate::leanh::lean_dec(v___x_7759_);
                        v___x_7761_ = l_Lean_Elab_Tactic_Do_doNotDup(
                            v___x_7760_,
                            v_val_7754_,
                            v_elimTrivial_7720_,
                        );
                        if v___x_7761_ == 0 {
                            v___x_7762_ = l_Lean_LocalDecl_fvarId(v_val_7746_);
                            v___x_7763_ = l_Lean_mkFVar(v___x_7762_);
                            v___x_7764_ = lean_array_push(v_fst_7747_, v___x_7763_);
                            v___x_7765_ = lean_array_push(v_snd_7748_, v_val_7754_);
                            if v_isShared_7751_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7750_, 1, v___x_7765_);
                                crate::leanh::lean_ctor_set(v___x_7750_, 0, v___x_7764_);
                                v___x_7767_ = v___x_7750_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7768_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7768_, 0, v___x_7764_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7768_, 1, v___x_7765_);
                                v___x_7767_ = v_reuseFailAlloc_7768_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7754_);
                            if v_isShared_7751_ == 0 {
                                v___x_7770_ = v___x_7750_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7771_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7771_, 0, v_fst_7747_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7771_, 1, v_snd_7748_);
                                v___x_7770_ = v_reuseFailAlloc_7771_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7755_);
                        crate::leanh::lean_dec(v_val_7754_);
                        if v_isShared_7751_ == 0 {
                            v___x_7773_ = v___x_7750_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7774_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7774_, 0, v_fst_7747_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7774_, 1, v_snd_7748_);
                            v___x_7773_ = v_reuseFailAlloc_7774_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7753_);
                    if v_isShared_7751_ == 0 {
                        v___x_7776_ = v___x_7750_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7777_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7777_, 0, v_fst_7747_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7777_, 1, v_snd_7748_);
                        v___x_7776_ = v_reuseFailAlloc_7777_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_a_7738_ = v___x_7767_;
                state = 2;
                continue;
            }
            6 => {
                v_a_7738_ = v___x_7770_;
                state = 2;
                continue;
            }
            7 => {
                v_a_7738_ = v___x_7773_;
                state = 2;
                continue;
            }
            8 => {
                v_a_7738_ = v___x_7776_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(
    mut v_elimTrivial_7781_: *mut crate::leanh::LeanObject,
    mut v_as_7782_: *mut crate::leanh::LeanObject,
    mut v_sz_7783_: *mut crate::leanh::LeanObject,
    mut v_i_7784_: *mut crate::leanh::LeanObject,
    mut v_b_7785_: *mut crate::leanh::LeanObject,
    mut v___y_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
    mut v___y_7789_: *mut crate::leanh::LeanObject,
    mut v___y_7790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_7791_: u8 = 0;
    let mut v_sz_boxed_7792_: usize = 0;
    let mut v_i_boxed_7793_: usize = 0;
    let mut v_res_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7791_ = (crate::leanh::lean_unbox(v_elimTrivial_7781_) as u8);
    v_sz_boxed_7792_ = crate::leanh::lean_unbox_usize(v_sz_7783_);
    crate::leanh::lean_dec(v_sz_7783_);
    v_i_boxed_7793_ = crate::leanh::lean_unbox_usize(v_i_7784_);
    crate::leanh::lean_dec(v_i_7784_);
    v_res_7794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_7791_, v_as_7782_, v_sz_boxed_7792_, v_i_boxed_7793_, v_b_7785_, v___y_7786_, v___y_7787_, v___y_7788_, v___y_7789_);
    crate::leanh::lean_dec(v___y_7789_);
    crate::leanh::lean_dec_ref(v___y_7788_);
    crate::leanh::lean_dec(v___y_7787_);
    crate::leanh::lean_dec_ref(v___y_7786_);
    crate::leanh::lean_dec_ref(v_as_7782_);
    return v_res_7794_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(
    mut v_elimTrivial_7795_: u8,
    mut v_as_7796_: *mut crate::leanh::LeanObject,
    mut v_sz_7797_: usize,
    mut v_i_7798_: usize,
    mut v_b_7799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7801_: u8 = 0;
    let mut v___x_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7806_: u8 = 0;
    let mut v___x_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: usize = 0;
    let mut v___x_7813_: usize = 0;
    let mut v_reuseFailAlloc_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7822_: u8 = 0;
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: u8 = 0;
    let mut v___x_7832_: u8 = 0;
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7849_: u8 = 0;
    let mut v_isSharedCheck_7850_: u8 = 0;
    let mut v_unused_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7801_ = lean_usize_dec_lt(v_i_7798_, v_sz_7797_);
                if v___x_7801_ == 0 {
                    v___x_7802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7802_, 0, v_b_7799_);
                    return v___x_7802_;
                } else {
                    v_snd_7803_ = crate::leanh::lean_ctor_get(v_b_7799_, 1);
                    v_isSharedCheck_7850_ = (!crate::leanh::lean_is_exclusive(v_b_7799_)) as u8;
                    if v_isSharedCheck_7850_ == 0 {
                        v_unused_7851_ = crate::leanh::lean_ctor_get(v_b_7799_, 0);
                        crate::leanh::lean_dec(v_unused_7851_);
                        v___x_7805_ = v_b_7799_;
                        v_isShared_7806_ = v_isSharedCheck_7850_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7803_);
                        crate::leanh::lean_dec(v_b_7799_);
                        v___x_7805_ = crate::leanh::lean_box(0);
                        v_isShared_7806_ = v_isSharedCheck_7850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7807_ = crate::leanh::lean_box(0);
                v_a_7816_ = lean_array_uget_borrowed(v_as_7796_, v_i_7798_);
                if crate::leanh::lean_obj_tag(v_a_7816_) == 0 {
                    v_a_7809_ = v_snd_7803_;
                    state = 2;
                    continue;
                } else {
                    v_val_7817_ = crate::leanh::lean_ctor_get(v_a_7816_, 0);
                    v_fst_7818_ = crate::leanh::lean_ctor_get(v_snd_7803_, 0);
                    v_snd_7819_ = crate::leanh::lean_ctor_get(v_snd_7803_, 1);
                    v_isSharedCheck_7849_ = (!crate::leanh::lean_is_exclusive(v_snd_7803_)) as u8;
                    if v_isSharedCheck_7849_ == 0 {
                        v___x_7821_ = v_snd_7803_;
                        v_isShared_7822_ = v_isSharedCheck_7849_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7819_);
                        crate::leanh::lean_inc(v_fst_7818_);
                        crate::leanh::lean_dec(v_snd_7803_);
                        v___x_7821_ = crate::leanh::lean_box(0);
                        v_isShared_7822_ = v_isSharedCheck_7849_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7805_, 1, v_a_7809_);
                    crate::leanh::lean_ctor_set(v___x_7805_, 0, v___x_7807_);
                    v___x_7811_ = v___x_7805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7815_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7815_, 0, v___x_7807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7815_, 1, v_a_7809_);
                    v___x_7811_ = v_reuseFailAlloc_7815_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7812_ = 1usize;
                v___x_7813_ = lean_usize_add(v_i_7798_, v___x_7812_);
                v_i_7798_ = v___x_7813_;
                v_b_7799_ = v___x_7811_;
                state = 0;
                continue;
            }
            4 => {
                v___x_7823_ = 0;
                v___x_7824_ = l_Lean_LocalDecl_value_x3f(v_val_7817_, v___x_7823_);
                if crate::leanh::lean_obj_tag(v___x_7824_) == 1 {
                    v_val_7825_ = crate::leanh::lean_ctor_get(v___x_7824_, 0);
                    crate::leanh::lean_inc(v_val_7825_);
                    crate::leanh::lean_dec_ref_known(v___x_7824_, 1);
                    v___x_7826_ = l_Lean_LocalDecl_type(v_val_7817_);
                    if crate::leanh::lean_obj_tag(v___x_7826_) == 10 {
                        v_data_7827_ = crate::leanh::lean_ctor_get(v___x_7826_, 0);
                        crate::leanh::lean_inc(v_data_7827_);
                        crate::leanh::lean_dec_ref_known(v___x_7826_, 2);
                        v___x_7828_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7829_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7830_ = l_Lean_KVMap_getNat(v_data_7827_, v___x_7828_, v___x_7829_);
                        crate::leanh::lean_dec(v_data_7827_);
                        v___x_7831_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7830_);
                        crate::leanh::lean_dec(v___x_7830_);
                        v___x_7832_ = l_Lean_Elab_Tactic_Do_doNotDup(
                            v___x_7831_,
                            v_val_7825_,
                            v_elimTrivial_7795_,
                        );
                        if v___x_7832_ == 0 {
                            v___x_7833_ = l_Lean_LocalDecl_fvarId(v_val_7817_);
                            v___x_7834_ = l_Lean_mkFVar(v___x_7833_);
                            v___x_7835_ = lean_array_push(v_fst_7818_, v___x_7834_);
                            v___x_7836_ = lean_array_push(v_snd_7819_, v_val_7825_);
                            if v_isShared_7822_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7821_, 1, v___x_7836_);
                                crate::leanh::lean_ctor_set(v___x_7821_, 0, v___x_7835_);
                                v___x_7838_ = v___x_7821_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7839_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7839_, 0, v___x_7835_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7839_, 1, v___x_7836_);
                                v___x_7838_ = v_reuseFailAlloc_7839_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7825_);
                            if v_isShared_7822_ == 0 {
                                v___x_7841_ = v___x_7821_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7842_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7842_, 0, v_fst_7818_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7842_, 1, v_snd_7819_);
                                v___x_7841_ = v_reuseFailAlloc_7842_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7826_);
                        crate::leanh::lean_dec(v_val_7825_);
                        if v_isShared_7822_ == 0 {
                            v___x_7844_ = v___x_7821_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7845_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7845_, 0, v_fst_7818_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7845_, 1, v_snd_7819_);
                            v___x_7844_ = v_reuseFailAlloc_7845_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7824_);
                    if v_isShared_7822_ == 0 {
                        v___x_7847_ = v___x_7821_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_fst_7818_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7848_, 1, v_snd_7819_);
                        v___x_7847_ = v_reuseFailAlloc_7848_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_a_7809_ = v___x_7838_;
                state = 2;
                continue;
            }
            6 => {
                v_a_7809_ = v___x_7841_;
                state = 2;
                continue;
            }
            7 => {
                v_a_7809_ = v___x_7844_;
                state = 2;
                continue;
            }
            8 => {
                v_a_7809_ = v___x_7847_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(
    mut v_elimTrivial_7852_: *mut crate::leanh::LeanObject,
    mut v_as_7853_: *mut crate::leanh::LeanObject,
    mut v_sz_7854_: *mut crate::leanh::LeanObject,
    mut v_i_7855_: *mut crate::leanh::LeanObject,
    mut v_b_7856_: *mut crate::leanh::LeanObject,
    mut v___y_7857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_7858_: u8 = 0;
    let mut v_sz_boxed_7859_: usize = 0;
    let mut v_i_boxed_7860_: usize = 0;
    let mut v_res_7861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7858_ = (crate::leanh::lean_unbox(v_elimTrivial_7852_) as u8);
    v_sz_boxed_7859_ = crate::leanh::lean_unbox_usize(v_sz_7854_);
    crate::leanh::lean_dec(v_sz_7854_);
    v_i_boxed_7860_ = crate::leanh::lean_unbox_usize(v_i_7855_);
    crate::leanh::lean_dec(v_i_7855_);
    v_res_7861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_7858_, v_as_7853_, v_sz_boxed_7859_, v_i_boxed_7860_, v_b_7856_);
    crate::leanh::lean_dec_ref(v_as_7853_);
    return v_res_7861_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(
    mut v_elimTrivial_7862_: u8,
    mut v_as_7863_: *mut crate::leanh::LeanObject,
    mut v_sz_7864_: usize,
    mut v_i_7865_: usize,
    mut v_b_7866_: *mut crate::leanh::LeanObject,
    mut v___y_7867_: *mut crate::leanh::LeanObject,
    mut v___y_7868_: *mut crate::leanh::LeanObject,
    mut v___y_7869_: *mut crate::leanh::LeanObject,
    mut v___y_7870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7872_: u8 = 0;
    let mut v___x_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7877_: u8 = 0;
    let mut v___x_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: usize = 0;
    let mut v___x_7884_: usize = 0;
    let mut v___x_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7893_: u8 = 0;
    let mut v___x_7894_: u8 = 0;
    let mut v___x_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: u8 = 0;
    let mut v___x_7903_: u8 = 0;
    let mut v___x_7904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7920_: u8 = 0;
    let mut v_isSharedCheck_7921_: u8 = 0;
    let mut v_unused_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7872_ = lean_usize_dec_lt(v_i_7865_, v_sz_7864_);
                if v___x_7872_ == 0 {
                    v___x_7873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7873_, 0, v_b_7866_);
                    return v___x_7873_;
                } else {
                    v_snd_7874_ = crate::leanh::lean_ctor_get(v_b_7866_, 1);
                    v_isSharedCheck_7921_ = (!crate::leanh::lean_is_exclusive(v_b_7866_)) as u8;
                    if v_isSharedCheck_7921_ == 0 {
                        v_unused_7922_ = crate::leanh::lean_ctor_get(v_b_7866_, 0);
                        crate::leanh::lean_dec(v_unused_7922_);
                        v___x_7876_ = v_b_7866_;
                        v_isShared_7877_ = v_isSharedCheck_7921_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7874_);
                        crate::leanh::lean_dec(v_b_7866_);
                        v___x_7876_ = crate::leanh::lean_box(0);
                        v_isShared_7877_ = v_isSharedCheck_7921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7878_ = crate::leanh::lean_box(0);
                v_a_7887_ = lean_array_uget_borrowed(v_as_7863_, v_i_7865_);
                if crate::leanh::lean_obj_tag(v_a_7887_) == 0 {
                    v_a_7880_ = v_snd_7874_;
                    state = 2;
                    continue;
                } else {
                    v_val_7888_ = crate::leanh::lean_ctor_get(v_a_7887_, 0);
                    v_fst_7889_ = crate::leanh::lean_ctor_get(v_snd_7874_, 0);
                    v_snd_7890_ = crate::leanh::lean_ctor_get(v_snd_7874_, 1);
                    v_isSharedCheck_7920_ = (!crate::leanh::lean_is_exclusive(v_snd_7874_)) as u8;
                    if v_isSharedCheck_7920_ == 0 {
                        v___x_7892_ = v_snd_7874_;
                        v_isShared_7893_ = v_isSharedCheck_7920_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7890_);
                        crate::leanh::lean_inc(v_fst_7889_);
                        crate::leanh::lean_dec(v_snd_7874_);
                        v___x_7892_ = crate::leanh::lean_box(0);
                        v_isShared_7893_ = v_isSharedCheck_7920_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7877_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7876_, 1, v_a_7880_);
                    crate::leanh::lean_ctor_set(v___x_7876_, 0, v___x_7878_);
                    v___x_7882_ = v___x_7876_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 0, v___x_7878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 1, v_a_7880_);
                    v___x_7882_ = v_reuseFailAlloc_7886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7883_ = 1usize;
                v___x_7884_ = lean_usize_add(v_i_7865_, v___x_7883_);
                v___x_7885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_7862_, v_as_7863_, v_sz_7864_, v___x_7884_, v___x_7882_);
                return v___x_7885_;
            }
            4 => {
                v___x_7894_ = 0;
                v___x_7895_ = l_Lean_LocalDecl_value_x3f(v_val_7888_, v___x_7894_);
                if crate::leanh::lean_obj_tag(v___x_7895_) == 1 {
                    v_val_7896_ = crate::leanh::lean_ctor_get(v___x_7895_, 0);
                    crate::leanh::lean_inc(v_val_7896_);
                    crate::leanh::lean_dec_ref_known(v___x_7895_, 1);
                    v___x_7897_ = l_Lean_LocalDecl_type(v_val_7888_);
                    if crate::leanh::lean_obj_tag(v___x_7897_) == 10 {
                        v_data_7898_ = crate::leanh::lean_ctor_get(v___x_7897_, 0);
                        crate::leanh::lean_inc(v_data_7898_);
                        crate::leanh::lean_dec_ref_known(v___x_7897_, 2);
                        v___x_7899_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7900_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7901_ = l_Lean_KVMap_getNat(v_data_7898_, v___x_7899_, v___x_7900_);
                        crate::leanh::lean_dec(v_data_7898_);
                        v___x_7902_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7901_);
                        crate::leanh::lean_dec(v___x_7901_);
                        v___x_7903_ = l_Lean_Elab_Tactic_Do_doNotDup(
                            v___x_7902_,
                            v_val_7896_,
                            v_elimTrivial_7862_,
                        );
                        if v___x_7903_ == 0 {
                            v___x_7904_ = l_Lean_LocalDecl_fvarId(v_val_7888_);
                            v___x_7905_ = l_Lean_mkFVar(v___x_7904_);
                            v___x_7906_ = lean_array_push(v_fst_7889_, v___x_7905_);
                            v___x_7907_ = lean_array_push(v_snd_7890_, v_val_7896_);
                            if v_isShared_7893_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7892_, 1, v___x_7907_);
                                crate::leanh::lean_ctor_set(v___x_7892_, 0, v___x_7906_);
                                v___x_7909_ = v___x_7892_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7910_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7910_, 0, v___x_7906_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7910_, 1, v___x_7907_);
                                v___x_7909_ = v_reuseFailAlloc_7910_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7896_);
                            if v_isShared_7893_ == 0 {
                                v___x_7912_ = v___x_7892_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7913_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7913_, 0, v_fst_7889_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7913_, 1, v_snd_7890_);
                                v___x_7912_ = v_reuseFailAlloc_7913_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7897_);
                        crate::leanh::lean_dec(v_val_7896_);
                        if v_isShared_7893_ == 0 {
                            v___x_7915_ = v___x_7892_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7916_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7916_, 0, v_fst_7889_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7916_, 1, v_snd_7890_);
                            v___x_7915_ = v_reuseFailAlloc_7916_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7895_);
                    if v_isShared_7893_ == 0 {
                        v___x_7918_ = v___x_7892_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7919_, 0, v_fst_7889_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7919_, 1, v_snd_7890_);
                        v___x_7918_ = v_reuseFailAlloc_7919_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_a_7880_ = v___x_7909_;
                state = 2;
                continue;
            }
            6 => {
                v_a_7880_ = v___x_7912_;
                state = 2;
                continue;
            }
            7 => {
                v_a_7880_ = v___x_7915_;
                state = 2;
                continue;
            }
            8 => {
                v_a_7880_ = v___x_7918_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(
    mut v_elimTrivial_7923_: *mut crate::leanh::LeanObject,
    mut v_as_7924_: *mut crate::leanh::LeanObject,
    mut v_sz_7925_: *mut crate::leanh::LeanObject,
    mut v_i_7926_: *mut crate::leanh::LeanObject,
    mut v_b_7927_: *mut crate::leanh::LeanObject,
    mut v___y_7928_: *mut crate::leanh::LeanObject,
    mut v___y_7929_: *mut crate::leanh::LeanObject,
    mut v___y_7930_: *mut crate::leanh::LeanObject,
    mut v___y_7931_: *mut crate::leanh::LeanObject,
    mut v___y_7932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_7933_: u8 = 0;
    let mut v_sz_boxed_7934_: usize = 0;
    let mut v_i_boxed_7935_: usize = 0;
    let mut v_res_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7933_ = (crate::leanh::lean_unbox(v_elimTrivial_7923_) as u8);
    v_sz_boxed_7934_ = crate::leanh::lean_unbox_usize(v_sz_7925_);
    crate::leanh::lean_dec(v_sz_7925_);
    v_i_boxed_7935_ = crate::leanh::lean_unbox_usize(v_i_7926_);
    crate::leanh::lean_dec(v_i_7926_);
    v_res_7936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_7933_, v_as_7924_, v_sz_boxed_7934_, v_i_boxed_7935_, v_b_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_);
    crate::leanh::lean_dec(v___y_7931_);
    crate::leanh::lean_dec_ref(v___y_7930_);
    crate::leanh::lean_dec(v___y_7929_);
    crate::leanh::lean_dec_ref(v___y_7928_);
    crate::leanh::lean_dec_ref(v_as_7924_);
    return v_res_7936_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(
    mut v_init_7937_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_7938_: u8,
    mut v_n_7939_: *mut crate::leanh::LeanObject,
    mut v_b_7940_: *mut crate::leanh::LeanObject,
    mut v___y_7941_: *mut crate::leanh::LeanObject,
    mut v___y_7942_: *mut crate::leanh::LeanObject,
    mut v___y_7943_: *mut crate::leanh::LeanObject,
    mut v___y_7944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7949_: usize = 0;
    let mut v___x_7950_: usize = 0;
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7955_: u8 = 0;
    let mut v_fst_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7966_: u8 = 0;
    let mut v_a_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v___x_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7974_: u8 = 0;
    let mut v_vs_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7978_: usize = 0;
    let mut v___x_7979_: usize = 0;
    let mut v___x_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7984_: u8 = 0;
    let mut v_fst_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7995_: u8 = 0;
    let mut v_a_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_7939_) == 0 {
                    v_cs_7946_ = crate::leanh::lean_ctor_get(v_n_7939_, 0);
                    v___x_7947_ = crate::leanh::lean_box(0);
                    v___x_7948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7948_, 0, v___x_7947_);
                    crate::leanh::lean_ctor_set(v___x_7948_, 1, v_b_7940_);
                    v_sz_7949_ = lean_array_size(v_cs_7946_);
                    v___x_7950_ = 0usize;
                    v___x_7951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_7937_, v_elimTrivial_7938_, v_cs_7946_, v_sz_7949_, v___x_7950_, v___x_7948_, v___y_7941_, v___y_7942_, v___y_7943_, v___y_7944_);
                    if crate::leanh::lean_obj_tag(v___x_7951_) == 0 {
                        v_a_7952_ = crate::leanh::lean_ctor_get(v___x_7951_, 0);
                        v_isSharedCheck_7966_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7951_)) as u8;
                        if v_isSharedCheck_7966_ == 0 {
                            v___x_7954_ = v___x_7951_;
                            v_isShared_7955_ = v_isSharedCheck_7966_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7952_);
                            crate::leanh::lean_dec(v___x_7951_);
                            v___x_7954_ = crate::leanh::lean_box(0);
                            v_isShared_7955_ = v_isSharedCheck_7966_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7967_ = crate::leanh::lean_ctor_get(v___x_7951_, 0);
                        v_isSharedCheck_7974_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7951_)) as u8;
                        if v_isSharedCheck_7974_ == 0 {
                            v___x_7969_ = v___x_7951_;
                            v_isShared_7970_ = v_isSharedCheck_7974_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7967_);
                            crate::leanh::lean_dec(v___x_7951_);
                            v___x_7969_ = crate::leanh::lean_box(0);
                            v_isShared_7970_ = v_isSharedCheck_7974_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_7975_ = crate::leanh::lean_ctor_get(v_n_7939_, 0);
                    v___x_7976_ = crate::leanh::lean_box(0);
                    v___x_7977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7977_, 0, v___x_7976_);
                    crate::leanh::lean_ctor_set(v___x_7977_, 1, v_b_7940_);
                    v_sz_7978_ = lean_array_size(v_vs_7975_);
                    v___x_7979_ = 0usize;
                    v___x_7980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_7938_, v_vs_7975_, v_sz_7978_, v___x_7979_, v___x_7977_, v___y_7941_, v___y_7942_, v___y_7943_, v___y_7944_);
                    if crate::leanh::lean_obj_tag(v___x_7980_) == 0 {
                        v_a_7981_ = crate::leanh::lean_ctor_get(v___x_7980_, 0);
                        v_isSharedCheck_7995_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7980_)) as u8;
                        if v_isSharedCheck_7995_ == 0 {
                            v___x_7983_ = v___x_7980_;
                            v_isShared_7984_ = v_isSharedCheck_7995_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7981_);
                            crate::leanh::lean_dec(v___x_7980_);
                            v___x_7983_ = crate::leanh::lean_box(0);
                            v_isShared_7984_ = v_isSharedCheck_7995_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_7996_ = crate::leanh::lean_ctor_get(v___x_7980_, 0);
                        v_isSharedCheck_8003_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7980_)) as u8;
                        if v_isSharedCheck_8003_ == 0 {
                            v___x_7998_ = v___x_7980_;
                            v_isShared_7999_ = v_isSharedCheck_8003_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7996_);
                            crate::leanh::lean_dec(v___x_7980_);
                            v___x_7998_ = crate::leanh::lean_box(0);
                            v_isShared_7999_ = v_isSharedCheck_8003_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_7956_ = crate::leanh::lean_ctor_get(v_a_7952_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7956_) == 0 {
                    v_snd_7957_ = crate::leanh::lean_ctor_get(v_a_7952_, 1);
                    crate::leanh::lean_inc(v_snd_7957_);
                    crate::leanh::lean_dec(v_a_7952_);
                    v___x_7958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7958_, 0, v_snd_7957_);
                    if v_isShared_7955_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7954_, 0, v___x_7958_);
                        v___x_7960_ = v___x_7954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7961_, 0, v___x_7958_);
                        v___x_7960_ = v_reuseFailAlloc_7961_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7956_);
                    crate::leanh::lean_dec(v_a_7952_);
                    v_val_7962_ = crate::leanh::lean_ctor_get(v_fst_7956_, 0);
                    crate::leanh::lean_inc(v_val_7962_);
                    crate::leanh::lean_dec_ref_known(v_fst_7956_, 1);
                    if v_isShared_7955_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7954_, 0, v_val_7962_);
                        v___x_7964_ = v___x_7954_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7965_, 0, v_val_7962_);
                        v___x_7964_ = v_reuseFailAlloc_7965_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7960_;
            }
            3 => {
                return v___x_7964_;
            }
            4 => {
                if v_isShared_7970_ == 0 {
                    v___x_7972_ = v___x_7969_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7973_, 0, v_a_7967_);
                    v___x_7972_ = v_reuseFailAlloc_7973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7972_;
            }
            6 => {
                v_fst_7985_ = crate::leanh::lean_ctor_get(v_a_7981_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7985_) == 0 {
                    v_snd_7986_ = crate::leanh::lean_ctor_get(v_a_7981_, 1);
                    crate::leanh::lean_inc(v_snd_7986_);
                    crate::leanh::lean_dec(v_a_7981_);
                    v___x_7987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7987_, 0, v_snd_7986_);
                    if v_isShared_7984_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7983_, 0, v___x_7987_);
                        v___x_7989_ = v___x_7983_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7990_, 0, v___x_7987_);
                        v___x_7989_ = v_reuseFailAlloc_7990_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7985_);
                    crate::leanh::lean_dec(v_a_7981_);
                    v_val_7991_ = crate::leanh::lean_ctor_get(v_fst_7985_, 0);
                    crate::leanh::lean_inc(v_val_7991_);
                    crate::leanh::lean_dec_ref_known(v_fst_7985_, 1);
                    if v_isShared_7984_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7983_, 0, v_val_7991_);
                        v___x_7993_ = v___x_7983_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7994_, 0, v_val_7991_);
                        v___x_7993_ = v_reuseFailAlloc_7994_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_7989_;
            }
            8 => {
                return v___x_7993_;
            }
            9 => {
                if v_isShared_7999_ == 0 {
                    v___x_8001_ = v___x_7998_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8002_, 0, v_a_7996_);
                    v___x_8001_ = v_reuseFailAlloc_8002_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(
    mut v_init_8004_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8005_: u8,
    mut v_as_8006_: *mut crate::leanh::LeanObject,
    mut v_sz_8007_: usize,
    mut v_i_8008_: usize,
    mut v_b_8009_: *mut crate::leanh::LeanObject,
    mut v___y_8010_: *mut crate::leanh::LeanObject,
    mut v___y_8011_: *mut crate::leanh::LeanObject,
    mut v___y_8012_: *mut crate::leanh::LeanObject,
    mut v___y_8013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8015_: u8 = 0;
    let mut v___x_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8020_: u8 = 0;
    let mut v_a_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8026_: u8 = 0;
    let mut v___x_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: usize = 0;
    let mut v___x_8039_: usize = 0;
    let mut v_reuseFailAlloc_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8042_: u8 = 0;
    let mut v_a_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8046_: u8 = 0;
    let mut v___x_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8050_: u8 = 0;
    let mut v_isSharedCheck_8051_: u8 = 0;
    let mut v_unused_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8015_ = lean_usize_dec_lt(v_i_8008_, v_sz_8007_);
                if v___x_8015_ == 0 {
                    v___x_8016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8016_, 0, v_b_8009_);
                    return v___x_8016_;
                } else {
                    v_snd_8017_ = crate::leanh::lean_ctor_get(v_b_8009_, 1);
                    v_isSharedCheck_8051_ = (!crate::leanh::lean_is_exclusive(v_b_8009_)) as u8;
                    if v_isSharedCheck_8051_ == 0 {
                        v_unused_8052_ = crate::leanh::lean_ctor_get(v_b_8009_, 0);
                        crate::leanh::lean_dec(v_unused_8052_);
                        v___x_8019_ = v_b_8009_;
                        v_isShared_8020_ = v_isSharedCheck_8051_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_8017_);
                        crate::leanh::lean_dec(v_b_8009_);
                        v___x_8019_ = crate::leanh::lean_box(0);
                        v_isShared_8020_ = v_isSharedCheck_8051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_8021_ = lean_array_uget_borrowed(v_as_8006_, v_i_8008_);
                crate::leanh::lean_inc(v_snd_8017_);
                v___x_8022_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8004_, v_elimTrivial_8005_, v_a_8021_, v_snd_8017_, v___y_8010_, v___y_8011_, v___y_8012_, v___y_8013_);
                if crate::leanh::lean_obj_tag(v___x_8022_) == 0 {
                    v_a_8023_ = crate::leanh::lean_ctor_get(v___x_8022_, 0);
                    v_isSharedCheck_8042_ = (!crate::leanh::lean_is_exclusive(v___x_8022_)) as u8;
                    if v_isSharedCheck_8042_ == 0 {
                        v___x_8025_ = v___x_8022_;
                        v_isShared_8026_ = v_isSharedCheck_8042_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8023_);
                        crate::leanh::lean_dec(v___x_8022_);
                        v___x_8025_ = crate::leanh::lean_box(0);
                        v_isShared_8026_ = v_isSharedCheck_8042_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8019_);
                    crate::leanh::lean_dec(v_snd_8017_);
                    v_a_8043_ = crate::leanh::lean_ctor_get(v___x_8022_, 0);
                    v_isSharedCheck_8050_ = (!crate::leanh::lean_is_exclusive(v___x_8022_)) as u8;
                    if v_isSharedCheck_8050_ == 0 {
                        v___x_8045_ = v___x_8022_;
                        v_isShared_8046_ = v_isSharedCheck_8050_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8043_);
                        crate::leanh::lean_dec(v___x_8022_);
                        v___x_8045_ = crate::leanh::lean_box(0);
                        v_isShared_8046_ = v_isSharedCheck_8050_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_8023_) == 0 {
                    v___x_8027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8027_, 0, v_a_8023_);
                    if v_isShared_8020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8019_, 0, v___x_8027_);
                        v___x_8029_ = v___x_8019_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8033_, 0, v___x_8027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8033_, 1, v_snd_8017_);
                        v___x_8029_ = v_reuseFailAlloc_8033_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8025_);
                    crate::leanh::lean_dec(v_snd_8017_);
                    v_a_8034_ = crate::leanh::lean_ctor_get(v_a_8023_, 0);
                    crate::leanh::lean_inc(v_a_8034_);
                    crate::leanh::lean_dec_ref_known(v_a_8023_, 1);
                    v___x_8035_ = crate::leanh::lean_box(0);
                    if v_isShared_8020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8019_, 1, v_a_8034_);
                        crate::leanh::lean_ctor_set(v___x_8019_, 0, v___x_8035_);
                        v___x_8037_ = v___x_8019_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8041_, 0, v___x_8035_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8041_, 1, v_a_8034_);
                        v___x_8037_ = v_reuseFailAlloc_8041_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8025_, 0, v___x_8029_);
                    v___x_8031_ = v___x_8025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8032_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8032_, 0, v___x_8029_);
                    v___x_8031_ = v_reuseFailAlloc_8032_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8031_;
            }
            5 => {
                v___x_8038_ = 1usize;
                v___x_8039_ = lean_usize_add(v_i_8008_, v___x_8038_);
                v_i_8008_ = v___x_8039_;
                v_b_8009_ = v___x_8037_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_8046_ == 0 {
                    v___x_8048_ = v___x_8045_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8049_, 0, v_a_8043_);
                    v___x_8048_ = v_reuseFailAlloc_8049_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(
    mut v_init_8053_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8054_: *mut crate::leanh::LeanObject,
    mut v_as_8055_: *mut crate::leanh::LeanObject,
    mut v_sz_8056_: *mut crate::leanh::LeanObject,
    mut v_i_8057_: *mut crate::leanh::LeanObject,
    mut v_b_8058_: *mut crate::leanh::LeanObject,
    mut v___y_8059_: *mut crate::leanh::LeanObject,
    mut v___y_8060_: *mut crate::leanh::LeanObject,
    mut v___y_8061_: *mut crate::leanh::LeanObject,
    mut v___y_8062_: *mut crate::leanh::LeanObject,
    mut v___y_8063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8064_: u8 = 0;
    let mut v_sz_boxed_8065_: usize = 0;
    let mut v_i_boxed_8066_: usize = 0;
    let mut v_res_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8064_ = (crate::leanh::lean_unbox(v_elimTrivial_8054_) as u8);
    v_sz_boxed_8065_ = crate::leanh::lean_unbox_usize(v_sz_8056_);
    crate::leanh::lean_dec(v_sz_8056_);
    v_i_boxed_8066_ = crate::leanh::lean_unbox_usize(v_i_8057_);
    crate::leanh::lean_dec(v_i_8057_);
    v_res_8067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_8053_, v_elimTrivial_boxed_8064_, v_as_8055_, v_sz_boxed_8065_, v_i_boxed_8066_, v_b_8058_, v___y_8059_, v___y_8060_, v___y_8061_, v___y_8062_);
    crate::leanh::lean_dec(v___y_8062_);
    crate::leanh::lean_dec_ref(v___y_8061_);
    crate::leanh::lean_dec(v___y_8060_);
    crate::leanh::lean_dec_ref(v___y_8059_);
    crate::leanh::lean_dec_ref(v_as_8055_);
    crate::leanh::lean_dec_ref(v_init_8053_);
    return v_res_8067_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(
    mut v_init_8068_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8069_: *mut crate::leanh::LeanObject,
    mut v_n_8070_: *mut crate::leanh::LeanObject,
    mut v_b_8071_: *mut crate::leanh::LeanObject,
    mut v___y_8072_: *mut crate::leanh::LeanObject,
    mut v___y_8073_: *mut crate::leanh::LeanObject,
    mut v___y_8074_: *mut crate::leanh::LeanObject,
    mut v___y_8075_: *mut crate::leanh::LeanObject,
    mut v___y_8076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8077_: u8 = 0;
    let mut v_res_8078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8077_ = (crate::leanh::lean_unbox(v_elimTrivial_8069_) as u8);
    v_res_8078_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8068_, v_elimTrivial_boxed_8077_, v_n_8070_, v_b_8071_, v___y_8072_, v___y_8073_, v___y_8074_, v___y_8075_);
    crate::leanh::lean_dec(v___y_8075_);
    crate::leanh::lean_dec_ref(v___y_8074_);
    crate::leanh::lean_dec(v___y_8073_);
    crate::leanh::lean_dec_ref(v___y_8072_);
    crate::leanh::lean_dec_ref(v_n_8070_);
    crate::leanh::lean_dec_ref(v_init_8068_);
    return v_res_8078_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(
    mut v_elimTrivial_8079_: u8,
    mut v_t_8080_: *mut crate::leanh::LeanObject,
    mut v_init_8081_: *mut crate::leanh::LeanObject,
    mut v___y_8082_: *mut crate::leanh::LeanObject,
    mut v___y_8083_: *mut crate::leanh::LeanObject,
    mut v___y_8084_: *mut crate::leanh::LeanObject,
    mut v___y_8085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8093_: u8 = 0;
    let mut v_a_8094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8101_: usize = 0;
    let mut v___x_8102_: usize = 0;
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8107_: u8 = 0;
    let mut v_fst_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8117_: u8 = 0;
    let mut v_a_8118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v___x_8123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8125_: u8 = 0;
    let mut v_isSharedCheck_8126_: u8 = 0;
    let mut v_a_8127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8130_: u8 = 0;
    let mut v___x_8132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_8087_ = crate::leanh::lean_ctor_get(v_t_8080_, 0);
                v_tail_8088_ = crate::leanh::lean_ctor_get(v_t_8080_, 1);
                crate::leanh::lean_inc_ref(v_init_8081_);
                v___x_8089_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8081_, v_elimTrivial_8079_, v_root_8087_, v_init_8081_, v___y_8082_, v___y_8083_, v___y_8084_, v___y_8085_);
                crate::leanh::lean_dec_ref(v_init_8081_);
                if crate::leanh::lean_obj_tag(v___x_8089_) == 0 {
                    v_a_8090_ = crate::leanh::lean_ctor_get(v___x_8089_, 0);
                    v_isSharedCheck_8126_ = (!crate::leanh::lean_is_exclusive(v___x_8089_)) as u8;
                    if v_isSharedCheck_8126_ == 0 {
                        v___x_8092_ = v___x_8089_;
                        v_isShared_8093_ = v_isSharedCheck_8126_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8090_);
                        crate::leanh::lean_dec(v___x_8089_);
                        v___x_8092_ = crate::leanh::lean_box(0);
                        v_isShared_8093_ = v_isSharedCheck_8126_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8127_ = crate::leanh::lean_ctor_get(v___x_8089_, 0);
                    v_isSharedCheck_8134_ = (!crate::leanh::lean_is_exclusive(v___x_8089_)) as u8;
                    if v_isSharedCheck_8134_ == 0 {
                        v___x_8129_ = v___x_8089_;
                        v_isShared_8130_ = v_isSharedCheck_8134_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8127_);
                        crate::leanh::lean_dec(v___x_8089_);
                        v___x_8129_ = crate::leanh::lean_box(0);
                        v_isShared_8130_ = v_isSharedCheck_8134_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_8090_) == 0 {
                    v_a_8094_ = crate::leanh::lean_ctor_get(v_a_8090_, 0);
                    crate::leanh::lean_inc(v_a_8094_);
                    crate::leanh::lean_dec_ref_known(v_a_8090_, 1);
                    if v_isShared_8093_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8092_, 0, v_a_8094_);
                        v___x_8096_ = v___x_8092_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8097_, 0, v_a_8094_);
                        v___x_8096_ = v_reuseFailAlloc_8097_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8092_);
                    v_a_8098_ = crate::leanh::lean_ctor_get(v_a_8090_, 0);
                    crate::leanh::lean_inc(v_a_8098_);
                    crate::leanh::lean_dec_ref_known(v_a_8090_, 1);
                    v___x_8099_ = crate::leanh::lean_box(0);
                    v___x_8100_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8100_, 0, v___x_8099_);
                    crate::leanh::lean_ctor_set(v___x_8100_, 1, v_a_8098_);
                    v_sz_8101_ = lean_array_size(v_tail_8088_);
                    v___x_8102_ = 0usize;
                    v___x_8103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_8079_, v_tail_8088_, v_sz_8101_, v___x_8102_, v___x_8100_, v___y_8082_, v___y_8083_, v___y_8084_, v___y_8085_);
                    if crate::leanh::lean_obj_tag(v___x_8103_) == 0 {
                        v_a_8104_ = crate::leanh::lean_ctor_get(v___x_8103_, 0);
                        v_isSharedCheck_8117_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8103_)) as u8;
                        if v_isSharedCheck_8117_ == 0 {
                            v___x_8106_ = v___x_8103_;
                            v_isShared_8107_ = v_isSharedCheck_8117_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8104_);
                            crate::leanh::lean_dec(v___x_8103_);
                            v___x_8106_ = crate::leanh::lean_box(0);
                            v_isShared_8107_ = v_isSharedCheck_8117_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_8118_ = crate::leanh::lean_ctor_get(v___x_8103_, 0);
                        v_isSharedCheck_8125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8103_)) as u8;
                        if v_isSharedCheck_8125_ == 0 {
                            v___x_8120_ = v___x_8103_;
                            v_isShared_8121_ = v_isSharedCheck_8125_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8118_);
                            crate::leanh::lean_dec(v___x_8103_);
                            v___x_8120_ = crate::leanh::lean_box(0);
                            v_isShared_8121_ = v_isSharedCheck_8125_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8096_;
            }
            3 => {
                v_fst_8108_ = crate::leanh::lean_ctor_get(v_a_8104_, 0);
                if crate::leanh::lean_obj_tag(v_fst_8108_) == 0 {
                    v_snd_8109_ = crate::leanh::lean_ctor_get(v_a_8104_, 1);
                    crate::leanh::lean_inc(v_snd_8109_);
                    crate::leanh::lean_dec(v_a_8104_);
                    if v_isShared_8107_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8106_, 0, v_snd_8109_);
                        v___x_8111_ = v___x_8106_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 0, v_snd_8109_);
                        v___x_8111_ = v_reuseFailAlloc_8112_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_8108_);
                    crate::leanh::lean_dec(v_a_8104_);
                    v_val_8113_ = crate::leanh::lean_ctor_get(v_fst_8108_, 0);
                    crate::leanh::lean_inc(v_val_8113_);
                    crate::leanh::lean_dec_ref_known(v_fst_8108_, 1);
                    if v_isShared_8107_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8106_, 0, v_val_8113_);
                        v___x_8115_ = v___x_8106_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8116_, 0, v_val_8113_);
                        v___x_8115_ = v_reuseFailAlloc_8116_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_8111_;
            }
            5 => {
                return v___x_8115_;
            }
            6 => {
                if v_isShared_8121_ == 0 {
                    v___x_8123_ = v___x_8120_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8124_, 0, v_a_8118_);
                    v___x_8123_ = v_reuseFailAlloc_8124_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8123_;
            }
            8 => {
                if v_isShared_8130_ == 0 {
                    v___x_8132_ = v___x_8129_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8133_, 0, v_a_8127_);
                    v___x_8132_ = v_reuseFailAlloc_8133_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(
    mut v_elimTrivial_8135_: *mut crate::leanh::LeanObject,
    mut v_t_8136_: *mut crate::leanh::LeanObject,
    mut v_init_8137_: *mut crate::leanh::LeanObject,
    mut v___y_8138_: *mut crate::leanh::LeanObject,
    mut v___y_8139_: *mut crate::leanh::LeanObject,
    mut v___y_8140_: *mut crate::leanh::LeanObject,
    mut v___y_8141_: *mut crate::leanh::LeanObject,
    mut v___y_8142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8143_: u8 = 0;
    let mut v_res_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8143_ = (crate::leanh::lean_unbox(v_elimTrivial_8135_) as u8);
    v_res_8144_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(
        v_elimTrivial_boxed_8143_,
        v_t_8136_,
        v_init_8137_,
        v___y_8138_,
        v___y_8139_,
        v___y_8140_,
        v___y_8141_,
    );
    crate::leanh::lean_dec(v___y_8141_);
    crate::leanh::lean_dec_ref(v___y_8140_);
    crate::leanh::lean_dec(v___y_8139_);
    crate::leanh::lean_dec_ref(v___y_8138_);
    crate::leanh::lean_dec_ref(v_t_8136_);
    return v_res_8144_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(
    mut v_as_8145_: *mut crate::leanh::LeanObject,
    mut v_sz_8146_: usize,
    mut v_i_8147_: usize,
    mut v_b_8148_: *mut crate::leanh::LeanObject,
    mut v___y_8149_: *mut crate::leanh::LeanObject,
    mut v___y_8150_: *mut crate::leanh::LeanObject,
    mut v___y_8151_: *mut crate::leanh::LeanObject,
    mut v___y_8152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8154_: u8 = 0;
    let mut v___x_8155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: usize = 0;
    let mut v___x_8161_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8154_ = lean_usize_dec_lt(v_i_8147_, v_sz_8146_);
                if v___x_8154_ == 0 {
                    v___x_8155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8155_, 0, v_b_8148_);
                    return v___x_8155_;
                } else {
                    v_a_8156_ = lean_array_uget_borrowed(v_as_8145_, v_i_8147_);
                    v___x_8157_ = l_Lean_Expr_fvarId_x21(v_a_8156_);
                    v___x_8158_ = l_Lean_MVarId_tryClear(
                        v_b_8148_,
                        v___x_8157_,
                        v___y_8149_,
                        v___y_8150_,
                        v___y_8151_,
                        v___y_8152_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8158_) == 0 {
                        v_a_8159_ = crate::leanh::lean_ctor_get(v___x_8158_, 0);
                        crate::leanh::lean_inc(v_a_8159_);
                        crate::leanh::lean_dec_ref_known(v___x_8158_, 1);
                        v___x_8160_ = 1usize;
                        v___x_8161_ = lean_usize_add(v_i_8147_, v___x_8160_);
                        v_i_8147_ = v___x_8161_;
                        v_b_8148_ = v_a_8159_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8158_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(
    mut v_as_8163_: *mut crate::leanh::LeanObject,
    mut v_sz_8164_: *mut crate::leanh::LeanObject,
    mut v_i_8165_: *mut crate::leanh::LeanObject,
    mut v_b_8166_: *mut crate::leanh::LeanObject,
    mut v___y_8167_: *mut crate::leanh::LeanObject,
    mut v___y_8168_: *mut crate::leanh::LeanObject,
    mut v___y_8169_: *mut crate::leanh::LeanObject,
    mut v___y_8170_: *mut crate::leanh::LeanObject,
    mut v___y_8171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_8172_: usize = 0;
    let mut v_i_boxed_8173_: usize = 0;
    let mut v_res_8174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8172_ = crate::leanh::lean_unbox_usize(v_sz_8164_);
    crate::leanh::lean_dec(v_sz_8164_);
    v_i_boxed_8173_ = crate::leanh::lean_unbox_usize(v_i_8165_);
    crate::leanh::lean_dec(v_i_8165_);
    v_res_8174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_8163_, v_sz_boxed_8172_, v_i_boxed_8173_, v_b_8166_, v___y_8167_, v___y_8168_, v___y_8169_, v___y_8170_);
    crate::leanh::lean_dec(v___y_8170_);
    crate::leanh::lean_dec_ref(v___y_8169_);
    crate::leanh::lean_dec(v___y_8168_);
    crate::leanh::lean_dec_ref(v___y_8167_);
    crate::leanh::lean_dec_ref(v_as_8163_);
    return v_res_8174_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(
    mut v_x_8175_: *mut crate::leanh::LeanObject,
    mut v_x_8176_: *mut crate::leanh::LeanObject,
    mut v_x_8177_: *mut crate::leanh::LeanObject,
    mut v_x_8178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_8179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_8180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8183_: u8 = 0;
    let mut v___x_8184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: u8 = 0;
    let mut v___x_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_8191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: u8 = 0;
    let mut v___x_8194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_8179_ = crate::leanh::lean_ctor_get(v_x_8175_, 0);
                v_vs_8180_ = crate::leanh::lean_ctor_get(v_x_8175_, 1);
                v_isSharedCheck_8204_ = (!crate::leanh::lean_is_exclusive(v_x_8175_)) as u8;
                if v_isSharedCheck_8204_ == 0 {
                    v___x_8182_ = v_x_8175_;
                    v_isShared_8183_ = v_isSharedCheck_8204_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_8180_);
                    crate::leanh::lean_inc(v_ks_8179_);
                    crate::leanh::lean_dec(v_x_8175_);
                    v___x_8182_ = crate::leanh::lean_box(0);
                    v_isShared_8183_ = v_isSharedCheck_8204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8184_ = lean_array_get_size(v_ks_8179_);
                v___x_8185_ = lean_nat_dec_lt(v_x_8176_, v___x_8184_);
                if v___x_8185_ == 0 {
                    crate::leanh::lean_dec(v_x_8176_);
                    v___x_8186_ = lean_array_push(v_ks_8179_, v_x_8177_);
                    v___x_8187_ = lean_array_push(v_vs_8180_, v_x_8178_);
                    if v_isShared_8183_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8182_, 1, v___x_8187_);
                        crate::leanh::lean_ctor_set(v___x_8182_, 0, v___x_8186_);
                        v___x_8189_ = v___x_8182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8190_, 0, v___x_8186_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8190_, 1, v___x_8187_);
                        v___x_8189_ = v_reuseFailAlloc_8190_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_8191_ = lean_array_fget_borrowed(v_ks_8179_, v_x_8176_);
                    v___x_8192_ = l_Lean_instBEqMVarId_beq(v_x_8177_, v_k_x27_8191_);
                    if v___x_8192_ == 0 {
                        if v_isShared_8183_ == 0 {
                            v___x_8194_ = v___x_8182_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8198_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8198_, 0, v_ks_8179_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8198_, 1, v_vs_8180_);
                            v___x_8194_ = v_reuseFailAlloc_8198_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_8199_ = lean_array_fset(v_ks_8179_, v_x_8176_, v_x_8177_);
                        v___x_8200_ = lean_array_fset(v_vs_8180_, v_x_8176_, v_x_8178_);
                        crate::leanh::lean_dec(v_x_8176_);
                        if v_isShared_8183_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8182_, 1, v___x_8200_);
                            crate::leanh::lean_ctor_set(v___x_8182_, 0, v___x_8199_);
                            v___x_8202_ = v___x_8182_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_8203_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8203_, 0, v___x_8199_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8203_, 1, v___x_8200_);
                            v___x_8202_ = v_reuseFailAlloc_8203_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8189_;
            }
            3 => {
                v___x_8195_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_8196_ = lean_nat_add(v_x_8176_, v___x_8195_);
                crate::leanh::lean_dec(v_x_8176_);
                v_x_8175_ = v___x_8194_;
                v_x_8176_ = v___x_8196_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_8202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(
    mut v_n_8205_: *mut crate::leanh::LeanObject,
    mut v_k_8206_: *mut crate::leanh::LeanObject,
    mut v_v_8207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8208_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8209_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_8205_, v___x_8208_, v_k_8206_, v_v_8207_);
    return v___x_8209_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_8210_: usize = 0;
    let mut v___x_8211_: usize = 0;
    let mut v___x_8212_: usize = 0;
    v___x_8210_ = 5usize;
    v___x_8211_ = 1usize;
    v___x_8212_ = lean_usize_shift_left(v___x_8211_, v___x_8210_);
    return v___x_8212_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_8213_: usize = 0;
    let mut v___x_8214_: usize = 0;
    let mut v___x_8215_: usize = 0;
    v___x_8213_ = 1usize;
    v___x_8214_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
    v___x_8215_ = lean_usize_sub(v___x_8214_, v___x_8213_);
    return v___x_8215_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8216_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_8216_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(
    mut v_x_8217_: *mut crate::leanh::LeanObject,
    mut v_x_8218_: usize,
    mut v_x_8219_: usize,
    mut v_x_8220_: *mut crate::leanh::LeanObject,
    mut v_x_8221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: usize = 0;
    let mut v___x_8224_: usize = 0;
    let mut v___x_8225_: usize = 0;
    let mut v___x_8226_: usize = 0;
    let mut v_j_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: u8 = 0;
    let mut v___x_8231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8232_: u8 = 0;
    let mut v_v_8233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_8235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_8242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8246_: u8 = 0;
    let mut v___x_8247_: u8 = 0;
    let mut v___x_8248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8253_: u8 = 0;
    let mut v_node_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8257_: u8 = 0;
    let mut v___x_8258_: usize = 0;
    let mut v___x_8259_: usize = 0;
    let mut v___x_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8264_: u8 = 0;
    let mut v___x_8265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8266_: u8 = 0;
    let mut v_unused_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_8269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8272_: u8 = 0;
    let mut v___x_8274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_8275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8277_: u8 = 0;
    let mut v_ks_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_8279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: usize = 0;
    let mut v___x_8284_: u8 = 0;
    let mut v___x_8285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8287_: u8 = 0;
    let mut v_reuseFailAlloc_8288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8217_) == 0 {
                    v_es_8222_ = crate::leanh::lean_ctor_get(v_x_8217_, 0);
                    v___x_8223_ = 5usize;
                    v___x_8224_ = 1usize;
                    v___x_8225_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1);
                    v___x_8226_ = lean_usize_land(v_x_8218_, v___x_8225_);
                    v_j_8227_ = lean_usize_to_nat(v___x_8226_);
                    v___x_8228_ = lean_array_get_size(v_es_8222_);
                    v___x_8229_ = lean_nat_dec_lt(v_j_8227_, v___x_8228_);
                    if v___x_8229_ == 0 {
                        crate::leanh::lean_dec(v_j_8227_);
                        crate::leanh::lean_dec(v_x_8221_);
                        crate::leanh::lean_dec(v_x_8220_);
                        return v_x_8217_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_8222_);
                        v_isSharedCheck_8266_ = (!crate::leanh::lean_is_exclusive(v_x_8217_)) as u8;
                        if v_isSharedCheck_8266_ == 0 {
                            v_unused_8267_ = crate::leanh::lean_ctor_get(v_x_8217_, 0);
                            crate::leanh::lean_dec(v_unused_8267_);
                            v___x_8231_ = v_x_8217_;
                            v_isShared_8232_ = v_isSharedCheck_8266_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_8217_);
                            v___x_8231_ = crate::leanh::lean_box(0);
                            v_isShared_8232_ = v_isSharedCheck_8266_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_8268_ = crate::leanh::lean_ctor_get(v_x_8217_, 0);
                    v_vs_8269_ = crate::leanh::lean_ctor_get(v_x_8217_, 1);
                    v_isSharedCheck_8289_ = (!crate::leanh::lean_is_exclusive(v_x_8217_)) as u8;
                    if v_isSharedCheck_8289_ == 0 {
                        v___x_8271_ = v_x_8217_;
                        v_isShared_8272_ = v_isSharedCheck_8289_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_8269_);
                        crate::leanh::lean_inc(v_ks_8268_);
                        crate::leanh::lean_dec(v_x_8217_);
                        v___x_8271_ = crate::leanh::lean_box(0);
                        v_isShared_8272_ = v_isSharedCheck_8289_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_8233_ = lean_array_fget(v_es_8222_, v_j_8227_);
                v___x_8234_ = crate::leanh::lean_box(0);
                v_xs_x27_8235_ = lean_array_fset(v_es_8222_, v_j_8227_, v___x_8234_);
                match crate::leanh::lean_obj_tag(v_v_8233_) {
                    0 => {
                        v_key_8242_ = crate::leanh::lean_ctor_get(v_v_8233_, 0);
                        v_val_8243_ = crate::leanh::lean_ctor_get(v_v_8233_, 1);
                        v_isSharedCheck_8253_ = (!crate::leanh::lean_is_exclusive(v_v_8233_)) as u8;
                        if v_isSharedCheck_8253_ == 0 {
                            v___x_8245_ = v_v_8233_;
                            v_isShared_8246_ = v_isSharedCheck_8253_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_8243_);
                            crate::leanh::lean_inc(v_key_8242_);
                            crate::leanh::lean_dec(v_v_8233_);
                            v___x_8245_ = crate::leanh::lean_box(0);
                            v_isShared_8246_ = v_isSharedCheck_8253_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_8254_ = crate::leanh::lean_ctor_get(v_v_8233_, 0);
                        v_isSharedCheck_8264_ = (!crate::leanh::lean_is_exclusive(v_v_8233_)) as u8;
                        if v_isSharedCheck_8264_ == 0 {
                            v___x_8256_ = v_v_8233_;
                            v_isShared_8257_ = v_isSharedCheck_8264_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_8254_);
                            crate::leanh::lean_dec(v_v_8233_);
                            v___x_8256_ = crate::leanh::lean_box(0);
                            v_isShared_8257_ = v_isSharedCheck_8264_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_8265_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8265_, 0, v_x_8220_);
                        crate::leanh::lean_ctor_set(v___x_8265_, 1, v_x_8221_);
                        v___y_8237_ = v___x_8265_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8238_ = lean_array_fset(v_xs_x27_8235_, v_j_8227_, v___y_8237_);
                crate::leanh::lean_dec(v_j_8227_);
                if v_isShared_8232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8231_, 0, v___x_8238_);
                    v___x_8240_ = v___x_8231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8241_, 0, v___x_8238_);
                    v___x_8240_ = v_reuseFailAlloc_8241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8240_;
            }
            4 => {
                v___x_8247_ = l_Lean_instBEqMVarId_beq(v_x_8220_, v_key_8242_);
                if v___x_8247_ == 0 {
                    crate::leanh::lean_del_object(v___x_8245_);
                    v___x_8248_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_8242_,
                        v_val_8243_,
                        v_x_8220_,
                        v_x_8221_,
                    );
                    v___x_8249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8249_, 0, v___x_8248_);
                    v___y_8237_ = v___x_8249_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_8243_);
                    crate::leanh::lean_dec(v_key_8242_);
                    if v_isShared_8246_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8245_, 1, v_x_8221_);
                        crate::leanh::lean_ctor_set(v___x_8245_, 0, v_x_8220_);
                        v___x_8251_ = v___x_8245_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8252_, 0, v_x_8220_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8252_, 1, v_x_8221_);
                        v___x_8251_ = v_reuseFailAlloc_8252_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_8237_ = v___x_8251_;
                state = 2;
                continue;
            }
            6 => {
                v___x_8258_ = lean_usize_shift_right(v_x_8218_, v___x_8223_);
                v___x_8259_ = lean_usize_add(v_x_8219_, v___x_8224_);
                v___x_8260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_8254_, v___x_8258_, v___x_8259_, v_x_8220_, v_x_8221_);
                if v_isShared_8257_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8256_, 0, v___x_8260_);
                    v___x_8262_ = v___x_8256_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8263_, 0, v___x_8260_);
                    v___x_8262_ = v_reuseFailAlloc_8263_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_8237_ = v___x_8262_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_8272_ == 0 {
                    v___x_8274_ = v___x_8271_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8288_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8288_, 0, v_ks_8268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8288_, 1, v_vs_8269_);
                    v___x_8274_ = v_reuseFailAlloc_8288_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_8275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_8274_, v_x_8220_, v_x_8221_);
                v___x_8283_ = 7usize;
                v___x_8284_ = lean_usize_dec_le(v___x_8283_, v_x_8219_);
                if v___x_8284_ == 0 {
                    v___x_8285_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_8275_);
                    v___x_8286_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_8287_ = lean_nat_dec_lt(v___x_8285_, v___x_8286_);
                    crate::leanh::lean_dec(v___x_8285_);
                    v___y_8277_ = v___x_8287_;
                    state = 10;
                    continue;
                } else {
                    v___y_8277_ = v___x_8284_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_8277_ == 0 {
                    v_ks_8278_ = crate::leanh::lean_ctor_get(v_newNode_8275_, 0);
                    crate::leanh::lean_inc_ref(v_ks_8278_);
                    v_vs_8279_ = crate::leanh::lean_ctor_get(v_newNode_8275_, 1);
                    crate::leanh::lean_inc_ref(v_vs_8279_);
                    crate::leanh::lean_dec_ref(v_newNode_8275_);
                    v___x_8280_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_8281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2);
                    v___x_8282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_8219_, v_ks_8278_, v_vs_8279_, v___x_8280_, v___x_8281_);
                    crate::leanh::lean_dec_ref(v_vs_8279_);
                    crate::leanh::lean_dec_ref(v_ks_8278_);
                    return v___x_8282_;
                } else {
                    return v_newNode_8275_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(
    mut v_depth_8290_: usize,
    mut v_keys_8291_: *mut crate::leanh::LeanObject,
    mut v_vals_8292_: *mut crate::leanh::LeanObject,
    mut v_i_8293_: *mut crate::leanh::LeanObject,
    mut v_entries_8294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8296_: u8 = 0;
    let mut v_k_8297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: u64 = 0;
    let mut v_h_8300_: usize = 0;
    let mut v___x_8301_: usize = 0;
    let mut v___x_8302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8303_: usize = 0;
    let mut v___x_8304_: usize = 0;
    let mut v___x_8305_: usize = 0;
    let mut v_h_8306_: usize = 0;
    let mut v___x_8307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8295_ = lean_array_get_size(v_keys_8291_);
                v___x_8296_ = lean_nat_dec_lt(v_i_8293_, v___x_8295_);
                if v___x_8296_ == 0 {
                    crate::leanh::lean_dec(v_i_8293_);
                    return v_entries_8294_;
                } else {
                    v_k_8297_ = lean_array_fget_borrowed(v_keys_8291_, v_i_8293_);
                    v_v_8298_ = lean_array_fget_borrowed(v_vals_8292_, v_i_8293_);
                    v___x_8299_ = l_Lean_instHashableMVarId_hash(v_k_8297_);
                    v_h_8300_ = lean_uint64_to_usize(v___x_8299_);
                    v___x_8301_ = 5usize;
                    v___x_8302_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8303_ = 1usize;
                    v___x_8304_ = lean_usize_sub(v_depth_8290_, v___x_8303_);
                    v___x_8305_ = lean_usize_mul(v___x_8301_, v___x_8304_);
                    v_h_8306_ = lean_usize_shift_right(v_h_8300_, v___x_8305_);
                    v___x_8307_ = lean_nat_add(v_i_8293_, v___x_8302_);
                    crate::leanh::lean_dec(v_i_8293_);
                    crate::leanh::lean_inc(v_v_8298_);
                    crate::leanh::lean_inc(v_k_8297_);
                    v___x_8308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_8294_, v_h_8306_, v_depth_8290_, v_k_8297_, v_v_8298_);
                    v_i_8293_ = v___x_8307_;
                    v_entries_8294_ = v___x_8308_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(
    mut v_depth_8310_: *mut crate::leanh::LeanObject,
    mut v_keys_8311_: *mut crate::leanh::LeanObject,
    mut v_vals_8312_: *mut crate::leanh::LeanObject,
    mut v_i_8313_: *mut crate::leanh::LeanObject,
    mut v_entries_8314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_8315_: usize = 0;
    let mut v_res_8316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_8315_ = crate::leanh::lean_unbox_usize(v_depth_8310_);
    crate::leanh::lean_dec(v_depth_8310_);
    v_res_8316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_8315_, v_keys_8311_, v_vals_8312_, v_i_8313_, v_entries_8314_);
    crate::leanh::lean_dec_ref(v_vals_8312_);
    crate::leanh::lean_dec_ref(v_keys_8311_);
    return v_res_8316_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_x_8317_: *mut crate::leanh::LeanObject,
    mut v_x_8318_: *mut crate::leanh::LeanObject,
    mut v_x_8319_: *mut crate::leanh::LeanObject,
    mut v_x_8320_: *mut crate::leanh::LeanObject,
    mut v_x_8321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7972__boxed_8322_: usize = 0;
    let mut v_x_7973__boxed_8323_: usize = 0;
    let mut v_res_8324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7972__boxed_8322_ = crate::leanh::lean_unbox_usize(v_x_8318_);
    crate::leanh::lean_dec(v_x_8318_);
    v_x_7973__boxed_8323_ = crate::leanh::lean_unbox_usize(v_x_8319_);
    crate::leanh::lean_dec(v_x_8319_);
    v_res_8324_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8317_, v_x_7972__boxed_8322_, v_x_7973__boxed_8323_, v_x_8320_, v_x_8321_);
    return v_res_8324_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(
    mut v_x_8325_: *mut crate::leanh::LeanObject,
    mut v_x_8326_: *mut crate::leanh::LeanObject,
    mut v_x_8327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8328_: u64 = 0;
    let mut v___x_8329_: usize = 0;
    let mut v___x_8330_: usize = 0;
    let mut v___x_8331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_instHashableMVarId_hash(v_x_8326_);
    v___x_8329_ = lean_uint64_to_usize(v___x_8328_);
    v___x_8330_ = 1usize;
    v___x_8331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8325_, v___x_8329_, v___x_8330_, v_x_8326_, v_x_8327_);
    return v___x_8331_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
    mut v_mvarId_8332_: *mut crate::leanh::LeanObject,
    mut v_val_8333_: *mut crate::leanh::LeanObject,
    mut v___y_8334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_8340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8344_: u8 = 0;
    let mut v_depth_8345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_8346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_8347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_8348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_8349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_8350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_8351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_8352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_8353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_8354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8357_: u8 = 0;
    let mut v___x_8358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8368_: u8 = 0;
    let mut v_isSharedCheck_8369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8336_ = lean_st_ref_take(v___y_8334_);
                v_mctx_8337_ = crate::leanh::lean_ctor_get(v___x_8336_, 0);
                v_cache_8338_ = crate::leanh::lean_ctor_get(v___x_8336_, 1);
                v_zetaDeltaFVarIds_8339_ = crate::leanh::lean_ctor_get(v___x_8336_, 2);
                v_postponed_8340_ = crate::leanh::lean_ctor_get(v___x_8336_, 3);
                v_diag_8341_ = crate::leanh::lean_ctor_get(v___x_8336_, 4);
                v_isSharedCheck_8369_ = (!crate::leanh::lean_is_exclusive(v___x_8336_)) as u8;
                if v_isSharedCheck_8369_ == 0 {
                    v___x_8343_ = v___x_8336_;
                    v_isShared_8344_ = v_isSharedCheck_8369_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_8341_);
                    crate::leanh::lean_inc(v_postponed_8340_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_8339_);
                    crate::leanh::lean_inc(v_cache_8338_);
                    crate::leanh::lean_inc(v_mctx_8337_);
                    crate::leanh::lean_dec(v___x_8336_);
                    v___x_8343_ = crate::leanh::lean_box(0);
                    v_isShared_8344_ = v_isSharedCheck_8369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_8345_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 0);
                v_levelAssignDepth_8346_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 1);
                v_lmvarCounter_8347_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 2);
                v_mvarCounter_8348_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 3);
                v_lDecls_8349_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 4);
                v_decls_8350_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 5);
                v_userNames_8351_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 6);
                v_lAssignment_8352_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 7);
                v_eAssignment_8353_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 8);
                v_dAssignment_8354_ = crate::leanh::lean_ctor_get(v_mctx_8337_, 9);
                v_isSharedCheck_8368_ = (!crate::leanh::lean_is_exclusive(v_mctx_8337_)) as u8;
                if v_isSharedCheck_8368_ == 0 {
                    v___x_8356_ = v_mctx_8337_;
                    v_isShared_8357_ = v_isSharedCheck_8368_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_8354_);
                    crate::leanh::lean_inc(v_eAssignment_8353_);
                    crate::leanh::lean_inc(v_lAssignment_8352_);
                    crate::leanh::lean_inc(v_userNames_8351_);
                    crate::leanh::lean_inc(v_decls_8350_);
                    crate::leanh::lean_inc(v_lDecls_8349_);
                    crate::leanh::lean_inc(v_mvarCounter_8348_);
                    crate::leanh::lean_inc(v_lmvarCounter_8347_);
                    crate::leanh::lean_inc(v_levelAssignDepth_8346_);
                    crate::leanh::lean_inc(v_depth_8345_);
                    crate::leanh::lean_dec(v_mctx_8337_);
                    v___x_8356_ = crate::leanh::lean_box(0);
                    v_isShared_8357_ = v_isSharedCheck_8368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8358_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_8353_, v_mvarId_8332_, v_val_8333_);
                if v_isShared_8357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8356_, 8, v___x_8358_);
                    v___x_8360_ = v___x_8356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8367_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 0, v_depth_8345_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_8367_,
                        1,
                        v_levelAssignDepth_8346_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 2, v_lmvarCounter_8347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 3, v_mvarCounter_8348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 4, v_lDecls_8349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 5, v_decls_8350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 6, v_userNames_8351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 7, v_lAssignment_8352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 8, v___x_8358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8367_, 9, v_dAssignment_8354_);
                    v___x_8360_ = v_reuseFailAlloc_8367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8343_, 0, v___x_8360_);
                    v___x_8362_ = v___x_8343_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8366_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8366_, 0, v___x_8360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8366_, 1, v_cache_8338_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_8366_,
                        2,
                        v_zetaDeltaFVarIds_8339_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8366_, 3, v_postponed_8340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8366_, 4, v_diag_8341_);
                    v___x_8362_ = v_reuseFailAlloc_8366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8363_ = lean_st_ref_set(v___y_8334_, v___x_8362_);
                v___x_8364_ = crate::leanh::lean_box(0);
                v___x_8365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8365_, 0, v___x_8364_);
                return v___x_8365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(
    mut v_mvarId_8370_: *mut crate::leanh::LeanObject,
    mut v_val_8371_: *mut crate::leanh::LeanObject,
    mut v___y_8372_: *mut crate::leanh::LeanObject,
    mut v___y_8373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8374_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
        v_mvarId_8370_,
        v_val_8371_,
        v___y_8372_,
    );
    crate::leanh::lean_dec(v___y_8372_);
    return v_res_8374_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets___lam__0(
    mut v_mvar_8377_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8378_: u8,
    mut v___y_8379_: *mut crate::leanh::LeanObject,
    mut v___y_8380_: *mut crate::leanh::LeanObject,
    mut v___y_8381_: *mut crate::leanh::LeanObject,
    mut v___y_8382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_8391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_8395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8409_: usize = 0;
    let mut v___x_8410_: usize = 0;
    let mut v___x_8411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8415_: u8 = 0;
    let mut v___x_8417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8419_: u8 = 0;
    let mut v_a_8420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8423_: u8 = 0;
    let mut v___x_8425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8427_: u8 = 0;
    let mut v_a_8428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8431_: u8 = 0;
    let mut v___x_8433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8435_: u8 = 0;
    let mut v_a_8436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8439_: u8 = 0;
    let mut v___x_8441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8443_: u8 = 0;
    let mut v_a_8444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8447_: u8 = 0;
    let mut v___x_8449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8451_: u8 = 0;
    let mut v_a_8452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8455_: u8 = 0;
    let mut v___x_8457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8459_: u8 = 0;
    let mut v_a_8460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8463_: u8 = 0;
    let mut v___x_8465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvar_8377_);
                v___x_8384_ = l_Lean_MVarId_getType(
                    v_mvar_8377_,
                    v___y_8379_,
                    v___y_8380_,
                    v___y_8381_,
                    v___y_8382_,
                );
                if crate::leanh::lean_obj_tag(v___x_8384_) == 0 {
                    v_a_8385_ = crate::leanh::lean_ctor_get(v___x_8384_, 0);
                    crate::leanh::lean_inc(v_a_8385_);
                    crate::leanh::lean_dec_ref_known(v___x_8384_, 1);
                    v___x_8386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0;
                    v___x_8387_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_a_8385_,
                        v___x_8386_,
                        v___y_8379_,
                        v___y_8380_,
                        v___y_8381_,
                        v___y_8382_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8387_) == 0 {
                        v_a_8388_ = crate::leanh::lean_ctor_get(v___x_8387_, 0);
                        crate::leanh::lean_inc(v_a_8388_);
                        crate::leanh::lean_dec_ref_known(v___x_8387_, 1);
                        v_fst_8389_ = crate::leanh::lean_ctor_get(v_a_8388_, 0);
                        crate::leanh::lean_inc(v_fst_8389_);
                        v_snd_8390_ = crate::leanh::lean_ctor_get(v_a_8388_, 1);
                        crate::leanh::lean_inc(v_snd_8390_);
                        crate::leanh::lean_dec(v_a_8388_);
                        v_lctx_8391_ = crate::leanh::lean_ctor_get(v___y_8379_, 2);
                        crate::leanh::lean_inc_ref(v_lctx_8391_);
                        v___x_8392_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(
                            v_lctx_8391_,
                            v_snd_8390_,
                            v___y_8379_,
                            v___y_8380_,
                            v___y_8381_,
                            v___y_8382_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8392_) == 0 {
                            v_a_8393_ = crate::leanh::lean_ctor_get(v___x_8392_, 0);
                            crate::leanh::lean_inc(v_a_8393_);
                            crate::leanh::lean_dec_ref_known(v___x_8392_, 1);
                            v___x_8394_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0;
                            v_decls_8395_ = crate::leanh::lean_ctor_get(v_a_8393_, 1);
                            crate::leanh::lean_inc_ref(v_decls_8395_);
                            crate::leanh::lean_dec(v_a_8393_);
                            v___x_8396_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_8378_, v_decls_8395_, v___x_8394_, v___y_8379_, v___y_8380_, v___y_8381_, v___y_8382_);
                            crate::leanh::lean_dec_ref(v_decls_8395_);
                            if crate::leanh::lean_obj_tag(v___x_8396_) == 0 {
                                v_a_8397_ = crate::leanh::lean_ctor_get(v___x_8396_, 0);
                                crate::leanh::lean_inc(v_a_8397_);
                                crate::leanh::lean_dec_ref_known(v___x_8396_, 1);
                                v_fst_8398_ = crate::leanh::lean_ctor_get(v_a_8397_, 0);
                                crate::leanh::lean_inc(v_fst_8398_);
                                v_snd_8399_ = crate::leanh::lean_ctor_get(v_a_8397_, 1);
                                crate::leanh::lean_inc(v_snd_8399_);
                                crate::leanh::lean_dec(v_a_8397_);
                                v___x_8400_ =
                                    l_Lean_Expr_replaceFVars(v_fst_8389_, v_fst_8398_, v_snd_8399_);
                                crate::leanh::lean_dec(v_snd_8399_);
                                crate::leanh::lean_dec(v_fst_8389_);
                                v___x_8401_ = l_Lean_Elab_Tactic_Do_elimLetsCore(
                                    v___x_8400_,
                                    v_elimTrivial_8378_,
                                    v___y_8379_,
                                    v___y_8380_,
                                    v___y_8381_,
                                    v___y_8382_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_8401_) == 0 {
                                    v_a_8402_ = crate::leanh::lean_ctor_get(v___x_8401_, 0);
                                    crate::leanh::lean_inc(v_a_8402_);
                                    crate::leanh::lean_dec_ref_known(v___x_8401_, 1);
                                    crate::leanh::lean_inc(v_mvar_8377_);
                                    v___x_8403_ = l_Lean_MVarId_getTag(
                                        v_mvar_8377_,
                                        v___y_8379_,
                                        v___y_8380_,
                                        v___y_8381_,
                                        v___y_8382_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_8403_) == 0 {
                                        v_a_8404_ = crate::leanh::lean_ctor_get(v___x_8403_, 0);
                                        crate::leanh::lean_inc(v_a_8404_);
                                        crate::leanh::lean_dec_ref_known(v___x_8403_, 1);
                                        v___x_8405_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                            v_a_8402_,
                                            v_a_8404_,
                                            v___y_8379_,
                                            v___y_8380_,
                                            v___y_8381_,
                                            v___y_8382_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_8405_) == 0 {
                                            v_a_8406_ = crate::leanh::lean_ctor_get(v___x_8405_, 0);
                                            crate::leanh::lean_inc_n(v_a_8406_, 2);
                                            crate::leanh::lean_dec_ref_known(v___x_8405_, 1);
                                            v___x_8407_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_8377_, v_a_8406_, v___y_8380_);
                                            crate::leanh::lean_dec_ref(v___x_8407_);
                                            v___x_8408_ = l_Lean_Expr_mvarId_x21(v_a_8406_);
                                            crate::leanh::lean_dec(v_a_8406_);
                                            v_sz_8409_ = lean_array_size(v_fst_8398_);
                                            v___x_8410_ = 0usize;
                                            v___x_8411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_8398_, v_sz_8409_, v___x_8410_, v___x_8408_, v___y_8379_, v___y_8380_, v___y_8381_, v___y_8382_);
                                            crate::leanh::lean_dec_ref(v___y_8379_);
                                            crate::leanh::lean_dec(v_fst_8398_);
                                            return v___x_8411_;
                                        } else {
                                            crate::leanh::lean_dec(v_fst_8398_);
                                            crate::leanh::lean_dec_ref(v___y_8379_);
                                            crate::leanh::lean_dec(v_mvar_8377_);
                                            v_a_8412_ = crate::leanh::lean_ctor_get(v___x_8405_, 0);
                                            v_isSharedCheck_8419_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_8405_))
                                                    as u8;
                                            if v_isSharedCheck_8419_ == 0 {
                                                v___x_8414_ = v___x_8405_;
                                                v_isShared_8415_ = v_isSharedCheck_8419_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_8412_);
                                                crate::leanh::lean_dec(v___x_8405_);
                                                v___x_8414_ = crate::leanh::lean_box(0);
                                                v_isShared_8415_ = v_isSharedCheck_8419_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_8402_);
                                        crate::leanh::lean_dec(v_fst_8398_);
                                        crate::leanh::lean_dec_ref(v___y_8379_);
                                        crate::leanh::lean_dec(v_mvar_8377_);
                                        v_a_8420_ = crate::leanh::lean_ctor_get(v___x_8403_, 0);
                                        v_isSharedCheck_8427_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_8403_)) as u8;
                                        if v_isSharedCheck_8427_ == 0 {
                                            v___x_8422_ = v___x_8403_;
                                            v_isShared_8423_ = v_isSharedCheck_8427_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_8420_);
                                            crate::leanh::lean_dec(v___x_8403_);
                                            v___x_8422_ = crate::leanh::lean_box(0);
                                            v_isShared_8423_ = v_isSharedCheck_8427_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_8398_);
                                    crate::leanh::lean_dec_ref(v___y_8379_);
                                    crate::leanh::lean_dec(v_mvar_8377_);
                                    v_a_8428_ = crate::leanh::lean_ctor_get(v___x_8401_, 0);
                                    v_isSharedCheck_8435_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_8401_)) as u8;
                                    if v_isSharedCheck_8435_ == 0 {
                                        v___x_8430_ = v___x_8401_;
                                        v_isShared_8431_ = v_isSharedCheck_8435_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_8428_);
                                        crate::leanh::lean_dec(v___x_8401_);
                                        v___x_8430_ = crate::leanh::lean_box(0);
                                        v_isShared_8431_ = v_isSharedCheck_8435_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_8389_);
                                crate::leanh::lean_dec_ref(v___y_8379_);
                                crate::leanh::lean_dec(v_mvar_8377_);
                                v_a_8436_ = crate::leanh::lean_ctor_get(v___x_8396_, 0);
                                v_isSharedCheck_8443_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8396_)) as u8;
                                if v_isSharedCheck_8443_ == 0 {
                                    v___x_8438_ = v___x_8396_;
                                    v_isShared_8439_ = v_isSharedCheck_8443_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8436_);
                                    crate::leanh::lean_dec(v___x_8396_);
                                    v___x_8438_ = crate::leanh::lean_box(0);
                                    v_isShared_8439_ = v_isSharedCheck_8443_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_8389_);
                            crate::leanh::lean_dec_ref(v___y_8379_);
                            crate::leanh::lean_dec(v_mvar_8377_);
                            v_a_8444_ = crate::leanh::lean_ctor_get(v___x_8392_, 0);
                            v_isSharedCheck_8451_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8392_)) as u8;
                            if v_isSharedCheck_8451_ == 0 {
                                v___x_8446_ = v___x_8392_;
                                v_isShared_8447_ = v_isSharedCheck_8451_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8444_);
                                crate::leanh::lean_dec(v___x_8392_);
                                v___x_8446_ = crate::leanh::lean_box(0);
                                v_isShared_8447_ = v_isSharedCheck_8451_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_8379_);
                        crate::leanh::lean_dec(v_mvar_8377_);
                        v_a_8452_ = crate::leanh::lean_ctor_get(v___x_8387_, 0);
                        v_isSharedCheck_8459_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8387_)) as u8;
                        if v_isSharedCheck_8459_ == 0 {
                            v___x_8454_ = v___x_8387_;
                            v_isShared_8455_ = v_isSharedCheck_8459_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8452_);
                            crate::leanh::lean_dec(v___x_8387_);
                            v___x_8454_ = crate::leanh::lean_box(0);
                            v_isShared_8455_ = v_isSharedCheck_8459_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_8379_);
                    crate::leanh::lean_dec(v_mvar_8377_);
                    v_a_8460_ = crate::leanh::lean_ctor_get(v___x_8384_, 0);
                    v_isSharedCheck_8467_ = (!crate::leanh::lean_is_exclusive(v___x_8384_)) as u8;
                    if v_isSharedCheck_8467_ == 0 {
                        v___x_8462_ = v___x_8384_;
                        v_isShared_8463_ = v_isSharedCheck_8467_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8460_);
                        crate::leanh::lean_dec(v___x_8384_);
                        v___x_8462_ = crate::leanh::lean_box(0);
                        v_isShared_8463_ = v_isSharedCheck_8467_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8415_ == 0 {
                    v___x_8417_ = v___x_8414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8418_, 0, v_a_8412_);
                    v___x_8417_ = v_reuseFailAlloc_8418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8417_;
            }
            3 => {
                if v_isShared_8423_ == 0 {
                    v___x_8425_ = v___x_8422_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8426_, 0, v_a_8420_);
                    v___x_8425_ = v_reuseFailAlloc_8426_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8425_;
            }
            5 => {
                if v_isShared_8431_ == 0 {
                    v___x_8433_ = v___x_8430_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8434_, 0, v_a_8428_);
                    v___x_8433_ = v_reuseFailAlloc_8434_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8433_;
            }
            7 => {
                if v_isShared_8439_ == 0 {
                    v___x_8441_ = v___x_8438_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8442_, 0, v_a_8436_);
                    v___x_8441_ = v_reuseFailAlloc_8442_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8441_;
            }
            9 => {
                if v_isShared_8447_ == 0 {
                    v___x_8449_ = v___x_8446_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8450_, 0, v_a_8444_);
                    v___x_8449_ = v_reuseFailAlloc_8450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8449_;
            }
            11 => {
                if v_isShared_8455_ == 0 {
                    v___x_8457_ = v___x_8454_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8458_, 0, v_a_8452_);
                    v___x_8457_ = v_reuseFailAlloc_8458_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8457_;
            }
            13 => {
                if v_isShared_8463_ == 0 {
                    v___x_8465_ = v___x_8462_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8466_, 0, v_a_8460_);
                    v___x_8465_ = v_reuseFailAlloc_8466_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_8465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(
    mut v_mvar_8468_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8469_: *mut crate::leanh::LeanObject,
    mut v___y_8470_: *mut crate::leanh::LeanObject,
    mut v___y_8471_: *mut crate::leanh::LeanObject,
    mut v___y_8472_: *mut crate::leanh::LeanObject,
    mut v___y_8473_: *mut crate::leanh::LeanObject,
    mut v___y_8474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8475_: u8 = 0;
    let mut v_res_8476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8475_ = (crate::leanh::lean_unbox(v_elimTrivial_8469_) as u8);
    v_res_8476_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(
        v_mvar_8468_,
        v_elimTrivial_boxed_8475_,
        v___y_8470_,
        v___y_8471_,
        v___y_8472_,
        v___y_8473_,
    );
    crate::leanh::lean_dec(v___y_8473_);
    crate::leanh::lean_dec_ref(v___y_8472_);
    crate::leanh::lean_dec(v___y_8471_);
    return v_res_8476_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets(
    mut v_mvar_8477_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8478_: u8,
    mut v_a_8479_: *mut crate::leanh::LeanObject,
    mut v_a_8480_: *mut crate::leanh::LeanObject,
    mut v_a_8481_: *mut crate::leanh::LeanObject,
    mut v_a_8482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8484_ = crate::leanh::lean_box((v_elimTrivial_8478_) as usize);
    crate::leanh::lean_inc(v_mvar_8477_);
    v___f_8485_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_8485_, 0, v_mvar_8477_);
    crate::leanh::lean_closure_set(v___f_8485_, 1, v___x_8484_);
    v___x_8486_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
        v_mvar_8477_,
        v___f_8485_,
        v_a_8479_,
        v_a_8480_,
        v_a_8481_,
        v_a_8482_,
    );
    return v___x_8486_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets___boxed(
    mut v_mvar_8487_: *mut crate::leanh::LeanObject,
    mut v_elimTrivial_8488_: *mut crate::leanh::LeanObject,
    mut v_a_8489_: *mut crate::leanh::LeanObject,
    mut v_a_8490_: *mut crate::leanh::LeanObject,
    mut v_a_8491_: *mut crate::leanh::LeanObject,
    mut v_a_8492_: *mut crate::leanh::LeanObject,
    mut v_a_8493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8494_: u8 = 0;
    let mut v_res_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8494_ = (crate::leanh::lean_unbox(v_elimTrivial_8488_) as u8);
    v_res_8495_ = l_Lean_Elab_Tactic_Do_elimLets(
        v_mvar_8487_,
        v_elimTrivial_boxed_8494_,
        v_a_8489_,
        v_a_8490_,
        v_a_8491_,
        v_a_8492_,
    );
    crate::leanh::lean_dec(v_a_8492_);
    crate::leanh::lean_dec_ref(v_a_8491_);
    crate::leanh::lean_dec(v_a_8490_);
    crate::leanh::lean_dec_ref(v_a_8489_);
    return v_res_8495_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(
    mut v_mvarId_8496_: *mut crate::leanh::LeanObject,
    mut v_val_8497_: *mut crate::leanh::LeanObject,
    mut v___y_8498_: *mut crate::leanh::LeanObject,
    mut v___y_8499_: *mut crate::leanh::LeanObject,
    mut v___y_8500_: *mut crate::leanh::LeanObject,
    mut v___y_8501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8503_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
        v_mvarId_8496_,
        v_val_8497_,
        v___y_8499_,
    );
    return v___x_8503_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(
    mut v_mvarId_8504_: *mut crate::leanh::LeanObject,
    mut v_val_8505_: *mut crate::leanh::LeanObject,
    mut v___y_8506_: *mut crate::leanh::LeanObject,
    mut v___y_8507_: *mut crate::leanh::LeanObject,
    mut v___y_8508_: *mut crate::leanh::LeanObject,
    mut v___y_8509_: *mut crate::leanh::LeanObject,
    mut v___y_8510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8511_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(
        v_mvarId_8504_,
        v_val_8505_,
        v___y_8506_,
        v___y_8507_,
        v___y_8508_,
        v___y_8509_,
    );
    crate::leanh::lean_dec(v___y_8509_);
    crate::leanh::lean_dec_ref(v___y_8508_);
    crate::leanh::lean_dec(v___y_8507_);
    crate::leanh::lean_dec_ref(v___y_8506_);
    return v_res_8511_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(
    mut v_00_u03b2_8512_: *mut crate::leanh::LeanObject,
    mut v_x_8513_: *mut crate::leanh::LeanObject,
    mut v_x_8514_: *mut crate::leanh::LeanObject,
    mut v_x_8515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8516_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_8513_, v_x_8514_, v_x_8515_);
    return v___x_8516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(
    mut v_elimTrivial_8517_: u8,
    mut v_as_8518_: *mut crate::leanh::LeanObject,
    mut v_sz_8519_: usize,
    mut v_i_8520_: usize,
    mut v_b_8521_: *mut crate::leanh::LeanObject,
    mut v___y_8522_: *mut crate::leanh::LeanObject,
    mut v___y_8523_: *mut crate::leanh::LeanObject,
    mut v___y_8524_: *mut crate::leanh::LeanObject,
    mut v___y_8525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_8517_, v_as_8518_, v_sz_8519_, v_i_8520_, v_b_8521_);
    return v___x_8527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(
    mut v_elimTrivial_8528_: *mut crate::leanh::LeanObject,
    mut v_as_8529_: *mut crate::leanh::LeanObject,
    mut v_sz_8530_: *mut crate::leanh::LeanObject,
    mut v_i_8531_: *mut crate::leanh::LeanObject,
    mut v_b_8532_: *mut crate::leanh::LeanObject,
    mut v___y_8533_: *mut crate::leanh::LeanObject,
    mut v___y_8534_: *mut crate::leanh::LeanObject,
    mut v___y_8535_: *mut crate::leanh::LeanObject,
    mut v___y_8536_: *mut crate::leanh::LeanObject,
    mut v___y_8537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8538_: u8 = 0;
    let mut v_sz_boxed_8539_: usize = 0;
    let mut v_i_boxed_8540_: usize = 0;
    let mut v_res_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8538_ = (crate::leanh::lean_unbox(v_elimTrivial_8528_) as u8);
    v_sz_boxed_8539_ = crate::leanh::lean_unbox_usize(v_sz_8530_);
    crate::leanh::lean_dec(v_sz_8530_);
    v_i_boxed_8540_ = crate::leanh::lean_unbox_usize(v_i_8531_);
    crate::leanh::lean_dec(v_i_8531_);
    v_res_8541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_8538_, v_as_8529_, v_sz_boxed_8539_, v_i_boxed_8540_, v_b_8532_, v___y_8533_, v___y_8534_, v___y_8535_, v___y_8536_);
    crate::leanh::lean_dec(v___y_8536_);
    crate::leanh::lean_dec_ref(v___y_8535_);
    crate::leanh::lean_dec(v___y_8534_);
    crate::leanh::lean_dec_ref(v___y_8533_);
    crate::leanh::lean_dec_ref(v_as_8529_);
    return v_res_8541_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(
    mut v_00_u03b2_8542_: *mut crate::leanh::LeanObject,
    mut v_x_8543_: *mut crate::leanh::LeanObject,
    mut v_x_8544_: usize,
    mut v_x_8545_: usize,
    mut v_x_8546_: *mut crate::leanh::LeanObject,
    mut v_x_8547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8543_, v_x_8544_, v_x_8545_, v_x_8546_, v_x_8547_);
    return v___x_8548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_8549_: *mut crate::leanh::LeanObject,
    mut v_x_8550_: *mut crate::leanh::LeanObject,
    mut v_x_8551_: *mut crate::leanh::LeanObject,
    mut v_x_8552_: *mut crate::leanh::LeanObject,
    mut v_x_8553_: *mut crate::leanh::LeanObject,
    mut v_x_8554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8428__boxed_8555_: usize = 0;
    let mut v_x_8429__boxed_8556_: usize = 0;
    let mut v_res_8557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8428__boxed_8555_ = crate::leanh::lean_unbox_usize(v_x_8551_);
    crate::leanh::lean_dec(v_x_8551_);
    v_x_8429__boxed_8556_ = crate::leanh::lean_unbox_usize(v_x_8552_);
    crate::leanh::lean_dec(v_x_8552_);
    v_res_8557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_8549_, v_x_8550_, v_x_8428__boxed_8555_, v_x_8429__boxed_8556_, v_x_8553_, v_x_8554_);
    return v_res_8557_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(
    mut v_elimTrivial_8558_: u8,
    mut v_as_8559_: *mut crate::leanh::LeanObject,
    mut v_sz_8560_: usize,
    mut v_i_8561_: usize,
    mut v_b_8562_: *mut crate::leanh::LeanObject,
    mut v___y_8563_: *mut crate::leanh::LeanObject,
    mut v___y_8564_: *mut crate::leanh::LeanObject,
    mut v___y_8565_: *mut crate::leanh::LeanObject,
    mut v___y_8566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_8558_, v_as_8559_, v_sz_8560_, v_i_8561_, v_b_8562_);
    return v___x_8568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(
    mut v_elimTrivial_8569_: *mut crate::leanh::LeanObject,
    mut v_as_8570_: *mut crate::leanh::LeanObject,
    mut v_sz_8571_: *mut crate::leanh::LeanObject,
    mut v_i_8572_: *mut crate::leanh::LeanObject,
    mut v_b_8573_: *mut crate::leanh::LeanObject,
    mut v___y_8574_: *mut crate::leanh::LeanObject,
    mut v___y_8575_: *mut crate::leanh::LeanObject,
    mut v___y_8576_: *mut crate::leanh::LeanObject,
    mut v___y_8577_: *mut crate::leanh::LeanObject,
    mut v___y_8578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elimTrivial_boxed_8579_: u8 = 0;
    let mut v_sz_boxed_8580_: usize = 0;
    let mut v_i_boxed_8581_: usize = 0;
    let mut v_res_8582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8579_ = (crate::leanh::lean_unbox(v_elimTrivial_8569_) as u8);
    v_sz_boxed_8580_ = crate::leanh::lean_unbox_usize(v_sz_8571_);
    crate::leanh::lean_dec(v_sz_8571_);
    v_i_boxed_8581_ = crate::leanh::lean_unbox_usize(v_i_8572_);
    crate::leanh::lean_dec(v_i_8572_);
    v_res_8582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_8579_, v_as_8570_, v_sz_boxed_8580_, v_i_boxed_8581_, v_b_8573_, v___y_8574_, v___y_8575_, v___y_8576_, v___y_8577_);
    crate::leanh::lean_dec(v___y_8577_);
    crate::leanh::lean_dec_ref(v___y_8576_);
    crate::leanh::lean_dec(v___y_8575_);
    crate::leanh::lean_dec_ref(v___y_8574_);
    crate::leanh::lean_dec_ref(v_as_8570_);
    return v_res_8582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(
    mut v_00_u03b2_8583_: *mut crate::leanh::LeanObject,
    mut v_n_8584_: *mut crate::leanh::LeanObject,
    mut v_k_8585_: *mut crate::leanh::LeanObject,
    mut v_v_8586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8587_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_8584_, v_k_8585_, v_v_8586_);
    return v___x_8587_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(
    mut v_00_u03b2_8588_: *mut crate::leanh::LeanObject,
    mut v_depth_8589_: usize,
    mut v_keys_8590_: *mut crate::leanh::LeanObject,
    mut v_vals_8591_: *mut crate::leanh::LeanObject,
    mut v_heq_8592_: *mut crate::leanh::LeanObject,
    mut v_i_8593_: *mut crate::leanh::LeanObject,
    mut v_entries_8594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_8589_, v_keys_8590_, v_vals_8591_, v_i_8593_, v_entries_8594_);
    return v___x_8595_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(
    mut v_00_u03b2_8596_: *mut crate::leanh::LeanObject,
    mut v_depth_8597_: *mut crate::leanh::LeanObject,
    mut v_keys_8598_: *mut crate::leanh::LeanObject,
    mut v_vals_8599_: *mut crate::leanh::LeanObject,
    mut v_heq_8600_: *mut crate::leanh::LeanObject,
    mut v_i_8601_: *mut crate::leanh::LeanObject,
    mut v_entries_8602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_8603_: usize = 0;
    let mut v_res_8604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_8603_ = crate::leanh::lean_unbox_usize(v_depth_8597_);
    crate::leanh::lean_dec(v_depth_8597_);
    v_res_8604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_8596_, v_depth_boxed_8603_, v_keys_8598_, v_vals_8599_, v_heq_8600_, v_i_8601_, v_entries_8602_);
    crate::leanh::lean_dec_ref(v_vals_8599_);
    crate::leanh::lean_dec_ref(v_keys_8598_);
    return v_res_8604_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(
    mut v_00_u03b2_8605_: *mut crate::leanh::LeanObject,
    mut v_x_8606_: *mut crate::leanh::LeanObject,
    mut v_x_8607_: *mut crate::leanh::LeanObject,
    mut v_x_8608_: *mut crate::leanh::LeanObject,
    mut v_x_8609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8610_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_8606_, v_x_8607_, v_x_8608_, v_x_8609_);
    return v___x_8610_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_LetElim(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_instInhabitedUses_default =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
    l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_LetElim(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 =
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_LetElim(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
