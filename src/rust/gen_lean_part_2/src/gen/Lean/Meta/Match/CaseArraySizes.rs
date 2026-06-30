// Lean compiler output
// Module: Lean.Meta.Match.CaseArraySizes
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.FVarSubst Lean.Meta.Match.CaseValues Lean.Meta.Tactic.Subst
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uset,
    lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_fvarId_x21, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkArrayLit, l_Lean_Meta_mkDecideProof, l_Lean_Meta_mkEq,
    l_Lean_Meta_mkEqSymm, l_Lean_Meta_mkLt,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_whnfD, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Match::CaseValues::{
    initialize_Lean_Meta_Match_CaseValues, l_Lean_Meta_caseValues,
    runtime_initialize_Lean_Meta_Match_CaseValues,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assertExt;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_clear;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_Meta_FVarSubst_get,
    runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_Meta_intro1Core, l_Lean_Meta_introNCore};
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    initialize_Lean_Meta_Tactic_Subst, l_Lean_Meta_substCore,
    runtime_initialize_Lean_Meta_Tactic_Subst,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
pub static l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCaseArraySizesSubgoal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getArrayArgType___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [65, 114, 114, 97, 121, 0],
    };
static mut l_Lean_Meta_getArrayArgType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getArrayArgType___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getArrayArgType___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getArrayArgType___closed__2_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            97, 114, 114, 97, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_getArrayArgType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_getArrayArgType___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getArrayArgType___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 101, 116, 76, 105, 116, 0]};
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value) as *mut leanh::LeanObject,4403657421190733771 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 111, 65, 114, 114, 97, 121, 76, 105, 116, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value) as *mut leanh::LeanObject,16726848587136120379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [104, 69, 113, 65, 76, 105, 116, 0]};
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value) as *mut leanh::LeanObject,14282815305757940368 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 83, 105, 122, 101, 0],
};
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            15829423518986167985 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__2_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__5_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___lam__0___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__5_value)
                as *mut leanh::LeanObject,
            8738205681931236784 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_caseArraySizes___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_caseArraySizes___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [115, 105, 122, 101, 0],
    };
static mut l_Lean_Meta_caseArraySizes___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_caseArraySizes___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getArrayArgType___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_caseArraySizes___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___closed__0_value)
                as *mut leanh::LeanObject,
            16555935894841173036 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_caseArraySizes___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_caseArraySizes___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(
    mut v_msgData_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = lean_st_ref_get(v___y_1258_);
    v_env_1261_ = leanh::lean_ctor_get(v___x_1260_, 0);
    leanh::lean_inc_ref(v_env_1261_);
    leanh::lean_dec(v___x_1260_);
    v___x_1262_ = lean_st_ref_get(v___y_1256_);
    v_mctx_1263_ = leanh::lean_ctor_get(v___x_1262_, 0);
    leanh::lean_inc_ref(v_mctx_1263_);
    leanh::lean_dec(v___x_1262_);
    v_lctx_1264_ = leanh::lean_ctor_get(v___y_1255_, 2);
    v_options_1265_ = leanh::lean_ctor_get(v___y_1257_, 2);
    leanh::lean_inc_ref(v_options_1265_);
    leanh::lean_inc_ref(v_lctx_1264_);
    v___x_1266_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1266_, 0, v_env_1261_);
    leanh::lean_ctor_set(v___x_1266_, 1, v_mctx_1263_);
    leanh::lean_ctor_set(v___x_1266_, 2, v_lctx_1264_);
    leanh::lean_ctor_set(v___x_1266_, 3, v_options_1265_);
    v___x_1267_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1267_, 0, v___x_1266_);
    leanh::lean_ctor_set(v___x_1267_, 1, v_msgData_1254_);
    v___x_1268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(
    mut v_msgData_1269_: *mut leanh::LeanObject,
    mut v___y_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
    leanh::lean_dec(v___y_1273_);
    leanh::lean_dec_ref(v___y_1272_);
    leanh::lean_dec(v___y_1271_);
    leanh::lean_dec_ref(v___y_1270_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(
    mut v_msg_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1287_: u8 = 0;
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1282_ = leanh::lean_ctor_get(v___y_1279_, 5);
                v___x_1283_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msg_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
                v_a_1284_ = leanh::lean_ctor_get(v___x_1283_, 0);
                v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v___x_1283_)) as u8;
                if v_isSharedCheck_1292_ == 0 {
                    v___x_1286_ = v___x_1283_;
                    v_isShared_1287_ = v_isSharedCheck_1292_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1284_);
                    leanh::lean_dec(v___x_1283_);
                    v___x_1286_ = leanh::lean_box(0);
                    v_isShared_1287_ = v_isSharedCheck_1292_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1282_);
                v___x_1288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1288_, 0, v_ref_1282_);
                leanh::lean_ctor_set(v___x_1288_, 1, v_a_1284_);
                if v_isShared_1287_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1286_, 1);
                    leanh::lean_ctor_set(v___x_1286_, 0, v___x_1288_);
                    v___x_1290_ = v___x_1286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(
    mut v_msg_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(
        v_msg_1293_,
        v___y_1294_,
        v___y_1295_,
        v___y_1296_,
        v___y_1297_,
    );
    leanh::lean_dec(v___y_1297_);
    leanh::lean_dec_ref(v___y_1296_);
    leanh::lean_dec(v___y_1295_);
    leanh::lean_dec_ref(v___y_1294_);
    return v_res_1299_;
}
pub unsafe fn _init_l_Lean_Meta_getArrayArgType___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Lean_Meta_getArrayArgType___closed__2;
    v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_Meta_getArrayArgType(
    mut v_a_1306_: *mut leanh::LeanObject,
    mut v_a_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
    mut v_a_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_1310_);
                leanh::lean_inc_ref(v_a_1309_);
                leanh::lean_inc(v_a_1308_);
                leanh::lean_inc_ref(v_a_1307_);
                leanh::lean_inc_ref(v_a_1306_);
                v___x_1312_ =
                    lean_infer_type(v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
                if leanh::lean_obj_tag(v___x_1312_) == 0 {
                    v_a_1313_ = leanh::lean_ctor_get(v___x_1312_, 0);
                    leanh::lean_inc(v_a_1313_);
                    leanh::lean_dec_ref_known(v___x_1312_, 1);
                    v___x_1314_ =
                        l_Lean_Meta_whnfD(v_a_1313_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
                    if leanh::lean_obj_tag(v___x_1314_) == 0 {
                        v_a_1315_ = leanh::lean_ctor_get(v___x_1314_, 0);
                        v_isSharedCheck_1339_ =
                            (!leanh::lean_is_exclusive(v___x_1314_)) as u8;
                        if v_isSharedCheck_1339_ == 0 {
                            v___x_1317_ = v___x_1314_;
                            v_isShared_1318_ = v_isSharedCheck_1339_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1315_);
                            leanh::lean_dec(v___x_1314_);
                            v___x_1317_ = leanh::lean_box(0);
                            v_isShared_1318_ = v_isSharedCheck_1339_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_1306_);
                        return v___x_1314_;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1306_);
                    return v___x_1312_;
                }
            }
            1 => {
                v___x_1324_ = l_Lean_Meta_getArrayArgType___closed__1;
                v___x_1325_ = leanh::lean_unsigned_to_nat(1);
                v___x_1326_ = l_Lean_Expr_isAppOfArity(v_a_1315_, v___x_1324_, v___x_1325_);
                if v___x_1326_ == 0 {
                    leanh::lean_del_object(v___x_1317_);
                    leanh::lean_dec(v_a_1315_);
                    v___x_1327_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_getArrayArgType___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_getArrayArgType___closed__3_once),
                        _init_l_Lean_Meta_getArrayArgType___closed__3,
                    );
                    v___x_1328_ = l_Lean_indentExpr(v_a_1306_);
                    v___x_1329_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1329_, 0, v___x_1327_);
                    leanh::lean_ctor_set(v___x_1329_, 1, v___x_1328_);
                    v___x_1330_ =
                        l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(
                            v___x_1329_,
                            v_a_1307_,
                            v_a_1308_,
                            v_a_1309_,
                            v_a_1310_,
                        );
                    v_a_1331_ = leanh::lean_ctor_get(v___x_1330_, 0);
                    v_isSharedCheck_1338_ = (!leanh::lean_is_exclusive(v___x_1330_)) as u8;
                    if v_isSharedCheck_1338_ == 0 {
                        v___x_1333_ = v___x_1330_;
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1331_);
                        leanh::lean_dec(v___x_1330_);
                        v___x_1333_ = leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1306_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1320_ = l_Lean_Expr_appArg_x21(v_a_1315_);
                leanh::lean_dec(v_a_1315_);
                if v_isShared_1318_ == 0 {
                    leanh::lean_ctor_set(v___x_1317_, 0, v___x_1320_);
                    v___x_1322_ = v___x_1317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
                    v___x_1322_ = v_reuseFailAlloc_1323_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1322_;
            }
            4 => {
                if v_isShared_1334_ == 0 {
                    v___x_1336_ = v___x_1333_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
                    v___x_1336_ = v_reuseFailAlloc_1337_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getArrayArgType___boxed(
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
    mut v_a_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ =
        l_Lean_Meta_getArrayArgType(v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
    leanh::lean_dec(v_a_1344_);
    leanh::lean_dec_ref(v_a_1343_);
    leanh::lean_dec(v_a_1342_);
    leanh::lean_dec_ref(v_a_1341_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(
    mut v_00_u03b1_1347_: *mut leanh::LeanObject,
    mut v_msg_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(
        v_msg_1348_,
        v___y_1349_,
        v___y_1350_,
        v___y_1351_,
        v___y_1352_,
    );
    return v___x_1354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(
    mut v_00_u03b1_1355_: *mut leanh::LeanObject,
    mut v_msg_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(
        v_00_u03b1_1355_,
        v_msg_1356_,
        v___y_1357_,
        v___y_1358_,
        v___y_1359_,
        v___y_1360_,
    );
    leanh::lean_dec(v___y_1360_);
    leanh::lean_dec_ref(v___y_1359_);
    leanh::lean_dec(v___y_1358_);
    leanh::lean_dec_ref(v___y_1357_);
    return v_res_1362_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_i_1368_: *mut leanh::LeanObject,
    mut v_n_1369_: *mut leanh::LeanObject,
    mut v_h_1370_: *mut leanh::LeanObject,
    mut v_a_1371_: *mut leanh::LeanObject,
    mut v_a_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Lean_mkRawNatLit(v_i_1368_);
    v___x_1377_ = l_Lean_mkRawNatLit(v_n_1369_);
    leanh::lean_inc_ref(v___x_1376_);
    v___x_1378_ = l_Lean_Meta_mkLt(
        v___x_1376_,
        v___x_1377_,
        v_a_1371_,
        v_a_1372_,
        v_a_1373_,
        v_a_1374_,
    );
    if leanh::lean_obj_tag(v___x_1378_) == 0 {
        let mut v_a_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1379_ = leanh::lean_ctor_get(v___x_1378_, 0);
        leanh::lean_inc(v_a_1379_);
        leanh::lean_dec_ref_known(v___x_1378_, 1);
        v___x_1380_ =
            l_Lean_Meta_mkDecideProof(v_a_1379_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
        if leanh::lean_obj_tag(v___x_1380_) == 0 {
            let mut v_a_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1381_ = leanh::lean_ctor_get(v___x_1380_, 0);
            leanh::lean_inc(v_a_1381_);
            leanh::lean_dec_ref_known(v___x_1380_, 1);
            v___x_1382_ =
                l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1;
            v___x_1383_ = leanh::lean_unsigned_to_nat(4);
            v___x_1384_ = lean_mk_empty_array_with_capacity(v___x_1383_);
            v___x_1385_ = lean_array_push(v___x_1384_, v_a_1367_);
            v___x_1386_ = lean_array_push(v___x_1385_, v___x_1376_);
            v___x_1387_ = lean_array_push(v___x_1386_, v_h_1370_);
            v___x_1388_ = lean_array_push(v___x_1387_, v_a_1381_);
            v___x_1389_ = l_Lean_Meta_mkAppM(
                v___x_1382_,
                v___x_1388_,
                v_a_1371_,
                v_a_1372_,
                v_a_1373_,
                v_a_1374_,
            );
            return v___x_1389_;
        } else {
            leanh::lean_dec_ref(v___x_1376_);
            leanh::lean_dec_ref(v_h_1370_);
            leanh::lean_dec_ref(v_a_1367_);
            return v___x_1380_;
        }
    } else {
        leanh::lean_dec_ref(v___x_1376_);
        leanh::lean_dec_ref(v_h_1370_);
        leanh::lean_dec_ref(v_a_1367_);
        return v___x_1378_;
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_i_1391_: *mut leanh::LeanObject,
    mut v_n_1392_: *mut leanh::LeanObject,
    mut v_h_1393_: *mut leanh::LeanObject,
    mut v_a_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1399_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(
        v_a_1390_, v_i_1391_, v_n_1392_, v_h_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_,
    );
    leanh::lean_dec(v_a_1397_);
    leanh::lean_dec_ref(v_a_1396_);
    leanh::lean_dec(v_a_1395_);
    leanh::lean_dec_ref(v_a_1394_);
    return v_res_1399_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(
    mut v_mvarId_1400_: *mut leanh::LeanObject,
    mut v_xs_1401_: *mut leanh::LeanObject,
    mut v___x_1402_: u8,
    mut v_args_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_heq_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v_a_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_a_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1411_ = l_Lean_MVarId_getType(
                    v_mvarId_1400_,
                    v___y_1406_,
                    v___y_1407_,
                    v___y_1408_,
                    v___y_1409_,
                );
                if leanh::lean_obj_tag(v___x_1411_) == 0 {
                    v_a_1412_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    leanh::lean_inc(v_a_1412_);
                    leanh::lean_dec_ref_known(v___x_1411_, 1);
                    v___x_1413_ = lean_array_push(v_xs_1401_, v_heq_1405_);
                    v___x_1414_ = 1;
                    v___x_1415_ = 1;
                    v___x_1416_ = l_Lean_Meta_mkForallFVars(
                        v___x_1413_,
                        v_a_1412_,
                        v___x_1402_,
                        v___x_1414_,
                        v___x_1414_,
                        v___x_1415_,
                        v___y_1406_,
                        v___y_1407_,
                        v___y_1408_,
                        v___y_1409_,
                    );
                    leanh::lean_dec_ref(v___x_1413_);
                    if leanh::lean_obj_tag(v___x_1416_) == 0 {
                        v_a_1417_ = leanh::lean_ctor_get(v___x_1416_, 0);
                        v_isSharedCheck_1426_ =
                            (!leanh::lean_is_exclusive(v___x_1416_)) as u8;
                        if v_isSharedCheck_1426_ == 0 {
                            v___x_1419_ = v___x_1416_;
                            v_isShared_1420_ = v_isSharedCheck_1426_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1417_);
                            leanh::lean_dec(v___x_1416_);
                            v___x_1419_ = leanh::lean_box(0);
                            v_isShared_1420_ = v_isSharedCheck_1426_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_1404_);
                        leanh::lean_dec_ref(v_args_1403_);
                        v_a_1427_ = leanh::lean_ctor_get(v___x_1416_, 0);
                        v_isSharedCheck_1434_ =
                            (!leanh::lean_is_exclusive(v___x_1416_)) as u8;
                        if v_isSharedCheck_1434_ == 0 {
                            v___x_1429_ = v___x_1416_;
                            v_isShared_1430_ = v_isSharedCheck_1434_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1427_);
                            leanh::lean_dec(v___x_1416_);
                            v___x_1429_ = leanh::lean_box(0);
                            v_isShared_1430_ = v_isSharedCheck_1434_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_heq_1405_);
                    leanh::lean_dec_ref(v_a_1404_);
                    leanh::lean_dec_ref(v_args_1403_);
                    leanh::lean_dec_ref(v_xs_1401_);
                    v_a_1435_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1442_ = (!leanh::lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1442_ == 0 {
                        v___x_1437_ = v___x_1411_;
                        v_isShared_1438_ = v_isSharedCheck_1442_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1435_);
                        leanh::lean_dec(v___x_1411_);
                        v___x_1437_ = leanh::lean_box(0);
                        v_isShared_1438_ = v_isSharedCheck_1442_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1421_ = lean_array_push(v_args_1403_, v_a_1404_);
                v___x_1422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1422_, 0, v_a_1417_);
                leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
                if v_isShared_1420_ == 0 {
                    leanh::lean_ctor_set(v___x_1419_, 0, v___x_1422_);
                    v___x_1424_ = v___x_1419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
                    v___x_1424_ = v_reuseFailAlloc_1425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1424_;
            }
            3 => {
                if v_isShared_1430_ == 0 {
                    v___x_1432_ = v___x_1429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1432_;
            }
            5 => {
                if v_isShared_1438_ == 0 {
                    v___x_1440_ = v___x_1437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
                    v___x_1440_ = v_reuseFailAlloc_1441_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(
    mut v_mvarId_1443_: *mut leanh::LeanObject,
    mut v_xs_1444_: *mut leanh::LeanObject,
    mut v___x_1445_: *mut leanh::LeanObject,
    mut v_args_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_heq_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1223__boxed_1454_: u8 = 0;
    let mut v_res_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223__boxed_1454_ = (leanh::lean_unbox(v___x_1445_) as u8);
    v_res_1455_ =
        l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(
            v_mvarId_1443_,
            v_xs_1444_,
            v___x_1223__boxed_1454_,
            v_args_1446_,
            v_a_1447_,
            v_heq_1448_,
            v___y_1449_,
            v___y_1450_,
            v___y_1451_,
            v___y_1452_,
        );
    leanh::lean_dec(v___y_1452_);
    leanh::lean_dec_ref(v___y_1451_);
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    return v_res_1455_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(
    mut v_k_1456_: *mut leanh::LeanObject,
    mut v_b_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1461_);
    leanh::lean_inc_ref(v___y_1460_);
    leanh::lean_inc(v___y_1459_);
    leanh::lean_inc_ref(v___y_1458_);
    v___x_1463_ = leanh::lean_apply_6(
        v_k_1456_,
        v_b_1457_,
        v___y_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        leanh::lean_box(0),
    );
    return v___x_1463_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_1464_: *mut leanh::LeanObject,
    mut v_b_1465_: *mut leanh::LeanObject,
    mut v___y_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_1464_, v_b_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
    leanh::lean_dec(v___y_1469_);
    leanh::lean_dec_ref(v___y_1468_);
    leanh::lean_dec(v___y_1467_);
    leanh::lean_dec_ref(v___y_1466_);
    return v_res_1471_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(
    mut v_name_1472_: *mut leanh::LeanObject,
    mut v_bi_1473_: u8,
    mut v_type_1474_: *mut leanh::LeanObject,
    mut v_k_1475_: *mut leanh::LeanObject,
    mut v_kind_1476_: u8,
    mut v___y_1477_: *mut leanh::LeanObject,
    mut v___y_1478_: *mut leanh::LeanObject,
    mut v___y_1479_: *mut leanh::LeanObject,
    mut v___y_1480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_a_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1482_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_1482_, 0, v_k_1475_);
                v___x_1483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_1472_,
                    v_bi_1473_,
                    v_type_1474_,
                    v___f_1482_,
                    v_kind_1476_,
                    v___y_1477_,
                    v___y_1478_,
                    v___y_1479_,
                    v___y_1480_,
                );
                if leanh::lean_obj_tag(v___x_1483_) == 0 {
                    v_a_1484_ = leanh::lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1491_ = (!leanh::lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1491_ == 0 {
                        v___x_1486_ = v___x_1483_;
                        v_isShared_1487_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1484_);
                        leanh::lean_dec(v___x_1483_);
                        v___x_1486_ = leanh::lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1492_ = leanh::lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1499_ = (!leanh::lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1499_ == 0 {
                        v___x_1494_ = v___x_1483_;
                        v_isShared_1495_ = v_isSharedCheck_1499_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1492_);
                        leanh::lean_dec(v___x_1483_);
                        v___x_1494_ = leanh::lean_box(0);
                        v_isShared_1495_ = v_isSharedCheck_1499_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1487_ == 0 {
                    v___x_1489_ = v___x_1486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
                    v___x_1489_ = v_reuseFailAlloc_1490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1489_;
            }
            3 => {
                if v_isShared_1495_ == 0 {
                    v___x_1497_ = v___x_1494_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1498_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
                    v___x_1497_ = v_reuseFailAlloc_1498_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(
    mut v_name_1500_: *mut leanh::LeanObject,
    mut v_bi_1501_: *mut leanh::LeanObject,
    mut v_type_1502_: *mut leanh::LeanObject,
    mut v_k_1503_: *mut leanh::LeanObject,
    mut v_kind_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1510_: u8 = 0;
    let mut v_kind_boxed_1511_: u8 = 0;
    let mut v_res_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1510_ = (leanh::lean_unbox(v_bi_1501_) as u8);
    v_kind_boxed_1511_ = (leanh::lean_unbox(v_kind_1504_) as u8);
    v_res_1512_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_1500_, v_bi_boxed_1510_, v_type_1502_, v_k_1503_, v_kind_boxed_1511_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
    leanh::lean_dec(v___y_1508_);
    leanh::lean_dec_ref(v___y_1507_);
    leanh::lean_dec(v___y_1506_);
    leanh::lean_dec_ref(v___y_1505_);
    return v_res_1512_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(
    mut v_name_1513_: *mut leanh::LeanObject,
    mut v_type_1514_: *mut leanh::LeanObject,
    mut v_k_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
    mut v___y_1517_: *mut leanh::LeanObject,
    mut v___y_1518_: *mut leanh::LeanObject,
    mut v___y_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1521_ = 0;
    v___x_1522_ = 0;
    v___x_1523_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_1513_, v___x_1521_, v_type_1514_, v_k_1515_, v___x_1522_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
    return v___x_1523_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(
    mut v_name_1524_: *mut leanh::LeanObject,
    mut v_type_1525_: *mut leanh::LeanObject,
    mut v_k_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1532_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_1524_, v_type_1525_, v_k_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
    leanh::lean_dec(v___y_1530_);
    leanh::lean_dec_ref(v___y_1529_);
    leanh::lean_dec(v___y_1528_);
    leanh::lean_dec_ref(v___y_1527_);
    return v_res_1532_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_i_1541_: *mut leanh::LeanObject,
    mut v_n_1542_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1543_: *mut leanh::LeanObject,
    mut v_xs_1544_: *mut leanh::LeanObject,
    mut v_args_1545_: *mut leanh::LeanObject,
    mut v_mvarId_1546_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1547_: *mut leanh::LeanObject,
    mut v_00_u03b1_1548_: *mut leanh::LeanObject,
    mut v___x_1549_: *mut leanh::LeanObject,
    mut v_xi_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1556_ =
        l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(
            v_a_1540_,
            v_i_1541_,
            v_n_1542_,
            v_aSizeEqN_1543_,
            v_xs_1544_,
            v_args_1545_,
            v_mvarId_1546_,
            v_xNamePrefix_1547_,
            v_00_u03b1_1548_,
            v___x_1549_,
            v_xi_1550_,
            v___y_1551_,
            v___y_1552_,
            v___y_1553_,
            v___y_1554_,
        );
    leanh::lean_dec(v___y_1554_);
    leanh::lean_dec_ref(v___y_1553_);
    leanh::lean_dec(v___y_1552_);
    leanh::lean_dec_ref(v___y_1551_);
    return v_res_1556_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(
    mut v_mvarId_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_n_1559_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1560_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1561_: *mut leanh::LeanObject,
    mut v_00_u03b1_1562_: *mut leanh::LeanObject,
    mut v_i_1563_: *mut leanh::LeanObject,
    mut v_xs_1564_: *mut leanh::LeanObject,
    mut v_args_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
    mut v_a_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_a_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_a_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1605_: u8 = 0;
    let mut v_a_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1571_ = lean_nat_dec_lt(v_i_1563_, v_n_1559_);
                if v___x_1571_ == 0 {
                    leanh::lean_dec(v_i_1563_);
                    leanh::lean_dec(v_xNamePrefix_1560_);
                    leanh::lean_inc_ref(v_xs_1564_);
                    v___x_1572_ = lean_array_to_list(v_xs_1564_);
                    v___x_1573_ = l_Lean_Meta_mkArrayLit(
                        v_00_u03b1_1562_,
                        v___x_1572_,
                        v_a_1566_,
                        v_a_1567_,
                        v_a_1568_,
                        v_a_1569_,
                    );
                    if leanh::lean_obj_tag(v___x_1573_) == 0 {
                        v_a_1574_ = leanh::lean_ctor_get(v___x_1573_, 0);
                        leanh::lean_inc(v_a_1574_);
                        leanh::lean_dec_ref_known(v___x_1573_, 1);
                        leanh::lean_inc_ref(v_a_1558_);
                        v___x_1575_ = l_Lean_Meta_mkEq(
                            v_a_1558_, v_a_1574_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_,
                        );
                        if leanh::lean_obj_tag(v___x_1575_) == 0 {
                            v_a_1576_ = leanh::lean_ctor_get(v___x_1575_, 0);
                            leanh::lean_inc(v_a_1576_);
                            leanh::lean_dec_ref_known(v___x_1575_, 1);
                            v___x_1577_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1;
                            v___x_1578_ = l_Lean_mkRawNatLit(v_n_1559_);
                            v___x_1579_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1580_ = lean_mk_empty_array_with_capacity(v___x_1579_);
                            v___x_1581_ = lean_array_push(v___x_1580_, v_a_1558_);
                            v___x_1582_ = lean_array_push(v___x_1581_, v___x_1578_);
                            v___x_1583_ = lean_array_push(v___x_1582_, v_aSizeEqN_1561_);
                            v___x_1584_ = l_Lean_Meta_mkAppM(
                                v___x_1577_,
                                v___x_1583_,
                                v_a_1566_,
                                v_a_1567_,
                                v_a_1568_,
                                v_a_1569_,
                            );
                            if leanh::lean_obj_tag(v___x_1584_) == 0 {
                                v_a_1585_ = leanh::lean_ctor_get(v___x_1584_, 0);
                                leanh::lean_inc(v_a_1585_);
                                leanh::lean_dec_ref_known(v___x_1584_, 1);
                                v___x_1586_ = leanh::lean_box((v___x_1571_) as usize);
                                v___f_1587_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                                leanh::lean_closure_set(v___f_1587_, 0, v_mvarId_1557_);
                                leanh::lean_closure_set(v___f_1587_, 1, v_xs_1564_);
                                leanh::lean_closure_set(v___f_1587_, 2, v___x_1586_);
                                leanh::lean_closure_set(v___f_1587_, 3, v_args_1565_);
                                leanh::lean_closure_set(v___f_1587_, 4, v_a_1585_);
                                v___x_1588_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3;
                                v___x_1589_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_1588_, v_a_1576_, v___f_1587_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
                                return v___x_1589_;
                            } else {
                                leanh::lean_dec(v_a_1576_);
                                leanh::lean_dec_ref(v_args_1565_);
                                leanh::lean_dec_ref(v_xs_1564_);
                                leanh::lean_dec(v_mvarId_1557_);
                                v_a_1590_ = leanh::lean_ctor_get(v___x_1584_, 0);
                                v_isSharedCheck_1597_ =
                                    (!leanh::lean_is_exclusive(v___x_1584_)) as u8;
                                if v_isSharedCheck_1597_ == 0 {
                                    v___x_1592_ = v___x_1584_;
                                    v_isShared_1593_ = v_isSharedCheck_1597_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1590_);
                                    leanh::lean_dec(v___x_1584_);
                                    v___x_1592_ = leanh::lean_box(0);
                                    v_isShared_1593_ = v_isSharedCheck_1597_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_args_1565_);
                            leanh::lean_dec_ref(v_xs_1564_);
                            leanh::lean_dec_ref(v_aSizeEqN_1561_);
                            leanh::lean_dec(v_n_1559_);
                            leanh::lean_dec_ref(v_a_1558_);
                            leanh::lean_dec(v_mvarId_1557_);
                            v_a_1598_ = leanh::lean_ctor_get(v___x_1575_, 0);
                            v_isSharedCheck_1605_ =
                                (!leanh::lean_is_exclusive(v___x_1575_)) as u8;
                            if v_isSharedCheck_1605_ == 0 {
                                v___x_1600_ = v___x_1575_;
                                v_isShared_1601_ = v_isSharedCheck_1605_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1598_);
                                leanh::lean_dec(v___x_1575_);
                                v___x_1600_ = leanh::lean_box(0);
                                v_isShared_1601_ = v_isSharedCheck_1605_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_1565_);
                        leanh::lean_dec_ref(v_xs_1564_);
                        leanh::lean_dec_ref(v_aSizeEqN_1561_);
                        leanh::lean_dec(v_n_1559_);
                        leanh::lean_dec_ref(v_a_1558_);
                        leanh::lean_dec(v_mvarId_1557_);
                        v_a_1606_ = leanh::lean_ctor_get(v___x_1573_, 0);
                        v_isSharedCheck_1613_ =
                            (!leanh::lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1613_ == 0 {
                            v___x_1608_ = v___x_1573_;
                            v_isShared_1609_ = v_isSharedCheck_1613_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1606_);
                            leanh::lean_dec(v___x_1573_);
                            v___x_1608_ = leanh::lean_box(0);
                            v_isShared_1609_ = v_isSharedCheck_1613_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_1614_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1615_ = lean_nat_add(v_i_1563_, v___x_1614_);
                    leanh::lean_inc(v___x_1615_);
                    leanh::lean_inc_ref(v_00_u03b1_1562_);
                    leanh::lean_inc(v_xNamePrefix_1560_);
                    v___f_1616_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed as *mut core::ffi::c_void, 16, 10);
                    leanh::lean_closure_set(v___f_1616_, 0, v_a_1558_);
                    leanh::lean_closure_set(v___f_1616_, 1, v_i_1563_);
                    leanh::lean_closure_set(v___f_1616_, 2, v_n_1559_);
                    leanh::lean_closure_set(v___f_1616_, 3, v_aSizeEqN_1561_);
                    leanh::lean_closure_set(v___f_1616_, 4, v_xs_1564_);
                    leanh::lean_closure_set(v___f_1616_, 5, v_args_1565_);
                    leanh::lean_closure_set(v___f_1616_, 6, v_mvarId_1557_);
                    leanh::lean_closure_set(v___f_1616_, 7, v_xNamePrefix_1560_);
                    leanh::lean_closure_set(v___f_1616_, 8, v_00_u03b1_1562_);
                    leanh::lean_closure_set(v___f_1616_, 9, v___x_1615_);
                    v___x_1617_ = lean_name_append_index_after(v_xNamePrefix_1560_, v___x_1615_);
                    v___x_1618_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_1617_, v_00_u03b1_1562_, v___f_1616_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
                    return v___x_1618_;
                }
            }
            1 => {
                if v_isShared_1593_ == 0 {
                    v___x_1595_ = v___x_1592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
                    v___x_1595_ = v_reuseFailAlloc_1596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1595_;
            }
            3 => {
                if v_isShared_1601_ == 0 {
                    v___x_1603_ = v___x_1600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
                    v___x_1603_ = v_reuseFailAlloc_1604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1603_;
            }
            5 => {
                if v_isShared_1609_ == 0 {
                    v___x_1611_ = v___x_1608_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
                    v___x_1611_ = v_reuseFailAlloc_1612_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(
    mut v_a_1619_: *mut leanh::LeanObject,
    mut v_i_1620_: *mut leanh::LeanObject,
    mut v_n_1621_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1622_: *mut leanh::LeanObject,
    mut v_xs_1623_: *mut leanh::LeanObject,
    mut v_args_1624_: *mut leanh::LeanObject,
    mut v_mvarId_1625_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1626_: *mut leanh::LeanObject,
    mut v_00_u03b1_1627_: *mut leanh::LeanObject,
    mut v___x_1628_: *mut leanh::LeanObject,
    mut v_xi_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_aSizeEqN_1622_);
                leanh::lean_inc(v_n_1621_);
                leanh::lean_inc_ref(v_a_1619_);
                v___x_1635_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(
                    v_a_1619_,
                    v_i_1620_,
                    v_n_1621_,
                    v_aSizeEqN_1622_,
                    v___y_1630_,
                    v___y_1631_,
                    v___y_1632_,
                    v___y_1633_,
                );
                if leanh::lean_obj_tag(v___x_1635_) == 0 {
                    v_a_1636_ = leanh::lean_ctor_get(v___x_1635_, 0);
                    leanh::lean_inc(v_a_1636_);
                    leanh::lean_dec_ref_known(v___x_1635_, 1);
                    v_xs_1637_ = lean_array_push(v_xs_1623_, v_xi_1629_);
                    v___x_1638_ = lean_array_push(v_args_1624_, v_a_1636_);
                    v___x_1639_ =
                        l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(
                            v_mvarId_1625_,
                            v_a_1619_,
                            v_n_1621_,
                            v_xNamePrefix_1626_,
                            v_aSizeEqN_1622_,
                            v_00_u03b1_1627_,
                            v___x_1628_,
                            v_xs_1637_,
                            v___x_1638_,
                            v___y_1630_,
                            v___y_1631_,
                            v___y_1632_,
                            v___y_1633_,
                        );
                    return v___x_1639_;
                } else {
                    leanh::lean_dec_ref(v_xi_1629_);
                    leanh::lean_dec(v___x_1628_);
                    leanh::lean_dec_ref(v_00_u03b1_1627_);
                    leanh::lean_dec(v_xNamePrefix_1626_);
                    leanh::lean_dec(v_mvarId_1625_);
                    leanh::lean_dec_ref(v_args_1624_);
                    leanh::lean_dec_ref(v_xs_1623_);
                    leanh::lean_dec_ref(v_aSizeEqN_1622_);
                    leanh::lean_dec(v_n_1621_);
                    leanh::lean_dec_ref(v_a_1619_);
                    v_a_1640_ = leanh::lean_ctor_get(v___x_1635_, 0);
                    v_isSharedCheck_1647_ = (!leanh::lean_is_exclusive(v___x_1635_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1642_ = v___x_1635_;
                        v_isShared_1643_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1640_);
                        leanh::lean_dec(v___x_1635_);
                        v___x_1642_ = leanh::lean_box(0);
                        v_isShared_1643_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1643_ == 0 {
                    v___x_1645_ = v___x_1642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
                    v___x_1645_ = v_reuseFailAlloc_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(
    mut v_mvarId_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
    mut v_n_1650_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1651_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1652_: *mut leanh::LeanObject,
    mut v_00_u03b1_1653_: *mut leanh::LeanObject,
    mut v_i_1654_: *mut leanh::LeanObject,
    mut v_xs_1655_: *mut leanh::LeanObject,
    mut v_args_1656_: *mut leanh::LeanObject,
    mut v_a_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(
        v_mvarId_1648_,
        v_a_1649_,
        v_n_1650_,
        v_xNamePrefix_1651_,
        v_aSizeEqN_1652_,
        v_00_u03b1_1653_,
        v_i_1654_,
        v_xs_1655_,
        v_args_1656_,
        v_a_1657_,
        v_a_1658_,
        v_a_1659_,
        v_a_1660_,
    );
    leanh::lean_dec(v_a_1660_);
    leanh::lean_dec_ref(v_a_1659_);
    leanh::lean_dec(v_a_1658_);
    leanh::lean_dec_ref(v_a_1657_);
    return v_res_1662_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(
    mut v_00_u03b1_1663_: *mut leanh::LeanObject,
    mut v_name_1664_: *mut leanh::LeanObject,
    mut v_bi_1665_: u8,
    mut v_type_1666_: *mut leanh::LeanObject,
    mut v_k_1667_: *mut leanh::LeanObject,
    mut v_kind_1668_: u8,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_1664_, v_bi_1665_, v_type_1666_, v_k_1667_, v_kind_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(
    mut v_00_u03b1_1675_: *mut leanh::LeanObject,
    mut v_name_1676_: *mut leanh::LeanObject,
    mut v_bi_1677_: *mut leanh::LeanObject,
    mut v_type_1678_: *mut leanh::LeanObject,
    mut v_k_1679_: *mut leanh::LeanObject,
    mut v_kind_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1686_: u8 = 0;
    let mut v_kind_boxed_1687_: u8 = 0;
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1686_ = (leanh::lean_unbox(v_bi_1677_) as u8);
    v_kind_boxed_1687_ = (leanh::lean_unbox(v_kind_1680_) as u8);
    v_res_1688_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(v_00_u03b1_1675_, v_name_1676_, v_bi_boxed_1686_, v_type_1678_, v_k_1679_, v_kind_boxed_1687_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
    leanh::lean_dec(v___y_1684_);
    leanh::lean_dec_ref(v___y_1683_);
    leanh::lean_dec(v___y_1682_);
    leanh::lean_dec_ref(v___y_1681_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(
    mut v_00_u03b1_1689_: *mut leanh::LeanObject,
    mut v_name_1690_: *mut leanh::LeanObject,
    mut v_type_1691_: *mut leanh::LeanObject,
    mut v_k_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_1690_, v_type_1691_, v_k_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
    return v___x_1698_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(
    mut v_00_u03b1_1699_: *mut leanh::LeanObject,
    mut v_name_1700_: *mut leanh::LeanObject,
    mut v_type_1701_: *mut leanh::LeanObject,
    mut v_k_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(v_00_u03b1_1699_, v_name_1700_, v_type_1701_, v_k_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
    leanh::lean_dec(v___y_1706_);
    leanh::lean_dec_ref(v___y_1705_);
    leanh::lean_dec(v___y_1704_);
    leanh::lean_dec_ref(v___y_1703_);
    return v_res_1708_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1709_: *mut leanh::LeanObject,
    mut v_x_1710_: *mut leanh::LeanObject,
    mut v_x_1711_: *mut leanh::LeanObject,
    mut v_x_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1713_ = leanh::lean_ctor_get(v_x_1709_, 0);
                v_vs_1714_ = leanh::lean_ctor_get(v_x_1709_, 1);
                v_isSharedCheck_1738_ = (!leanh::lean_is_exclusive(v_x_1709_)) as u8;
                if v_isSharedCheck_1738_ == 0 {
                    v___x_1716_ = v_x_1709_;
                    v_isShared_1717_ = v_isSharedCheck_1738_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1714_);
                    leanh::lean_inc(v_ks_1713_);
                    leanh::lean_dec(v_x_1709_);
                    v___x_1716_ = leanh::lean_box(0);
                    v_isShared_1717_ = v_isSharedCheck_1738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1718_ = lean_array_get_size(v_ks_1713_);
                v___x_1719_ = lean_nat_dec_lt(v_x_1710_, v___x_1718_);
                if v___x_1719_ == 0 {
                    leanh::lean_dec(v_x_1710_);
                    v___x_1720_ = lean_array_push(v_ks_1713_, v_x_1711_);
                    v___x_1721_ = lean_array_push(v_vs_1714_, v_x_1712_);
                    if v_isShared_1717_ == 0 {
                        leanh::lean_ctor_set(v___x_1716_, 1, v___x_1721_);
                        leanh::lean_ctor_set(v___x_1716_, 0, v___x_1720_);
                        v___x_1723_ = v___x_1716_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1724_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1720_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1721_);
                        v___x_1723_ = v_reuseFailAlloc_1724_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1725_ = lean_array_fget_borrowed(v_ks_1713_, v_x_1710_);
                    v___x_1726_ = l_Lean_instBEqMVarId_beq(v_x_1711_, v_k_x27_1725_);
                    if v___x_1726_ == 0 {
                        if v_isShared_1717_ == 0 {
                            v___x_1728_ = v___x_1716_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1732_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_ks_1713_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_vs_1714_);
                            v___x_1728_ = v_reuseFailAlloc_1732_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1733_ = lean_array_fset(v_ks_1713_, v_x_1710_, v_x_1711_);
                        v___x_1734_ = lean_array_fset(v_vs_1714_, v_x_1710_, v_x_1712_);
                        leanh::lean_dec(v_x_1710_);
                        if v_isShared_1717_ == 0 {
                            leanh::lean_ctor_set(v___x_1716_, 1, v___x_1734_);
                            leanh::lean_ctor_set(v___x_1716_, 0, v___x_1733_);
                            v___x_1736_ = v___x_1716_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1737_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1733_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1734_);
                            v___x_1736_ = v_reuseFailAlloc_1737_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1723_;
            }
            3 => {
                v___x_1729_ = leanh::lean_unsigned_to_nat(1);
                v___x_1730_ = lean_nat_add(v_x_1710_, v___x_1729_);
                leanh::lean_dec(v_x_1710_);
                v_x_1709_ = v___x_1728_;
                v_x_1710_ = v___x_1730_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_1739_: *mut leanh::LeanObject,
    mut v_k_1740_: *mut leanh::LeanObject,
    mut v_v_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = leanh::lean_unsigned_to_nat(0);
    v___x_1743_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1739_, v___x_1742_, v_k_1740_, v_v_1741_);
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: usize = 0;
    v___x_1744_ = 5usize;
    v___x_1745_ = 1usize;
    v___x_1746_ = lean_usize_shift_left(v___x_1745_, v___x_1744_);
    return v___x_1746_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    v___x_1747_ = 1usize;
    v___x_1748_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1749_ = lean_usize_sub(v___x_1748_, v___x_1747_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1750_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(
    mut v_x_1751_: *mut leanh::LeanObject,
    mut v_x_1752_: usize,
    mut v_x_1753_: usize,
    mut v_x_1754_: *mut leanh::LeanObject,
    mut v_x_1755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: usize = 0;
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: usize = 0;
    let mut v_j_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v_v_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_node_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: usize = 0;
    let mut v___x_1793_: usize = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut v_unused_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1811_: u8 = 0;
    let mut v_ks_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1751_) == 0 {
                    v_es_1756_ = leanh::lean_ctor_get(v_x_1751_, 0);
                    v___x_1757_ = 5usize;
                    v___x_1758_ = 1usize;
                    v___x_1759_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1760_ = lean_usize_land(v_x_1752_, v___x_1759_);
                    v_j_1761_ = lean_usize_to_nat(v___x_1760_);
                    v___x_1762_ = lean_array_get_size(v_es_1756_);
                    v___x_1763_ = lean_nat_dec_lt(v_j_1761_, v___x_1762_);
                    if v___x_1763_ == 0 {
                        leanh::lean_dec(v_j_1761_);
                        leanh::lean_dec(v_x_1755_);
                        leanh::lean_dec(v_x_1754_);
                        return v_x_1751_;
                    } else {
                        leanh::lean_inc_ref(v_es_1756_);
                        v_isSharedCheck_1800_ = (!leanh::lean_is_exclusive(v_x_1751_)) as u8;
                        if v_isSharedCheck_1800_ == 0 {
                            v_unused_1801_ = leanh::lean_ctor_get(v_x_1751_, 0);
                            leanh::lean_dec(v_unused_1801_);
                            v___x_1765_ = v_x_1751_;
                            v_isShared_1766_ = v_isSharedCheck_1800_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1751_);
                            v___x_1765_ = leanh::lean_box(0);
                            v_isShared_1766_ = v_isSharedCheck_1800_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1802_ = leanh::lean_ctor_get(v_x_1751_, 0);
                    v_vs_1803_ = leanh::lean_ctor_get(v_x_1751_, 1);
                    v_isSharedCheck_1823_ = (!leanh::lean_is_exclusive(v_x_1751_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1805_ = v_x_1751_;
                        v_isShared_1806_ = v_isSharedCheck_1823_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1803_);
                        leanh::lean_inc(v_ks_1802_);
                        leanh::lean_dec(v_x_1751_);
                        v___x_1805_ = leanh::lean_box(0);
                        v_isShared_1806_ = v_isSharedCheck_1823_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1767_ = lean_array_fget(v_es_1756_, v_j_1761_);
                v___x_1768_ = leanh::lean_box(0);
                v_xs_x27_1769_ = lean_array_fset(v_es_1756_, v_j_1761_, v___x_1768_);
                match leanh::lean_obj_tag(v_v_1767_) {
                    0 => {
                        v_key_1776_ = leanh::lean_ctor_get(v_v_1767_, 0);
                        v_val_1777_ = leanh::lean_ctor_get(v_v_1767_, 1);
                        v_isSharedCheck_1787_ = (!leanh::lean_is_exclusive(v_v_1767_)) as u8;
                        if v_isSharedCheck_1787_ == 0 {
                            v___x_1779_ = v_v_1767_;
                            v_isShared_1780_ = v_isSharedCheck_1787_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1777_);
                            leanh::lean_inc(v_key_1776_);
                            leanh::lean_dec(v_v_1767_);
                            v___x_1779_ = leanh::lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1787_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1788_ = leanh::lean_ctor_get(v_v_1767_, 0);
                        v_isSharedCheck_1798_ = (!leanh::lean_is_exclusive(v_v_1767_)) as u8;
                        if v_isSharedCheck_1798_ == 0 {
                            v___x_1790_ = v_v_1767_;
                            v_isShared_1791_ = v_isSharedCheck_1798_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1788_);
                            leanh::lean_dec(v_v_1767_);
                            v___x_1790_ = leanh::lean_box(0);
                            v_isShared_1791_ = v_isSharedCheck_1798_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1799_, 0, v_x_1754_);
                        leanh::lean_ctor_set(v___x_1799_, 1, v_x_1755_);
                        v___y_1771_ = v___x_1799_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1772_ = lean_array_fset(v_xs_x27_1769_, v_j_1761_, v___y_1771_);
                leanh::lean_dec(v_j_1761_);
                if v_isShared_1766_ == 0 {
                    leanh::lean_ctor_set(v___x_1765_, 0, v___x_1772_);
                    v___x_1774_ = v___x_1765_;
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
            3 => {
                return v___x_1774_;
            }
            4 => {
                v___x_1781_ = l_Lean_instBEqMVarId_beq(v_x_1754_, v_key_1776_);
                if v___x_1781_ == 0 {
                    leanh::lean_del_object(v___x_1779_);
                    v___x_1782_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1776_,
                        v_val_1777_,
                        v_x_1754_,
                        v_x_1755_,
                    );
                    v___x_1783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1783_, 0, v___x_1782_);
                    v___y_1771_ = v___x_1783_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1777_);
                    leanh::lean_dec(v_key_1776_);
                    if v_isShared_1780_ == 0 {
                        leanh::lean_ctor_set(v___x_1779_, 1, v_x_1755_);
                        leanh::lean_ctor_set(v___x_1779_, 0, v_x_1754_);
                        v___x_1785_ = v___x_1779_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_x_1754_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_x_1755_);
                        v___x_1785_ = v_reuseFailAlloc_1786_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1771_ = v___x_1785_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1792_ = lean_usize_shift_right(v_x_1752_, v___x_1757_);
                v___x_1793_ = lean_usize_add(v_x_1753_, v___x_1758_);
                v___x_1794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_node_1788_, v___x_1792_, v___x_1793_, v_x_1754_, v_x_1755_);
                if v_isShared_1791_ == 0 {
                    leanh::lean_ctor_set(v___x_1790_, 0, v___x_1794_);
                    v___x_1796_ = v___x_1790_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
                    v___x_1796_ = v_reuseFailAlloc_1797_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1771_ = v___x_1796_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1806_ == 0 {
                    v___x_1808_ = v___x_1805_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_ks_1802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_vs_1803_);
                    v___x_1808_ = v_reuseFailAlloc_1822_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1809_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1808_, v_x_1754_, v_x_1755_);
                v___x_1817_ = 7usize;
                v___x_1818_ = lean_usize_dec_le(v___x_1817_, v_x_1753_);
                if v___x_1818_ == 0 {
                    v___x_1819_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1809_);
                    v___x_1820_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1821_ = lean_nat_dec_lt(v___x_1819_, v___x_1820_);
                    leanh::lean_dec(v___x_1819_);
                    v___y_1811_ = v___x_1821_;
                    state = 10;
                    continue;
                } else {
                    v___y_1811_ = v___x_1818_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1811_ == 0 {
                    v_ks_1812_ = leanh::lean_ctor_get(v_newNode_1809_, 0);
                    leanh::lean_inc_ref(v_ks_1812_);
                    v_vs_1813_ = leanh::lean_ctor_get(v_newNode_1809_, 1);
                    leanh::lean_inc_ref(v_vs_1813_);
                    leanh::lean_dec_ref(v_newNode_1809_);
                    v___x_1814_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1815_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1753_, v_ks_1812_, v_vs_1813_, v___x_1814_, v___x_1815_);
                    leanh::lean_dec_ref(v_vs_1813_);
                    leanh::lean_dec_ref(v_ks_1812_);
                    return v___x_1816_;
                } else {
                    return v_newNode_1809_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_1824_: usize,
    mut v_keys_1825_: *mut leanh::LeanObject,
    mut v_vals_1826_: *mut leanh::LeanObject,
    mut v_i_1827_: *mut leanh::LeanObject,
    mut v_entries_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v_k_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u64 = 0;
    let mut v_h_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: usize = 0;
    let mut v___x_1839_: usize = 0;
    let mut v_h_1840_: usize = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1829_ = lean_array_get_size(v_keys_1825_);
                v___x_1830_ = lean_nat_dec_lt(v_i_1827_, v___x_1829_);
                if v___x_1830_ == 0 {
                    leanh::lean_dec(v_i_1827_);
                    return v_entries_1828_;
                } else {
                    v_k_1831_ = lean_array_fget_borrowed(v_keys_1825_, v_i_1827_);
                    v_v_1832_ = lean_array_fget_borrowed(v_vals_1826_, v_i_1827_);
                    v___x_1833_ = l_Lean_instHashableMVarId_hash(v_k_1831_);
                    v_h_1834_ = lean_uint64_to_usize(v___x_1833_);
                    v___x_1835_ = 5usize;
                    v___x_1836_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1837_ = 1usize;
                    v___x_1838_ = lean_usize_sub(v_depth_1824_, v___x_1837_);
                    v___x_1839_ = lean_usize_mul(v___x_1835_, v___x_1838_);
                    v_h_1840_ = lean_usize_shift_right(v_h_1834_, v___x_1839_);
                    v___x_1841_ = lean_nat_add(v_i_1827_, v___x_1836_);
                    leanh::lean_dec(v_i_1827_);
                    leanh::lean_inc(v_v_1832_);
                    leanh::lean_inc(v_k_1831_);
                    v___x_1842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_entries_1828_, v_h_1840_, v_depth_1824_, v_k_1831_, v_v_1832_);
                    v_i_1827_ = v___x_1841_;
                    v_entries_1828_ = v___x_1842_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_1844_: *mut leanh::LeanObject,
    mut v_keys_1845_: *mut leanh::LeanObject,
    mut v_vals_1846_: *mut leanh::LeanObject,
    mut v_i_1847_: *mut leanh::LeanObject,
    mut v_entries_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1849_: usize = 0;
    let mut v_res_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1849_ = leanh::lean_unbox_usize(v_depth_1844_);
    leanh::lean_dec(v_depth_1844_);
    v_res_1850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1849_, v_keys_1845_, v_vals_1846_, v_i_1847_, v_entries_1848_);
    leanh::lean_dec_ref(v_vals_1846_);
    leanh::lean_dec_ref(v_keys_1845_);
    return v_res_1850_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1851_: *mut leanh::LeanObject,
    mut v_x_1852_: *mut leanh::LeanObject,
    mut v_x_1853_: *mut leanh::LeanObject,
    mut v_x_1854_: *mut leanh::LeanObject,
    mut v_x_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_998__boxed_1856_: usize = 0;
    let mut v_x_999__boxed_1857_: usize = 0;
    let mut v_res_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_998__boxed_1856_ = leanh::lean_unbox_usize(v_x_1852_);
    leanh::lean_dec(v_x_1852_);
    v_x_999__boxed_1857_ = leanh::lean_unbox_usize(v_x_1853_);
    leanh::lean_dec(v_x_1853_);
    v_res_1858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_1851_, v_x_998__boxed_1856_, v_x_999__boxed_1857_, v_x_1854_, v_x_1855_);
    return v_res_1858_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(
    mut v_x_1859_: *mut leanh::LeanObject,
    mut v_x_1860_: *mut leanh::LeanObject,
    mut v_x_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: u64 = 0;
    let mut v___x_1863_: usize = 0;
    let mut v___x_1864_: usize = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_instHashableMVarId_hash(v_x_1860_);
    v___x_1863_ = lean_uint64_to_usize(v___x_1862_);
    v___x_1864_ = 1usize;
    v___x_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_1859_, v___x_1863_, v___x_1864_, v_x_1860_, v_x_1861_);
    return v___x_1865_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(
    mut v_mvarId_1866_: *mut leanh::LeanObject,
    mut v_val_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v_depth_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1870_ = lean_st_ref_take(v___y_1868_);
                v_mctx_1871_ = leanh::lean_ctor_get(v___x_1870_, 0);
                v_cache_1872_ = leanh::lean_ctor_get(v___x_1870_, 1);
                v_zetaDeltaFVarIds_1873_ = leanh::lean_ctor_get(v___x_1870_, 2);
                v_postponed_1874_ = leanh::lean_ctor_get(v___x_1870_, 3);
                v_diag_1875_ = leanh::lean_ctor_get(v___x_1870_, 4);
                v_isSharedCheck_1903_ = (!leanh::lean_is_exclusive(v___x_1870_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v___x_1877_ = v___x_1870_;
                    v_isShared_1878_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1875_);
                    leanh::lean_inc(v_postponed_1874_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1873_);
                    leanh::lean_inc(v_cache_1872_);
                    leanh::lean_inc(v_mctx_1871_);
                    leanh::lean_dec(v___x_1870_);
                    v___x_1877_ = leanh::lean_box(0);
                    v_isShared_1878_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1879_ = leanh::lean_ctor_get(v_mctx_1871_, 0);
                v_levelAssignDepth_1880_ = leanh::lean_ctor_get(v_mctx_1871_, 1);
                v_lmvarCounter_1881_ = leanh::lean_ctor_get(v_mctx_1871_, 2);
                v_mvarCounter_1882_ = leanh::lean_ctor_get(v_mctx_1871_, 3);
                v_lDecls_1883_ = leanh::lean_ctor_get(v_mctx_1871_, 4);
                v_decls_1884_ = leanh::lean_ctor_get(v_mctx_1871_, 5);
                v_userNames_1885_ = leanh::lean_ctor_get(v_mctx_1871_, 6);
                v_lAssignment_1886_ = leanh::lean_ctor_get(v_mctx_1871_, 7);
                v_eAssignment_1887_ = leanh::lean_ctor_get(v_mctx_1871_, 8);
                v_dAssignment_1888_ = leanh::lean_ctor_get(v_mctx_1871_, 9);
                v_isSharedCheck_1902_ = (!leanh::lean_is_exclusive(v_mctx_1871_)) as u8;
                if v_isSharedCheck_1902_ == 0 {
                    v___x_1890_ = v_mctx_1871_;
                    v_isShared_1891_ = v_isSharedCheck_1902_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1888_);
                    leanh::lean_inc(v_eAssignment_1887_);
                    leanh::lean_inc(v_lAssignment_1886_);
                    leanh::lean_inc(v_userNames_1885_);
                    leanh::lean_inc(v_decls_1884_);
                    leanh::lean_inc(v_lDecls_1883_);
                    leanh::lean_inc(v_mvarCounter_1882_);
                    leanh::lean_inc(v_lmvarCounter_1881_);
                    leanh::lean_inc(v_levelAssignDepth_1880_);
                    leanh::lean_inc(v_depth_1879_);
                    leanh::lean_dec(v_mctx_1871_);
                    v___x_1890_ = leanh::lean_box(0);
                    v_isShared_1891_ = v_isSharedCheck_1902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1892_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_eAssignment_1887_, v_mvarId_1866_, v_val_1867_);
                if v_isShared_1891_ == 0 {
                    leanh::lean_ctor_set(v___x_1890_, 8, v___x_1892_);
                    v___x_1894_ = v___x_1890_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_depth_1879_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1901_,
                        1,
                        v_levelAssignDepth_1880_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_lmvarCounter_1881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_mvarCounter_1882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_lDecls_1883_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 5, v_decls_1884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_userNames_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_lAssignment_1886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 8, v___x_1892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 9, v_dAssignment_1888_);
                    v___x_1894_ = v_reuseFailAlloc_1901_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1878_ == 0 {
                    leanh::lean_ctor_set(v___x_1877_, 0, v___x_1894_);
                    v___x_1896_ = v___x_1877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_cache_1872_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1900_,
                        2,
                        v_zetaDeltaFVarIds_1873_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_postponed_1874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_diag_1875_);
                    v___x_1896_ = v_reuseFailAlloc_1900_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1897_ = lean_st_ref_set(v___y_1868_, v___x_1896_);
                v___x_1898_ = leanh::lean_box(0);
                v___x_1899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1899_, 0, v___x_1898_);
                return v___x_1899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(
    mut v_mvarId_1904_: *mut leanh::LeanObject,
    mut v_val_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_1904_, v_val_1905_, v___y_1906_);
    leanh::lean_dec(v___y_1906_);
    return v_res_1908_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(
    mut v_mvarId_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_n_1913_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1914_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1915_: *mut leanh::LeanObject,
    mut v_a_1916_: *mut leanh::LeanObject,
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_unused_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v_a_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_a_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut v_a_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_1912_);
                v___x_1921_ = l_Lean_Meta_getArrayArgType(
                    v_a_1912_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_,
                );
                if leanh::lean_obj_tag(v___x_1921_) == 0 {
                    v_a_1922_ = leanh::lean_ctor_get(v___x_1921_, 0);
                    leanh::lean_inc(v_a_1922_);
                    leanh::lean_dec_ref_known(v___x_1921_, 1);
                    v___x_1923_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1924_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0;
                    leanh::lean_inc(v_mvarId_1911_);
                    v___x_1925_ =
                        l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(
                            v_mvarId_1911_,
                            v_a_1912_,
                            v_n_1913_,
                            v_xNamePrefix_1914_,
                            v_aSizeEqN_1915_,
                            v_a_1922_,
                            v___x_1923_,
                            v___x_1924_,
                            v___x_1924_,
                            v_a_1916_,
                            v_a_1917_,
                            v_a_1918_,
                            v_a_1919_,
                        );
                    if leanh::lean_obj_tag(v___x_1925_) == 0 {
                        v_a_1926_ = leanh::lean_ctor_get(v___x_1925_, 0);
                        leanh::lean_inc(v_a_1926_);
                        leanh::lean_dec_ref_known(v___x_1925_, 1);
                        v_fst_1927_ = leanh::lean_ctor_get(v_a_1926_, 0);
                        leanh::lean_inc(v_fst_1927_);
                        v_snd_1928_ = leanh::lean_ctor_get(v_a_1926_, 1);
                        leanh::lean_inc(v_snd_1928_);
                        leanh::lean_dec(v_a_1926_);
                        leanh::lean_inc(v_mvarId_1911_);
                        v___x_1929_ = l_Lean_MVarId_getTag(
                            v_mvarId_1911_,
                            v_a_1916_,
                            v_a_1917_,
                            v_a_1918_,
                            v_a_1919_,
                        );
                        if leanh::lean_obj_tag(v___x_1929_) == 0 {
                            v_a_1930_ = leanh::lean_ctor_get(v___x_1929_, 0);
                            leanh::lean_inc(v_a_1930_);
                            leanh::lean_dec_ref_known(v___x_1929_, 1);
                            v___x_1931_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_fst_1927_,
                                v_a_1930_,
                                v_a_1916_,
                                v_a_1917_,
                                v_a_1918_,
                                v_a_1919_,
                            );
                            if leanh::lean_obj_tag(v___x_1931_) == 0 {
                                v_a_1932_ = leanh::lean_ctor_get(v___x_1931_, 0);
                                leanh::lean_inc_n(v_a_1932_, 2);
                                leanh::lean_dec_ref_known(v___x_1931_, 1);
                                v___x_1933_ = l_Lean_mkAppN(v_a_1932_, v_snd_1928_);
                                leanh::lean_dec(v_snd_1928_);
                                v___x_1934_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_1911_, v___x_1933_, v_a_1917_);
                                v_isSharedCheck_1942_ =
                                    (!leanh::lean_is_exclusive(v___x_1934_)) as u8;
                                if v_isSharedCheck_1942_ == 0 {
                                    v_unused_1943_ = leanh::lean_ctor_get(v___x_1934_, 0);
                                    leanh::lean_dec(v_unused_1943_);
                                    v___x_1936_ = v___x_1934_;
                                    v_isShared_1937_ = v_isSharedCheck_1942_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1934_);
                                    v___x_1936_ = leanh::lean_box(0);
                                    v_isShared_1937_ = v_isSharedCheck_1942_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_snd_1928_);
                                leanh::lean_dec(v_mvarId_1911_);
                                v_a_1944_ = leanh::lean_ctor_get(v___x_1931_, 0);
                                v_isSharedCheck_1951_ =
                                    (!leanh::lean_is_exclusive(v___x_1931_)) as u8;
                                if v_isSharedCheck_1951_ == 0 {
                                    v___x_1946_ = v___x_1931_;
                                    v_isShared_1947_ = v_isSharedCheck_1951_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1944_);
                                    leanh::lean_dec(v___x_1931_);
                                    v___x_1946_ = leanh::lean_box(0);
                                    v_isShared_1947_ = v_isSharedCheck_1951_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_snd_1928_);
                            leanh::lean_dec(v_fst_1927_);
                            leanh::lean_dec(v_mvarId_1911_);
                            v_a_1952_ = leanh::lean_ctor_get(v___x_1929_, 0);
                            v_isSharedCheck_1959_ =
                                (!leanh::lean_is_exclusive(v___x_1929_)) as u8;
                            if v_isSharedCheck_1959_ == 0 {
                                v___x_1954_ = v___x_1929_;
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1952_);
                                leanh::lean_dec(v___x_1929_);
                                v___x_1954_ = leanh::lean_box(0);
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_1911_);
                        v_a_1960_ = leanh::lean_ctor_get(v___x_1925_, 0);
                        v_isSharedCheck_1967_ =
                            (!leanh::lean_is_exclusive(v___x_1925_)) as u8;
                        if v_isSharedCheck_1967_ == 0 {
                            v___x_1962_ = v___x_1925_;
                            v_isShared_1963_ = v_isSharedCheck_1967_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1960_);
                            leanh::lean_dec(v___x_1925_);
                            v___x_1962_ = leanh::lean_box(0);
                            v_isShared_1963_ = v_isSharedCheck_1967_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_aSizeEqN_1915_);
                    leanh::lean_dec(v_xNamePrefix_1914_);
                    leanh::lean_dec(v_n_1913_);
                    leanh::lean_dec_ref(v_a_1912_);
                    leanh::lean_dec(v_mvarId_1911_);
                    v_a_1968_ = leanh::lean_ctor_get(v___x_1921_, 0);
                    v_isSharedCheck_1975_ = (!leanh::lean_is_exclusive(v___x_1921_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1970_ = v___x_1921_;
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1968_);
                        leanh::lean_dec(v___x_1921_);
                        v___x_1970_ = leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1938_ = l_Lean_Expr_mvarId_x21(v_a_1932_);
                leanh::lean_dec(v_a_1932_);
                if v_isShared_1937_ == 0 {
                    leanh::lean_ctor_set(v___x_1936_, 0, v___x_1938_);
                    v___x_1940_ = v___x_1936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1940_;
            }
            3 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1949_;
            }
            5 => {
                if v_isShared_1955_ == 0 {
                    v___x_1957_ = v___x_1954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
                    v___x_1957_ = v_reuseFailAlloc_1958_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1957_;
            }
            7 => {
                if v_isShared_1963_ == 0 {
                    v___x_1965_ = v___x_1962_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
                    v___x_1965_ = v_reuseFailAlloc_1966_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1965_;
            }
            9 => {
                if v_isShared_1971_ == 0 {
                    v___x_1973_ = v___x_1970_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(
    mut v_mvarId_1976_: *mut leanh::LeanObject,
    mut v_a_1977_: *mut leanh::LeanObject,
    mut v_n_1978_: *mut leanh::LeanObject,
    mut v_xNamePrefix_1979_: *mut leanh::LeanObject,
    mut v_aSizeEqN_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
    mut v_a_1983_: *mut leanh::LeanObject,
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(
        v_mvarId_1976_,
        v_a_1977_,
        v_n_1978_,
        v_xNamePrefix_1979_,
        v_aSizeEqN_1980_,
        v_a_1981_,
        v_a_1982_,
        v_a_1983_,
        v_a_1984_,
    );
    leanh::lean_dec(v_a_1984_);
    leanh::lean_dec_ref(v_a_1983_);
    leanh::lean_dec(v_a_1982_);
    leanh::lean_dec_ref(v_a_1981_);
    return v_res_1986_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(
    mut v_mvarId_1987_: *mut leanh::LeanObject,
    mut v_val_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_1987_, v_val_1988_, v___y_1990_);
    return v___x_1994_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(
    mut v_mvarId_1995_: *mut leanh::LeanObject,
    mut v_val_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_1995_, v_val_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
    leanh::lean_dec(v___y_2000_);
    leanh::lean_dec_ref(v___y_1999_);
    leanh::lean_dec(v___y_1998_);
    leanh::lean_dec_ref(v___y_1997_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(
    mut v_00_u03b2_2003_: *mut leanh::LeanObject,
    mut v_x_2004_: *mut leanh::LeanObject,
    mut v_x_2005_: *mut leanh::LeanObject,
    mut v_x_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_x_2004_, v_x_2005_, v_x_2006_);
    return v___x_2007_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2008_: *mut leanh::LeanObject,
    mut v_x_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: usize,
    mut v_x_2011_: usize,
    mut v_x_2012_: *mut leanh::LeanObject,
    mut v_x_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_2009_, v_x_2010_, v_x_2011_, v_x_2012_, v_x_2013_);
    return v___x_2014_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2015_: *mut leanh::LeanObject,
    mut v_x_2016_: *mut leanh::LeanObject,
    mut v_x_2017_: *mut leanh::LeanObject,
    mut v_x_2018_: *mut leanh::LeanObject,
    mut v_x_2019_: *mut leanh::LeanObject,
    mut v_x_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1364__boxed_2021_: usize = 0;
    let mut v_x_1365__boxed_2022_: usize = 0;
    let mut v_res_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1364__boxed_2021_ = leanh::lean_unbox_usize(v_x_2017_);
    leanh::lean_dec(v_x_2017_);
    v_x_1365__boxed_2022_ = leanh::lean_unbox_usize(v_x_2018_);
    leanh::lean_dec(v_x_2018_);
    v_res_2023_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(v_00_u03b2_2015_, v_x_2016_, v_x_1364__boxed_2021_, v_x_1365__boxed_2022_, v_x_2019_, v_x_2020_);
    return v_res_2023_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2024_: *mut leanh::LeanObject,
    mut v_n_2025_: *mut leanh::LeanObject,
    mut v_k_2026_: *mut leanh::LeanObject,
    mut v_v_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2025_, v_k_2026_, v_v_2027_);
    return v___x_2028_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2029_: *mut leanh::LeanObject,
    mut v_depth_2030_: usize,
    mut v_keys_2031_: *mut leanh::LeanObject,
    mut v_vals_2032_: *mut leanh::LeanObject,
    mut v_heq_2033_: *mut leanh::LeanObject,
    mut v_i_2034_: *mut leanh::LeanObject,
    mut v_entries_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2030_, v_keys_2031_, v_vals_2032_, v_i_2034_, v_entries_2035_);
    return v___x_2036_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2037_: *mut leanh::LeanObject,
    mut v_depth_2038_: *mut leanh::LeanObject,
    mut v_keys_2039_: *mut leanh::LeanObject,
    mut v_vals_2040_: *mut leanh::LeanObject,
    mut v_heq_2041_: *mut leanh::LeanObject,
    mut v_i_2042_: *mut leanh::LeanObject,
    mut v_entries_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2044_: usize = 0;
    let mut v_res_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2044_ = leanh::lean_unbox_usize(v_depth_2038_);
    leanh::lean_dec(v_depth_2038_);
    v_res_2045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2037_, v_depth_boxed_2044_, v_keys_2039_, v_vals_2040_, v_heq_2041_, v_i_2042_, v_entries_2043_);
    leanh::lean_dec_ref(v_vals_2040_);
    leanh::lean_dec_ref(v_keys_2039_);
    return v_res_2045_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2046_: *mut leanh::LeanObject,
    mut v_x_2047_: *mut leanh::LeanObject,
    mut v_x_2048_: *mut leanh::LeanObject,
    mut v_x_2049_: *mut leanh::LeanObject,
    mut v_x_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2047_, v_x_2048_, v_x_2049_, v_x_2050_);
    return v___x_2051_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(
    mut v_mvarId_2052_: *mut leanh::LeanObject,
    mut v_x_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2063_: u8 = 0;
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_a_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2059_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2052_,
                    v_x_2053_,
                    v___y_2054_,
                    v___y_2055_,
                    v___y_2056_,
                    v___y_2057_,
                );
                if leanh::lean_obj_tag(v___x_2059_) == 0 {
                    v_a_2060_ = leanh::lean_ctor_get(v___x_2059_, 0);
                    v_isSharedCheck_2067_ = (!leanh::lean_is_exclusive(v___x_2059_)) as u8;
                    if v_isSharedCheck_2067_ == 0 {
                        v___x_2062_ = v___x_2059_;
                        v_isShared_2063_ = v_isSharedCheck_2067_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2060_);
                        leanh::lean_dec(v___x_2059_);
                        v___x_2062_ = leanh::lean_box(0);
                        v_isShared_2063_ = v_isSharedCheck_2067_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2068_ = leanh::lean_ctor_get(v___x_2059_, 0);
                    v_isSharedCheck_2075_ = (!leanh::lean_is_exclusive(v___x_2059_)) as u8;
                    if v_isSharedCheck_2075_ == 0 {
                        v___x_2070_ = v___x_2059_;
                        v_isShared_2071_ = v_isSharedCheck_2075_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2068_);
                        leanh::lean_dec(v___x_2059_);
                        v___x_2070_ = leanh::lean_box(0);
                        v_isShared_2071_ = v_isSharedCheck_2075_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2063_ == 0 {
                    v___x_2065_ = v___x_2062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
                    v___x_2065_ = v_reuseFailAlloc_2066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2065_;
            }
            3 => {
                if v_isShared_2071_ == 0 {
                    v___x_2073_ = v___x_2070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(
    mut v_mvarId_2076_: *mut leanh::LeanObject,
    mut v_x_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2083_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(
        v_mvarId_2076_,
        v_x_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
        v___y_2081_,
    );
    leanh::lean_dec(v___y_2081_);
    leanh::lean_dec_ref(v___y_2080_);
    leanh::lean_dec(v___y_2079_);
    leanh::lean_dec_ref(v___y_2078_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(
    mut v_00_u03b1_2084_: *mut leanh::LeanObject,
    mut v_mvarId_2085_: *mut leanh::LeanObject,
    mut v_x_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
    mut v___y_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(
        v_mvarId_2085_,
        v_x_2086_,
        v___y_2087_,
        v___y_2088_,
        v___y_2089_,
        v___y_2090_,
    );
    return v___x_2092_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(
    mut v_00_u03b1_2093_: *mut leanh::LeanObject,
    mut v_mvarId_2094_: *mut leanh::LeanObject,
    mut v_x_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(
        v_00_u03b1_2093_,
        v_mvarId_2094_,
        v_x_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
        v___y_2099_,
    );
    leanh::lean_dec(v___y_2099_);
    leanh::lean_dec_ref(v___y_2098_);
    leanh::lean_dec(v___y_2097_);
    leanh::lean_dec_ref(v___y_2096_);
    return v_res_2101_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(
    mut v_sz_2102_: usize,
    mut v_i_2103_: usize,
    mut v_bs_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2105_: u8 = 0;
    let mut v_v_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: usize = 0;
    let mut v___x_2111_: usize = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2105_ = lean_usize_dec_lt(v_i_2103_, v_sz_2102_);
                if v___x_2105_ == 0 {
                    return v_bs_2104_;
                } else {
                    v_v_2106_ = lean_array_uget(v_bs_2104_, v_i_2103_);
                    v___x_2107_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2108_ = lean_array_uset(v_bs_2104_, v_i_2103_, v___x_2107_);
                    v___x_2109_ = l_Lean_mkRawNatLit(v_v_2106_);
                    v___x_2110_ = 1usize;
                    v___x_2111_ = lean_usize_add(v_i_2103_, v___x_2110_);
                    v___x_2112_ = lean_array_uset(v_bs_x27_2108_, v_i_2103_, v___x_2109_);
                    v_i_2103_ = v___x_2111_;
                    v_bs_2104_ = v___x_2112_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(
    mut v_sz_2114_: *mut leanh::LeanObject,
    mut v_i_2115_: *mut leanh::LeanObject,
    mut v_bs_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2117_: usize = 0;
    let mut v_i_boxed_2118_: usize = 0;
    let mut v_res_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2117_ = leanh::lean_unbox_usize(v_sz_2114_);
    leanh::lean_dec(v_sz_2114_);
    v_i_boxed_2118_ = leanh::lean_unbox_usize(v_i_2115_);
    leanh::lean_dec(v_i_2115_);
    v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_boxed_2117_, v_i_boxed_2118_, v_bs_2116_);
    return v_res_2119_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(
    mut v___x_2120_: *mut leanh::LeanObject,
    mut v_mvarId_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v___x_2123_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2124_: *mut leanh::LeanObject,
    mut v_isZero_2125_: u8,
    mut v___x_2126_: *mut leanh::LeanObject,
    mut v_subst_2127_: *mut leanh::LeanObject,
    mut v___x_2128_: u8,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v_fst_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v_a_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2173_: u8 = 0;
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v_a_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_a_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_a_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2134_ = l_Lean_Meta_mkEqSymm(
                    v___x_2120_,
                    v___y_2129_,
                    v___y_2130_,
                    v___y_2131_,
                    v___y_2132_,
                );
                if leanh::lean_obj_tag(v___x_2134_) == 0 {
                    v_a_2135_ = leanh::lean_ctor_get(v___x_2134_, 0);
                    leanh::lean_inc(v_a_2135_);
                    leanh::lean_dec_ref_known(v___x_2134_, 1);
                    leanh::lean_inc(v___x_2123_);
                    v___x_2136_ =
                        l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(
                            v_mvarId_2121_,
                            v_a_2122_,
                            v___x_2123_,
                            v_xNamePrefix_2124_,
                            v_a_2135_,
                            v___y_2129_,
                            v___y_2130_,
                            v___y_2131_,
                            v___y_2132_,
                        );
                    if leanh::lean_obj_tag(v___x_2136_) == 0 {
                        v_a_2137_ = leanh::lean_ctor_get(v___x_2136_, 0);
                        leanh::lean_inc(v_a_2137_);
                        leanh::lean_dec_ref_known(v___x_2136_, 1);
                        v___x_2138_ = leanh::lean_box(0);
                        v___x_2139_ = l_Lean_Meta_introNCore(
                            v_a_2137_,
                            v___x_2123_,
                            v___x_2138_,
                            v_isZero_2125_,
                            v_isZero_2125_,
                            v___y_2129_,
                            v___y_2130_,
                            v___y_2131_,
                            v___y_2132_,
                        );
                        if leanh::lean_obj_tag(v___x_2139_) == 0 {
                            v_a_2140_ = leanh::lean_ctor_get(v___x_2139_, 0);
                            leanh::lean_inc(v_a_2140_);
                            leanh::lean_dec_ref_known(v___x_2139_, 1);
                            v_fst_2141_ = leanh::lean_ctor_get(v_a_2140_, 0);
                            leanh::lean_inc(v_fst_2141_);
                            v_snd_2142_ = leanh::lean_ctor_get(v_a_2140_, 1);
                            leanh::lean_inc(v_snd_2142_);
                            leanh::lean_dec(v_a_2140_);
                            v___x_2143_ = l_Lean_Meta_intro1Core(
                                v_snd_2142_,
                                v_isZero_2125_,
                                v___y_2129_,
                                v___y_2130_,
                                v___y_2131_,
                                v___y_2132_,
                            );
                            if leanh::lean_obj_tag(v___x_2143_) == 0 {
                                v_a_2144_ = leanh::lean_ctor_get(v___x_2143_, 0);
                                leanh::lean_inc(v_a_2144_);
                                leanh::lean_dec_ref_known(v___x_2143_, 1);
                                v_fst_2145_ = leanh::lean_ctor_get(v_a_2144_, 0);
                                leanh::lean_inc(v_fst_2145_);
                                v_snd_2146_ = leanh::lean_ctor_get(v_a_2144_, 1);
                                leanh::lean_inc(v_snd_2146_);
                                leanh::lean_dec(v_a_2144_);
                                v___x_2147_ = l_Lean_MVarId_clear(
                                    v_snd_2146_,
                                    v___x_2126_,
                                    v___y_2129_,
                                    v___y_2130_,
                                    v___y_2131_,
                                    v___y_2132_,
                                );
                                if leanh::lean_obj_tag(v___x_2147_) == 0 {
                                    v_a_2148_ = leanh::lean_ctor_get(v___x_2147_, 0);
                                    leanh::lean_inc(v_a_2148_);
                                    leanh::lean_dec_ref_known(v___x_2147_, 1);
                                    v___x_2149_ = l_Lean_Meta_substCore(
                                        v_a_2148_,
                                        v_fst_2145_,
                                        v_isZero_2125_,
                                        v_subst_2127_,
                                        v___x_2128_,
                                        v_isZero_2125_,
                                        v___y_2129_,
                                        v___y_2130_,
                                        v___y_2131_,
                                        v___y_2132_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2149_) == 0 {
                                        v_a_2150_ = leanh::lean_ctor_get(v___x_2149_, 0);
                                        v_isSharedCheck_2161_ =
                                            (!leanh::lean_is_exclusive(v___x_2149_)) as u8;
                                        if v_isSharedCheck_2161_ == 0 {
                                            v___x_2152_ = v___x_2149_;
                                            v_isShared_2153_ = v_isSharedCheck_2161_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2150_);
                                            leanh::lean_dec(v___x_2149_);
                                            v___x_2152_ = leanh::lean_box(0);
                                            v_isShared_2153_ = v_isSharedCheck_2161_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_fst_2141_);
                                        v_a_2162_ = leanh::lean_ctor_get(v___x_2149_, 0);
                                        v_isSharedCheck_2169_ =
                                            (!leanh::lean_is_exclusive(v___x_2149_)) as u8;
                                        if v_isSharedCheck_2169_ == 0 {
                                            v___x_2164_ = v___x_2149_;
                                            v_isShared_2165_ = v_isSharedCheck_2169_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2162_);
                                            leanh::lean_dec(v___x_2149_);
                                            v___x_2164_ = leanh::lean_box(0);
                                            v_isShared_2165_ = v_isSharedCheck_2169_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_fst_2145_);
                                    leanh::lean_dec(v_fst_2141_);
                                    leanh::lean_dec(v_subst_2127_);
                                    v_a_2170_ = leanh::lean_ctor_get(v___x_2147_, 0);
                                    v_isSharedCheck_2177_ =
                                        (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                                    if v_isSharedCheck_2177_ == 0 {
                                        v___x_2172_ = v___x_2147_;
                                        v_isShared_2173_ = v_isSharedCheck_2177_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2170_);
                                        leanh::lean_dec(v___x_2147_);
                                        v___x_2172_ = leanh::lean_box(0);
                                        v_isShared_2173_ = v_isSharedCheck_2177_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_fst_2141_);
                                leanh::lean_dec(v_subst_2127_);
                                leanh::lean_dec(v___x_2126_);
                                v_a_2178_ = leanh::lean_ctor_get(v___x_2143_, 0);
                                v_isSharedCheck_2185_ =
                                    (!leanh::lean_is_exclusive(v___x_2143_)) as u8;
                                if v_isSharedCheck_2185_ == 0 {
                                    v___x_2180_ = v___x_2143_;
                                    v_isShared_2181_ = v_isSharedCheck_2185_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2178_);
                                    leanh::lean_dec(v___x_2143_);
                                    v___x_2180_ = leanh::lean_box(0);
                                    v_isShared_2181_ = v_isSharedCheck_2185_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_subst_2127_);
                            leanh::lean_dec(v___x_2126_);
                            v_a_2186_ = leanh::lean_ctor_get(v___x_2139_, 0);
                            v_isSharedCheck_2193_ =
                                (!leanh::lean_is_exclusive(v___x_2139_)) as u8;
                            if v_isSharedCheck_2193_ == 0 {
                                v___x_2188_ = v___x_2139_;
                                v_isShared_2189_ = v_isSharedCheck_2193_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2186_);
                                leanh::lean_dec(v___x_2139_);
                                v___x_2188_ = leanh::lean_box(0);
                                v_isShared_2189_ = v_isSharedCheck_2193_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_subst_2127_);
                        leanh::lean_dec(v___x_2126_);
                        leanh::lean_dec(v___x_2123_);
                        v_a_2194_ = leanh::lean_ctor_get(v___x_2136_, 0);
                        v_isSharedCheck_2201_ =
                            (!leanh::lean_is_exclusive(v___x_2136_)) as u8;
                        if v_isSharedCheck_2201_ == 0 {
                            v___x_2196_ = v___x_2136_;
                            v_isShared_2197_ = v_isSharedCheck_2201_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2194_);
                            leanh::lean_dec(v___x_2136_);
                            v___x_2196_ = leanh::lean_box(0);
                            v_isShared_2197_ = v_isSharedCheck_2201_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_subst_2127_);
                    leanh::lean_dec(v___x_2126_);
                    leanh::lean_dec(v_xNamePrefix_2124_);
                    leanh::lean_dec(v___x_2123_);
                    leanh::lean_dec_ref(v_a_2122_);
                    leanh::lean_dec(v_mvarId_2121_);
                    v_a_2202_ = leanh::lean_ctor_get(v___x_2134_, 0);
                    v_isSharedCheck_2209_ = (!leanh::lean_is_exclusive(v___x_2134_)) as u8;
                    if v_isSharedCheck_2209_ == 0 {
                        v___x_2204_ = v___x_2134_;
                        v_isShared_2205_ = v_isSharedCheck_2209_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2202_);
                        leanh::lean_dec(v___x_2134_);
                        v___x_2204_ = leanh::lean_box(0);
                        v_isShared_2205_ = v_isSharedCheck_2209_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2154_ = leanh::lean_ctor_get(v_a_2150_, 0);
                leanh::lean_inc(v_fst_2154_);
                v_snd_2155_ = leanh::lean_ctor_get(v_a_2150_, 1);
                leanh::lean_inc(v_snd_2155_);
                leanh::lean_dec(v_a_2150_);
                v___x_2156_ = l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0;
                v___x_2157_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2157_, 0, v_snd_2155_);
                leanh::lean_ctor_set(v___x_2157_, 1, v_fst_2141_);
                leanh::lean_ctor_set(v___x_2157_, 2, v___x_2156_);
                leanh::lean_ctor_set(v___x_2157_, 3, v_fst_2154_);
                if v_isShared_2153_ == 0 {
                    leanh::lean_ctor_set(v___x_2152_, 0, v___x_2157_);
                    v___x_2159_ = v___x_2152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
                    v___x_2159_ = v_reuseFailAlloc_2160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2159_;
            }
            3 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2167_;
            }
            5 => {
                if v_isShared_2173_ == 0 {
                    v___x_2175_ = v___x_2172_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
                    v___x_2175_ = v_reuseFailAlloc_2176_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2175_;
            }
            7 => {
                if v_isShared_2181_ == 0 {
                    v___x_2183_ = v___x_2180_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2183_;
            }
            9 => {
                if v_isShared_2189_ == 0 {
                    v___x_2191_ = v___x_2188_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
                    v___x_2191_ = v_reuseFailAlloc_2192_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2191_;
            }
            11 => {
                if v_isShared_2197_ == 0 {
                    v___x_2199_ = v___x_2196_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2199_;
            }
            13 => {
                if v_isShared_2205_ == 0 {
                    v___x_2207_ = v___x_2204_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(
    mut v___x_2210_: *mut leanh::LeanObject,
    mut v_mvarId_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v___x_2213_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2214_: *mut leanh::LeanObject,
    mut v_isZero_2215_: *mut leanh::LeanObject,
    mut v___x_2216_: *mut leanh::LeanObject,
    mut v_subst_2217_: *mut leanh::LeanObject,
    mut v___x_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
    mut v___y_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isZero_boxed_2224_: u8 = 0;
    let mut v___x_3732__boxed_2225_: u8 = 0;
    let mut v_res_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_2224_ = (leanh::lean_unbox(v_isZero_2215_) as u8);
    v___x_3732__boxed_2225_ = (leanh::lean_unbox(v___x_2218_) as u8);
    v_res_2226_ =
        l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(
            v___x_2210_,
            v_mvarId_2211_,
            v_a_2212_,
            v___x_2213_,
            v_xNamePrefix_2214_,
            v_isZero_boxed_2224_,
            v___x_2216_,
            v_subst_2217_,
            v___x_3732__boxed_2225_,
            v___y_2219_,
            v___y_2220_,
            v___y_2221_,
            v___y_2222_,
        );
    leanh::lean_dec(v___y_2222_);
    leanh::lean_dec_ref(v___y_2221_);
    leanh::lean_dec(v___y_2220_);
    leanh::lean_dec_ref(v___y_2219_);
    return v_res_2226_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(
    mut v_fst_2227_: *mut leanh::LeanObject,
    mut v_sz_2228_: usize,
    mut v_i_2229_: usize,
    mut v_bs_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v_v_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
                if v___x_2231_ == 0 {
                    return v_bs_2230_;
                } else {
                    v_v_2232_ = lean_array_uget(v_bs_2230_, v_i_2229_);
                    v___x_2233_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2234_ = lean_array_uset(v_bs_2230_, v_i_2229_, v___x_2233_);
                    v___x_2235_ = l_Lean_Meta_FVarSubst_get(v_fst_2227_, v_v_2232_);
                    v___x_2236_ = l_Lean_Expr_fvarId_x21(v___x_2235_);
                    leanh::lean_dec_ref(v___x_2235_);
                    v___x_2237_ = 1usize;
                    v___x_2238_ = lean_usize_add(v_i_2229_, v___x_2237_);
                    v___x_2239_ = lean_array_uset(v_bs_x27_2234_, v_i_2229_, v___x_2236_);
                    v_i_2229_ = v___x_2238_;
                    v_bs_2230_ = v___x_2239_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(
    mut v_fst_2241_: *mut leanh::LeanObject,
    mut v_sz_2242_: *mut leanh::LeanObject,
    mut v_i_2243_: *mut leanh::LeanObject,
    mut v_bs_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2245_: usize = 0;
    let mut v_i_boxed_2246_: usize = 0;
    let mut v_res_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2245_ = leanh::lean_unbox_usize(v_sz_2242_);
    leanh::lean_dec(v_sz_2242_);
    v_i_boxed_2246_ = leanh::lean_unbox_usize(v_i_2243_);
    leanh::lean_dec(v_i_2243_);
    v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_2241_, v_sz_boxed_2245_, v_i_boxed_2246_, v_bs_2244_);
    leanh::lean_dec(v_fst_2241_);
    return v_res_2247_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(
    mut v_sizes_2248_: *mut leanh::LeanObject,
    mut v_fst_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2251_: *mut leanh::LeanObject,
    mut v_as_2252_: *mut leanh::LeanObject,
    mut v_i_2253_: *mut leanh::LeanObject,
    mut v_j_2254_: *mut leanh::LeanObject,
    mut v_bs_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
    mut v___y_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2262_: u8 = 0;
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newHs_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: u8 = 0;
    let mut v_one_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2282_: usize = 0;
    let mut v___x_2283_: usize = 0;
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2261_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2262_ = lean_nat_dec_eq(v_i_2253_, v_zero_2261_);
                if v_isZero_2262_ == 1 {
                    leanh::lean_dec(v_j_2254_);
                    leanh::lean_dec(v_i_2253_);
                    leanh::lean_dec(v_xNamePrefix_2251_);
                    leanh::lean_dec_ref(v_a_2250_);
                    leanh::lean_dec(v_fst_2249_);
                    v___x_2263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2263_, 0, v_bs_2255_);
                    return v___x_2263_;
                } else {
                    v___x_2264_ = lean_array_fget_borrowed(v_as_2252_, v_j_2254_);
                    v_mvarId_2265_ = leanh::lean_ctor_get(v___x_2264_, 0);
                    v_newHs_2266_ = leanh::lean_ctor_get(v___x_2264_, 1);
                    v_subst_2267_ = leanh::lean_ctor_get(v___x_2264_, 2);
                    v___x_2268_ = 1;
                    v_one_2269_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2270_ = lean_nat_sub(v_i_2253_, v_one_2269_);
                    leanh::lean_dec(v_i_2253_);
                    v___x_2276_ = lean_array_get_size(v_sizes_2248_);
                    v___x_2277_ = lean_nat_dec_lt(v_j_2254_, v___x_2276_);
                    if v___x_2277_ == 0 {
                        leanh::lean_inc(v_subst_2267_);
                        leanh::lean_inc(v_fst_2249_);
                        leanh::lean_inc(v_mvarId_2265_);
                        v___x_2278_ = l_Lean_Meta_substCore(
                            v_mvarId_2265_,
                            v_fst_2249_,
                            v___x_2277_,
                            v_subst_2267_,
                            v___x_2268_,
                            v___x_2277_,
                            v___y_2256_,
                            v___y_2257_,
                            v___y_2258_,
                            v___y_2259_,
                        );
                        if leanh::lean_obj_tag(v___x_2278_) == 0 {
                            v_a_2279_ = leanh::lean_ctor_get(v___x_2278_, 0);
                            leanh::lean_inc(v_a_2279_);
                            leanh::lean_dec_ref_known(v___x_2278_, 1);
                            v_fst_2280_ = leanh::lean_ctor_get(v_a_2279_, 0);
                            leanh::lean_inc(v_fst_2280_);
                            v_snd_2281_ = leanh::lean_ctor_get(v_a_2279_, 1);
                            leanh::lean_inc(v_snd_2281_);
                            leanh::lean_dec(v_a_2279_);
                            v_sz_2282_ = lean_array_size(v_newHs_2266_);
                            v___x_2283_ = 0usize;
                            leanh::lean_inc_ref(v_newHs_2266_);
                            v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_2280_, v_sz_2282_, v___x_2283_, v_newHs_2266_);
                            v___x_2285_ =
                                l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0;
                            v___x_2286_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2286_, 0, v_snd_2281_);
                            leanh::lean_ctor_set(v___x_2286_, 1, v___x_2285_);
                            leanh::lean_ctor_set(v___x_2286_, 2, v___x_2284_);
                            leanh::lean_ctor_set(v___x_2286_, 3, v_fst_2280_);
                            v_a_2272_ = v___x_2286_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_n_2270_);
                            leanh::lean_dec_ref(v_bs_2255_);
                            leanh::lean_dec(v_j_2254_);
                            leanh::lean_dec(v_xNamePrefix_2251_);
                            leanh::lean_dec_ref(v_a_2250_);
                            leanh::lean_dec(v_fst_2249_);
                            v_a_2287_ = leanh::lean_ctor_get(v___x_2278_, 0);
                            v_isSharedCheck_2294_ =
                                (!leanh::lean_is_exclusive(v___x_2278_)) as u8;
                            if v_isSharedCheck_2294_ == 0 {
                                v___x_2289_ = v___x_2278_;
                                v_isShared_2290_ = v_isSharedCheck_2294_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2287_);
                                leanh::lean_dec(v___x_2278_);
                                v___x_2289_ = leanh::lean_box(0);
                                v_isShared_2290_ = v_isSharedCheck_2294_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_fst_2249_);
                        v___x_2295_ = l_Lean_Meta_FVarSubst_get(v_subst_2267_, v_fst_2249_);
                        v___x_2296_ = l_Lean_Expr_fvarId_x21(v___x_2295_);
                        leanh::lean_dec_ref(v___x_2295_);
                        v___x_2297_ = lean_array_fget_borrowed(v_sizes_2248_, v_j_2254_);
                        leanh::lean_inc(v___x_2296_);
                        v___x_2298_ = l_Lean_mkFVar(v___x_2296_);
                        v___x_2299_ = leanh::lean_box((v_isZero_2262_) as usize);
                        v___x_2300_ = leanh::lean_box((v___x_2268_) as usize);
                        leanh::lean_inc(v_subst_2267_);
                        leanh::lean_inc(v_xNamePrefix_2251_);
                        leanh::lean_inc(v___x_2297_);
                        leanh::lean_inc_ref(v_a_2250_);
                        leanh::lean_inc_n(v_mvarId_2265_, 2);
                        v___f_2301_ = leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        leanh::lean_closure_set(v___f_2301_, 0, v___x_2298_);
                        leanh::lean_closure_set(v___f_2301_, 1, v_mvarId_2265_);
                        leanh::lean_closure_set(v___f_2301_, 2, v_a_2250_);
                        leanh::lean_closure_set(v___f_2301_, 3, v___x_2297_);
                        leanh::lean_closure_set(v___f_2301_, 4, v_xNamePrefix_2251_);
                        leanh::lean_closure_set(v___f_2301_, 5, v___x_2299_);
                        leanh::lean_closure_set(v___f_2301_, 6, v___x_2296_);
                        leanh::lean_closure_set(v___f_2301_, 7, v_subst_2267_);
                        leanh::lean_closure_set(v___f_2301_, 8, v___x_2300_);
                        v___x_2302_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_2265_, v___f_2301_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
                        if leanh::lean_obj_tag(v___x_2302_) == 0 {
                            v_a_2303_ = leanh::lean_ctor_get(v___x_2302_, 0);
                            leanh::lean_inc(v_a_2303_);
                            leanh::lean_dec_ref_known(v___x_2302_, 1);
                            v_a_2272_ = v_a_2303_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_n_2270_);
                            leanh::lean_dec_ref(v_bs_2255_);
                            leanh::lean_dec(v_j_2254_);
                            leanh::lean_dec(v_xNamePrefix_2251_);
                            leanh::lean_dec_ref(v_a_2250_);
                            leanh::lean_dec(v_fst_2249_);
                            v_a_2304_ = leanh::lean_ctor_get(v___x_2302_, 0);
                            v_isSharedCheck_2311_ =
                                (!leanh::lean_is_exclusive(v___x_2302_)) as u8;
                            if v_isSharedCheck_2311_ == 0 {
                                v___x_2306_ = v___x_2302_;
                                v_isShared_2307_ = v_isSharedCheck_2311_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2304_);
                                leanh::lean_dec(v___x_2302_);
                                v___x_2306_ = leanh::lean_box(0);
                                v_isShared_2307_ = v_isSharedCheck_2311_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2273_ = lean_nat_add(v_j_2254_, v_one_2269_);
                leanh::lean_dec(v_j_2254_);
                v___x_2274_ = lean_array_push(v_bs_2255_, v_a_2272_);
                v_i_2253_ = v_n_2270_;
                v_j_2254_ = v___x_2273_;
                v_bs_2255_ = v___x_2274_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2290_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2292_;
            }
            4 => {
                if v_isShared_2307_ == 0 {
                    v___x_2309_ = v___x_2306_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
                    v___x_2309_ = v_reuseFailAlloc_2310_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(
    mut v_sizes_2312_: *mut leanh::LeanObject,
    mut v_fst_2313_: *mut leanh::LeanObject,
    mut v_a_2314_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2315_: *mut leanh::LeanObject,
    mut v_as_2316_: *mut leanh::LeanObject,
    mut v_i_2317_: *mut leanh::LeanObject,
    mut v_j_2318_: *mut leanh::LeanObject,
    mut v_bs_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2325_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(
        v_sizes_2312_,
        v_fst_2313_,
        v_a_2314_,
        v_xNamePrefix_2315_,
        v_as_2316_,
        v_i_2317_,
        v_j_2318_,
        v_bs_2319_,
        v___y_2320_,
        v___y_2321_,
        v___y_2322_,
        v___y_2323_,
    );
    leanh::lean_dec(v___y_2323_);
    leanh::lean_dec_ref(v___y_2322_);
    leanh::lean_dec(v___y_2321_);
    leanh::lean_dec_ref(v___y_2320_);
    leanh::lean_dec_ref(v_as_2316_);
    leanh::lean_dec_ref(v_sizes_2312_);
    return v_res_2325_;
}
pub unsafe fn _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = leanh::lean_box(0);
    v___x_2333_ = l_Lean_Meta_caseArraySizes___lam__0___closed__3;
    v___x_2334_ = l_Lean_mkConst(v___x_2333_, v___x_2332_);
    return v___x_2334_;
}
pub unsafe fn l_Lean_Meta_caseArraySizes___lam__0(
    mut v___x_2338_: *mut leanh::LeanObject,
    mut v___x_2339_: *mut leanh::LeanObject,
    mut v_mvarId_2340_: *mut leanh::LeanObject,
    mut v_sizes_2341_: *mut leanh::LeanObject,
    mut v_hNamePrefix_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2366_: usize = 0;
    let mut v___x_2367_: usize = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_a_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v_a_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2395_: u8 = 0;
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_a_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v_a_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2350_ = l_Lean_Meta_mkAppM(
                    v___x_2338_,
                    v___x_2339_,
                    v___y_2345_,
                    v___y_2346_,
                    v___y_2347_,
                    v___y_2348_,
                );
                if leanh::lean_obj_tag(v___x_2350_) == 0 {
                    v_a_2351_ = leanh::lean_ctor_get(v___x_2350_, 0);
                    leanh::lean_inc(v_a_2351_);
                    leanh::lean_dec_ref_known(v___x_2350_, 1);
                    v___x_2352_ = l_Lean_Meta_caseArraySizes___lam__0___closed__1;
                    v___x_2353_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_caseArraySizes___lam__0___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_caseArraySizes___lam__0___closed__4_once
                        ),
                        _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4,
                    );
                    v___x_2354_ = l_Lean_Meta_caseArraySizes___lam__0___closed__6;
                    v___x_2355_ = l_Lean_MVarId_assertExt(
                        v_mvarId_2340_,
                        v___x_2352_,
                        v___x_2353_,
                        v_a_2351_,
                        v___x_2354_,
                        v___y_2345_,
                        v___y_2346_,
                        v___y_2347_,
                        v___y_2348_,
                    );
                    if leanh::lean_obj_tag(v___x_2355_) == 0 {
                        v_a_2356_ = leanh::lean_ctor_get(v___x_2355_, 0);
                        leanh::lean_inc(v_a_2356_);
                        leanh::lean_dec_ref_known(v___x_2355_, 1);
                        v___x_2357_ = 0;
                        v___x_2358_ = l_Lean_Meta_intro1Core(
                            v_a_2356_,
                            v___x_2357_,
                            v___y_2345_,
                            v___y_2346_,
                            v___y_2347_,
                            v___y_2348_,
                        );
                        if leanh::lean_obj_tag(v___x_2358_) == 0 {
                            v_a_2359_ = leanh::lean_ctor_get(v___x_2358_, 0);
                            leanh::lean_inc(v_a_2359_);
                            leanh::lean_dec_ref_known(v___x_2358_, 1);
                            v_fst_2360_ = leanh::lean_ctor_get(v_a_2359_, 0);
                            leanh::lean_inc(v_fst_2360_);
                            v_snd_2361_ = leanh::lean_ctor_get(v_a_2359_, 1);
                            leanh::lean_inc(v_snd_2361_);
                            leanh::lean_dec(v_a_2359_);
                            v___x_2362_ = l_Lean_Meta_intro1Core(
                                v_snd_2361_,
                                v___x_2357_,
                                v___y_2345_,
                                v___y_2346_,
                                v___y_2347_,
                                v___y_2348_,
                            );
                            if leanh::lean_obj_tag(v___x_2362_) == 0 {
                                v_a_2363_ = leanh::lean_ctor_get(v___x_2362_, 0);
                                leanh::lean_inc(v_a_2363_);
                                leanh::lean_dec_ref_known(v___x_2362_, 1);
                                v_fst_2364_ = leanh::lean_ctor_get(v_a_2363_, 0);
                                leanh::lean_inc(v_fst_2364_);
                                v_snd_2365_ = leanh::lean_ctor_get(v_a_2363_, 1);
                                leanh::lean_inc(v_snd_2365_);
                                leanh::lean_dec(v_a_2363_);
                                v_sz_2366_ = lean_array_size(v_sizes_2341_);
                                v___x_2367_ = 0usize;
                                leanh::lean_inc_ref(v_sizes_2341_);
                                v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_2366_, v___x_2367_, v_sizes_2341_);
                                v___x_2369_ = 1;
                                v___x_2370_ = l_Lean_Meta_caseValues(
                                    v_snd_2365_,
                                    v_fst_2360_,
                                    v___x_2368_,
                                    v_hNamePrefix_2342_,
                                    v___x_2369_,
                                    v___y_2345_,
                                    v___y_2346_,
                                    v___y_2347_,
                                    v___y_2348_,
                                );
                                if leanh::lean_obj_tag(v___x_2370_) == 0 {
                                    v_a_2371_ = leanh::lean_ctor_get(v___x_2370_, 0);
                                    leanh::lean_inc(v_a_2371_);
                                    leanh::lean_dec_ref_known(v___x_2370_, 1);
                                    v___x_2372_ = lean_array_get_size(v_a_2371_);
                                    v___x_2373_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2372_);
                                    v___x_2375_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_2341_, v_fst_2364_, v_a_2343_, v_xNamePrefix_2344_, v_a_2371_, v___x_2372_, v___x_2373_, v___x_2374_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
                                    leanh::lean_dec(v_a_2371_);
                                    leanh::lean_dec_ref(v_sizes_2341_);
                                    return v___x_2375_;
                                } else {
                                    leanh::lean_dec(v_fst_2364_);
                                    leanh::lean_dec(v_xNamePrefix_2344_);
                                    leanh::lean_dec_ref(v_a_2343_);
                                    leanh::lean_dec_ref(v_sizes_2341_);
                                    v_a_2376_ = leanh::lean_ctor_get(v___x_2370_, 0);
                                    v_isSharedCheck_2383_ =
                                        (!leanh::lean_is_exclusive(v___x_2370_)) as u8;
                                    if v_isSharedCheck_2383_ == 0 {
                                        v___x_2378_ = v___x_2370_;
                                        v_isShared_2379_ = v_isSharedCheck_2383_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2376_);
                                        leanh::lean_dec(v___x_2370_);
                                        v___x_2378_ = leanh::lean_box(0);
                                        v_isShared_2379_ = v_isSharedCheck_2383_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_fst_2360_);
                                leanh::lean_dec(v_xNamePrefix_2344_);
                                leanh::lean_dec_ref(v_a_2343_);
                                leanh::lean_dec(v_hNamePrefix_2342_);
                                leanh::lean_dec_ref(v_sizes_2341_);
                                v_a_2384_ = leanh::lean_ctor_get(v___x_2362_, 0);
                                v_isSharedCheck_2391_ =
                                    (!leanh::lean_is_exclusive(v___x_2362_)) as u8;
                                if v_isSharedCheck_2391_ == 0 {
                                    v___x_2386_ = v___x_2362_;
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2384_);
                                    leanh::lean_dec(v___x_2362_);
                                    v___x_2386_ = leanh::lean_box(0);
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_xNamePrefix_2344_);
                            leanh::lean_dec_ref(v_a_2343_);
                            leanh::lean_dec(v_hNamePrefix_2342_);
                            leanh::lean_dec_ref(v_sizes_2341_);
                            v_a_2392_ = leanh::lean_ctor_get(v___x_2358_, 0);
                            v_isSharedCheck_2399_ =
                                (!leanh::lean_is_exclusive(v___x_2358_)) as u8;
                            if v_isSharedCheck_2399_ == 0 {
                                v___x_2394_ = v___x_2358_;
                                v_isShared_2395_ = v_isSharedCheck_2399_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2392_);
                                leanh::lean_dec(v___x_2358_);
                                v___x_2394_ = leanh::lean_box(0);
                                v_isShared_2395_ = v_isSharedCheck_2399_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_xNamePrefix_2344_);
                        leanh::lean_dec_ref(v_a_2343_);
                        leanh::lean_dec(v_hNamePrefix_2342_);
                        leanh::lean_dec_ref(v_sizes_2341_);
                        v_a_2400_ = leanh::lean_ctor_get(v___x_2355_, 0);
                        v_isSharedCheck_2407_ =
                            (!leanh::lean_is_exclusive(v___x_2355_)) as u8;
                        if v_isSharedCheck_2407_ == 0 {
                            v___x_2402_ = v___x_2355_;
                            v_isShared_2403_ = v_isSharedCheck_2407_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2400_);
                            leanh::lean_dec(v___x_2355_);
                            v___x_2402_ = leanh::lean_box(0);
                            v_isShared_2403_ = v_isSharedCheck_2407_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_xNamePrefix_2344_);
                    leanh::lean_dec_ref(v_a_2343_);
                    leanh::lean_dec(v_hNamePrefix_2342_);
                    leanh::lean_dec_ref(v_sizes_2341_);
                    leanh::lean_dec(v_mvarId_2340_);
                    v_a_2408_ = leanh::lean_ctor_get(v___x_2350_, 0);
                    v_isSharedCheck_2415_ = (!leanh::lean_is_exclusive(v___x_2350_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2410_ = v___x_2350_;
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2408_);
                        leanh::lean_dec(v___x_2350_);
                        v___x_2410_ = leanh::lean_box(0);
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2379_ == 0 {
                    v___x_2381_ = v___x_2378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
                    v___x_2381_ = v_reuseFailAlloc_2382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2381_;
            }
            3 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2389_;
            }
            5 => {
                if v_isShared_2395_ == 0 {
                    v___x_2397_ = v___x_2394_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
                    v___x_2397_ = v_reuseFailAlloc_2398_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2397_;
            }
            7 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2405_;
            }
            9 => {
                if v_isShared_2411_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_caseArraySizes___lam__0___boxed(
    mut v___x_2416_: *mut leanh::LeanObject,
    mut v___x_2417_: *mut leanh::LeanObject,
    mut v_mvarId_2418_: *mut leanh::LeanObject,
    mut v_sizes_2419_: *mut leanh::LeanObject,
    mut v_hNamePrefix_2420_: *mut leanh::LeanObject,
    mut v_a_2421_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
    mut v___y_2425_: *mut leanh::LeanObject,
    mut v___y_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_Lean_Meta_caseArraySizes___lam__0(
        v___x_2416_,
        v___x_2417_,
        v_mvarId_2418_,
        v_sizes_2419_,
        v_hNamePrefix_2420_,
        v_a_2421_,
        v_xNamePrefix_2422_,
        v___y_2423_,
        v___y_2424_,
        v___y_2425_,
        v___y_2426_,
    );
    leanh::lean_dec(v___y_2426_);
    leanh::lean_dec_ref(v___y_2425_);
    leanh::lean_dec(v___y_2424_);
    leanh::lean_dec_ref(v___y_2423_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_Meta_caseArraySizes(
    mut v_mvarId_2433_: *mut leanh::LeanObject,
    mut v_fvarId_2434_: *mut leanh::LeanObject,
    mut v_sizes_2435_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2436_: *mut leanh::LeanObject,
    mut v_hNamePrefix_2437_: *mut leanh::LeanObject,
    mut v_a_2438_: *mut leanh::LeanObject,
    mut v_a_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_2443_ = l_Lean_mkFVar(v_fvarId_2434_);
    v___x_2444_ = l_Lean_Meta_caseArraySizes___closed__1;
    v___x_2445_ = leanh::lean_unsigned_to_nat(1);
    v___x_2446_ = lean_mk_empty_array_with_capacity(v___x_2445_);
    leanh::lean_inc_ref(v_a_2443_);
    v___x_2447_ = lean_array_push(v___x_2446_, v_a_2443_);
    leanh::lean_inc(v_mvarId_2433_);
    v___f_2448_ = leanh::lean_alloc_closure(
        l_Lean_Meta_caseArraySizes___lam__0___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___f_2448_, 0, v___x_2444_);
    leanh::lean_closure_set(v___f_2448_, 1, v___x_2447_);
    leanh::lean_closure_set(v___f_2448_, 2, v_mvarId_2433_);
    leanh::lean_closure_set(v___f_2448_, 3, v_sizes_2435_);
    leanh::lean_closure_set(v___f_2448_, 4, v_hNamePrefix_2437_);
    leanh::lean_closure_set(v___f_2448_, 5, v_a_2443_);
    leanh::lean_closure_set(v___f_2448_, 6, v_xNamePrefix_2436_);
    v___x_2449_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(
        v_mvarId_2433_,
        v___f_2448_,
        v_a_2438_,
        v_a_2439_,
        v_a_2440_,
        v_a_2441_,
    );
    return v___x_2449_;
}
pub unsafe fn l_Lean_Meta_caseArraySizes___boxed(
    mut v_mvarId_2450_: *mut leanh::LeanObject,
    mut v_fvarId_2451_: *mut leanh::LeanObject,
    mut v_sizes_2452_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2453_: *mut leanh::LeanObject,
    mut v_hNamePrefix_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
    mut v_a_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2460_ = l_Lean_Meta_caseArraySizes(
        v_mvarId_2450_,
        v_fvarId_2451_,
        v_sizes_2452_,
        v_xNamePrefix_2453_,
        v_hNamePrefix_2454_,
        v_a_2455_,
        v_a_2456_,
        v_a_2457_,
        v_a_2458_,
    );
    leanh::lean_dec(v_a_2458_);
    leanh::lean_dec_ref(v_a_2457_);
    leanh::lean_dec(v_a_2456_);
    leanh::lean_dec_ref(v_a_2455_);
    return v_res_2460_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3(
    mut v_sizes_2461_: *mut leanh::LeanObject,
    mut v_fst_2462_: *mut leanh::LeanObject,
    mut v_a_2463_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2464_: *mut leanh::LeanObject,
    mut v_as_2465_: *mut leanh::LeanObject,
    mut v_i_2466_: *mut leanh::LeanObject,
    mut v_j_2467_: *mut leanh::LeanObject,
    mut v_inv_2468_: *mut leanh::LeanObject,
    mut v_bs_2469_: *mut leanh::LeanObject,
    mut v___y_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(
        v_sizes_2461_,
        v_fst_2462_,
        v_a_2463_,
        v_xNamePrefix_2464_,
        v_as_2465_,
        v_i_2466_,
        v_j_2467_,
        v_bs_2469_,
        v___y_2470_,
        v___y_2471_,
        v___y_2472_,
        v___y_2473_,
    );
    return v___x_2475_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(
    mut v_sizes_2476_: *mut leanh::LeanObject,
    mut v_fst_2477_: *mut leanh::LeanObject,
    mut v_a_2478_: *mut leanh::LeanObject,
    mut v_xNamePrefix_2479_: *mut leanh::LeanObject,
    mut v_as_2480_: *mut leanh::LeanObject,
    mut v_i_2481_: *mut leanh::LeanObject,
    mut v_j_2482_: *mut leanh::LeanObject,
    mut v_inv_2483_: *mut leanh::LeanObject,
    mut v_bs_2484_: *mut leanh::LeanObject,
    mut v___y_2485_: *mut leanh::LeanObject,
    mut v___y_2486_: *mut leanh::LeanObject,
    mut v___y_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
    mut v___y_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3(
        v_sizes_2476_,
        v_fst_2477_,
        v_a_2478_,
        v_xNamePrefix_2479_,
        v_as_2480_,
        v_i_2481_,
        v_j_2482_,
        v_inv_2483_,
        v_bs_2484_,
        v___y_2485_,
        v___y_2486_,
        v___y_2487_,
        v___y_2488_,
    );
    leanh::lean_dec(v___y_2488_);
    leanh::lean_dec_ref(v___y_2487_);
    leanh::lean_dec(v___y_2486_);
    leanh::lean_dec_ref(v___y_2485_);
    leanh::lean_dec_ref(v_as_2480_);
    leanh::lean_dec_ref(v_sizes_2476_);
    return v_res_2490_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_CaseArraySizes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_CaseArraySizes(
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
pub unsafe fn initialize_Lean_Meta_Match_CaseArraySizes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_CaseValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_CaseArraySizes(builtin);
}