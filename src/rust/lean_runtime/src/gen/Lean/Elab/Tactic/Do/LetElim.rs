// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: Lean.Meta.Tactic.Simp Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_ofFn___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_maxRecDepthErrorMessage, l_Lean_mkAtom,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::{lean_expr_instantiate_rev, lean_expr_instantiate1};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instBEqUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instBEqUses: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instOrdUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instOrdUses: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedUses_default: u8 = 0;
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedUses: u8 = 0;
pub static l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_Uses_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instAddUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instAddUses: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_FVarUses_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_instAddFVarUses: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value: LeanStringObject<
    22,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value)
                as *mut LeanObject,
            3731765604234633101 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_addMData___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_addMData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_addMData___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value: LeanStringObject<5> =
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
        m_data: [117, 115, 101, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value)
                as *mut LeanObject,
            10599070204101149623 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_countUses___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_countUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_countUses___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUses___closed__2_value: LeanStringObject<5> =
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
        m_data: [32, 62, 61, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_countUses___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_countUses___closed__4_value: LeanStringObject<7> =
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
        m_data: [102, 97, 105, 108, 101, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_countUses___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_countUses___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_countUses___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_countUses___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorIdx(mut v_x_4306_: u8) -> *mut LeanObject {
    match v_x_4306_ {
        0 => {
            let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
            v___x_4307_ = lean_unsigned_to_nat(0);
            return v___x_4307_;
        }
        1 => {
            let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
            v___x_4308_ = lean_unsigned_to_nat(1);
            return v___x_4308_;
        }
        _ => {
            let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
            v___x_4309_ = lean_unsigned_to_nat(2);
            return v___x_4309_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(
    mut v_x_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4311_ = (lean_unbox(v_x_4310_) as u8);
    v_res_4312_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_boxed_4311_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(mut v_x_4313_: u8) -> *mut LeanObject {
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    v___x_4314_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4313_);
    return v___x_4314_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(
    mut v_x_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_4316_: u8 = 0;
    let mut v_res_4317_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4316_ = (lean_unbox(v_x_4315_) as u8);
    v_res_4317_ = l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(v_x_4__boxed_4316_);
    return v_res_4317_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(
    mut v_k_4318_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4318_);
    return v_k_4318_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(
    mut v_k_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4320_: *mut LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_4319_);
    lean_dec(v_k_4319_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim(
    mut v_motive_4321_: *mut LeanObject,
    mut v_ctorIdx_4322_: *mut LeanObject,
    mut v_t_4323_: u8,
    mut v_h_4324_: *mut LeanObject,
    mut v_k_4325_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4325_);
    return v_k_4325_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(
    mut v_motive_4326_: *mut LeanObject,
    mut v_ctorIdx_4327_: *mut LeanObject,
    mut v_t_4328_: *mut LeanObject,
    mut v_h_4329_: *mut LeanObject,
    mut v_k_4330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4331_: u8 = 0;
    let mut v_res_4332_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4331_ = (lean_unbox(v_t_4328_) as u8);
    v_res_4332_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(
        v_motive_4326_,
        v_ctorIdx_4327_,
        v_t_boxed_4331_,
        v_h_4329_,
        v_k_4330_,
    );
    lean_dec(v_k_4330_);
    lean_dec(v_ctorIdx_4327_);
    return v_res_4332_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(
    mut v_zero_4333_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_zero_4333_);
    return v_zero_4333_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(
    mut v_zero_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4335_: *mut LeanObject = core::ptr::null_mut();
    v_res_4335_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_4334_);
    lean_dec(v_zero_4334_);
    return v_res_4335_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim(
    mut v_motive_4336_: *mut LeanObject,
    mut v_t_4337_: u8,
    mut v_h_4338_: *mut LeanObject,
    mut v_zero_4339_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_zero_4339_);
    return v_zero_4339_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(
    mut v_motive_4340_: *mut LeanObject,
    mut v_t_4341_: *mut LeanObject,
    mut v_h_4342_: *mut LeanObject,
    mut v_zero_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4344_: u8 = 0;
    let mut v_res_4345_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4344_ = (lean_unbox(v_t_4341_) as u8);
    v_res_4345_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(
        v_motive_4340_,
        v_t_boxed_4344_,
        v_h_4342_,
        v_zero_4343_,
    );
    lean_dec(v_zero_4343_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(
    mut v_one_4346_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_one_4346_);
    return v_one_4346_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(
    mut v_one_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4348_: *mut LeanObject = core::ptr::null_mut();
    v_res_4348_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_4347_);
    lean_dec(v_one_4347_);
    return v_res_4348_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim(
    mut v_motive_4349_: *mut LeanObject,
    mut v_t_4350_: u8,
    mut v_h_4351_: *mut LeanObject,
    mut v_one_4352_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_one_4352_);
    return v_one_4352_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(
    mut v_motive_4353_: *mut LeanObject,
    mut v_t_4354_: *mut LeanObject,
    mut v_h_4355_: *mut LeanObject,
    mut v_one_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4357_: u8 = 0;
    let mut v_res_4358_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4357_ = (lean_unbox(v_t_4354_) as u8);
    v_res_4358_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(
        v_motive_4353_,
        v_t_boxed_4357_,
        v_h_4355_,
        v_one_4356_,
    );
    lean_dec(v_one_4356_);
    return v_res_4358_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(
    mut v_many_4359_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_many_4359_);
    return v_many_4359_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(
    mut v_many_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4361_: *mut LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_4360_);
    lean_dec(v_many_4360_);
    return v_res_4361_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim(
    mut v_motive_4362_: *mut LeanObject,
    mut v_t_4363_: u8,
    mut v_h_4364_: *mut LeanObject,
    mut v_many_4365_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_many_4365_);
    return v_many_4365_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(
    mut v_motive_4366_: *mut LeanObject,
    mut v_t_4367_: *mut LeanObject,
    mut v_h_4368_: *mut LeanObject,
    mut v_many_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4370_: u8 = 0;
    let mut v_res_4371_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4370_ = (lean_unbox(v_t_4367_) as u8);
    v_res_4371_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(
        v_motive_4366_,
        v_t_boxed_4370_,
        v_h_4368_,
        v_many_4369_,
    );
    lean_dec(v_many_4369_);
    return v_res_4371_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instBEqUses_beq(mut v_x_4372_: u8, mut v_y_4373_: u8) -> u8 {
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    v___x_4374_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4372_);
    v___x_4375_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_4373_);
    v___x_4376_ = lean_nat_dec_eq(v___x_4374_, v___x_4375_);
    lean_dec(v___x_4375_);
    lean_dec(v___x_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(
    mut v_x_4377_: *mut LeanObject,
    mut v_y_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_4379_: u8 = 0;
    let mut v_y_18__boxed_4380_: u8 = 0;
    let mut v_res_4381_: u8 = 0;
    let mut v_r_4382_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_4379_ = (lean_unbox(v_x_4377_) as u8);
    v_y_18__boxed_4380_ = (lean_unbox(v_y_4378_) as u8);
    v_res_4381_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_4379_, v_y_18__boxed_4380_);
    v_r_4382_ = lean_box((v_res_4381_) as usize);
    return v_r_4382_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instOrdUses_ord(mut v_x_4385_: u8, mut v_y_4386_: u8) -> u8 {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    v___x_4387_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_4385_);
    v___x_4388_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_4386_);
    v___x_4389_ = lean_nat_dec_lt(v___x_4387_, v___x_4388_);
    if v___x_4389_ == 0 {
        let mut v___x_4390_: u8 = 0;
        v___x_4390_ = lean_nat_dec_eq(v___x_4387_, v___x_4388_);
        lean_dec(v___x_4388_);
        lean_dec(v___x_4387_);
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
        lean_dec(v___x_4388_);
        lean_dec(v___x_4387_);
        v___x_4393_ = 0;
        return v___x_4393_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(
    mut v_x_4394_: *mut LeanObject,
    mut v_y_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_4396_: u8 = 0;
    let mut v_y_31__boxed_4397_: u8 = 0;
    let mut v_res_4398_: u8 = 0;
    let mut v_r_4399_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4396_ = (lean_unbox(v_x_4394_) as u8);
    v_y_31__boxed_4397_ = (lean_unbox(v_y_4395_) as u8);
    v_res_4398_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_4396_, v_y_31__boxed_4397_);
    v_r_4399_ = lean_box((v_res_4398_) as usize);
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
    mut v_x_4407_: *mut LeanObject,
    mut v_x_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_4409_: u8 = 0;
    let mut v_x_31__boxed_4410_: u8 = 0;
    let mut v_res_4411_: u8 = 0;
    let mut v_r_4412_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4409_ = (lean_unbox(v_x_4407_) as u8);
    v_x_31__boxed_4410_ = (lean_unbox(v_x_4408_) as u8);
    v_res_4411_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_4409_, v_x_31__boxed_4410_);
    v_r_4412_ = lean_box((v_res_4411_) as usize);
    return v_r_4412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toNat(mut v_x_4413_: u8) -> *mut LeanObject {
    match v_x_4413_ {
        0 => {
            let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
            v___x_4414_ = lean_unsigned_to_nat(0);
            return v___x_4414_;
        }
        1 => {
            let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
            v___x_4415_ = lean_unsigned_to_nat(1);
            return v___x_4415_;
        }
        _ => {
            let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
            v___x_4416_ = lean_unsigned_to_nat(2);
            return v___x_4416_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(
    mut v_x_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_34__boxed_4418_: u8 = 0;
    let mut v_res_4419_: *mut LeanObject = core::ptr::null_mut();
    v_x_34__boxed_4418_ = (lean_unbox(v_x_4417_) as u8);
    v_res_4419_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_4418_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Uses_fromNat(mut v_x_4420_: *mut LeanObject) -> u8 {
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    v___x_4421_ = lean_unsigned_to_nat(0);
    v___x_4422_ = lean_nat_dec_eq(v_x_4420_, v___x_4421_);
    if v___x_4422_ == 0 {
        let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4424_: u8 = 0;
        v___x_4423_ = lean_unsigned_to_nat(1);
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
    mut v_x_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4429_: u8 = 0;
    let mut v_r_4430_: *mut LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_4428_);
    lean_dec(v_x_4428_);
    v_r_4430_ = lean_box((v_res_4429_) as usize);
    return v_r_4430_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_4433_: *mut LeanObject,
    mut v_x_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4440_: u8 = 0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4434_) == 0 {
                    return v_x_4433_;
                } else {
                    v_key_4435_ = lean_ctor_get(v_x_4434_, 0);
                    v_value_4436_ = lean_ctor_get(v_x_4434_, 1);
                    v_tail_4437_ = lean_ctor_get(v_x_4434_, 2);
                    v_isSharedCheck_4460_ = (!lean_is_exclusive(v_x_4434_)) as u8;
                    if v_isSharedCheck_4460_ == 0 {
                        v___x_4439_ = v_x_4434_;
                        v_isShared_4440_ = v_isSharedCheck_4460_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4437_);
                        lean_inc(v_value_4436_);
                        lean_inc(v_key_4435_);
                        lean_dec(v_x_4434_);
                        v___x_4439_ = lean_box(0);
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
                lean_inc(v___x_4454_);
                if v_isShared_4440_ == 0 {
                    lean_ctor_set(v___x_4439_, 2, v___x_4454_);
                    v___x_4456_ = v___x_4439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_key_4435_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_value_4436_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 2, v___x_4454_);
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
    mut v_i_4461_: *mut LeanObject,
    mut v_source_4462_: *mut LeanObject,
    mut v_target_4463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_es_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4464_ = lean_array_get_size(v_source_4462_);
                v___x_4465_ = lean_nat_dec_lt(v_i_4461_, v___x_4464_);
                if v___x_4465_ == 0 {
                    lean_dec_ref(v_source_4462_);
                    lean_dec(v_i_4461_);
                    return v_target_4463_;
                } else {
                    v_es_4466_ = lean_array_fget(v_source_4462_, v_i_4461_);
                    v___x_4467_ = lean_box(0);
                    v_source_4468_ = lean_array_fset(v_source_4462_, v_i_4461_, v___x_4467_);
                    v_target_4469_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_4463_, v_es_4466_);
                    v___x_4470_ = lean_unsigned_to_nat(1);
                    v___x_4471_ = lean_nat_add(v_i_4461_, v___x_4470_);
                    lean_dec(v_i_4461_);
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
    mut v_data_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = lean_array_get_size(v_data_4473_);
    v___x_4475_ = lean_unsigned_to_nat(2);
    v_nbuckets_4476_ = lean_nat_mul(v___x_4474_, v___x_4475_);
    v___x_4477_ = lean_unsigned_to_nat(0);
    v___x_4478_ = lean_box(0);
    v___x_4479_ = lean_mk_array(v_nbuckets_4476_, v___x_4478_);
    v___x_4480_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_4477_, v_data_4473_, v___x_4479_);
    return v___x_4480_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(
    mut v_a_4481_: *mut LeanObject,
    mut v_x_4482_: *mut LeanObject,
) -> u8 {
    let mut v___x_4483_: u8 = 0;
    let mut v_key_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4482_) == 0 {
                    v___x_4483_ = 0;
                    return v___x_4483_;
                } else {
                    v_key_4484_ = lean_ctor_get(v_x_4482_, 0);
                    v_tail_4485_ = lean_ctor_get(v_x_4482_, 2);
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
    mut v_a_4488_: *mut LeanObject,
    mut v_x_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4488_, v_x_4489_);
    lean_dec(v_x_4489_);
    lean_dec(v_a_4488_);
    v_r_4491_ = lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(
    mut v_x3_4492_: u8,
    mut v_x_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4500_: u8 = 0;
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4493_) == 0 {
                    v___x_4494_ = lean_box((v_x3_4492_) as usize);
                    v___x_4495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4495_, 0, v___x_4494_);
                    return v___x_4495_;
                } else {
                    v_val_4496_ = lean_ctor_get(v_x_4493_, 0);
                    v_isSharedCheck_4506_ = (!lean_is_exclusive(v_x_4493_)) as u8;
                    if v_isSharedCheck_4506_ == 0 {
                        v___x_4498_ = v_x_4493_;
                        v_isShared_4499_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4496_);
                        lean_dec(v_x_4493_);
                        v___x_4498_ = lean_box(0);
                        v_isShared_4499_ = v_isSharedCheck_4506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4500_ = (lean_unbox(v_val_4496_) as u8);
                lean_dec(v_val_4496_);
                v___x_4501_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_4492_, v___x_4500_);
                v___x_4502_ = lean_box((v___x_4501_) as usize);
                if v_isShared_4499_ == 0 {
                    lean_ctor_set(v___x_4498_, 0, v___x_4502_);
                    v___x_4504_ = v___x_4498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
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
    mut v_x3_4507_: *mut LeanObject,
    mut v_x_4508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x3_854__boxed_4509_: u8 = 0;
    let mut v_res_4510_: *mut LeanObject = core::ptr::null_mut();
    v_x3_854__boxed_4509_ = (lean_unbox(v_x3_4507_) as u8);
    v_res_4510_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_854__boxed_4509_, v_x_4508_);
    return v_res_4510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(
    mut v_x3_4511_: u8,
    mut v_a_4512_: *mut LeanObject,
    mut v_x_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v_tail_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4513_) == 0 {
                    v___x_4514_ = lean_box(0);
                    v___x_4515_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_4511_, v___x_4514_);
                    v_val_4516_ = lean_ctor_get(v___x_4515_, 0);
                    lean_inc(v_val_4516_);
                    lean_dec(v___x_4515_);
                    v___x_4517_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4517_, 0, v_a_4512_);
                    lean_ctor_set(v___x_4517_, 1, v_val_4516_);
                    lean_ctor_set(v___x_4517_, 2, v_x_4513_);
                    return v___x_4517_;
                } else {
                    v_key_4518_ = lean_ctor_get(v_x_4513_, 0);
                    v_value_4519_ = lean_ctor_get(v_x_4513_, 1);
                    v_tail_4520_ = lean_ctor_get(v_x_4513_, 2);
                    v_isSharedCheck_4535_ = (!lean_is_exclusive(v_x_4513_)) as u8;
                    if v_isSharedCheck_4535_ == 0 {
                        v___x_4522_ = v_x_4513_;
                        v_isShared_4523_ = v_isSharedCheck_4535_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4520_);
                        lean_inc(v_value_4519_);
                        lean_inc(v_key_4518_);
                        lean_dec(v_x_4513_);
                        v___x_4522_ = lean_box(0);
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
                        lean_ctor_set(v___x_4522_, 2, v_tail_4525_);
                        v___x_4527_ = v___x_4522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_key_4518_);
                        lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_value_4519_);
                        lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_tail_4525_);
                        v___x_4527_ = v_reuseFailAlloc_4528_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_4518_);
                    v___x_4529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4529_, 0, v_value_4519_);
                    v___x_4530_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_4511_, v___x_4529_);
                    v_val_4531_ = lean_ctor_get(v___x_4530_, 0);
                    lean_inc(v_val_4531_);
                    lean_dec(v___x_4530_);
                    if v_isShared_4523_ == 0 {
                        lean_ctor_set(v___x_4522_, 1, v_val_4531_);
                        lean_ctor_set(v___x_4522_, 0, v_a_4512_);
                        v___x_4533_ = v___x_4522_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4512_);
                        lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_val_4531_);
                        lean_ctor_set(v_reuseFailAlloc_4534_, 2, v_tail_4520_);
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
    mut v_x3_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_x_4538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x3_886__boxed_4539_: u8 = 0;
    let mut v_res_4540_: *mut LeanObject = core::ptr::null_mut();
    v_x3_886__boxed_4539_ = (lean_unbox(v_x3_4536_) as u8);
    v_res_4540_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_886__boxed_4539_, v_a_4537_, v_x_4538_);
    return v_res_4540_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(
    mut v_x3_4541_: u8,
    mut v_m_4542_: *mut LeanObject,
    mut v_a_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v_val_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4544_ = lean_ctor_get(v_m_4542_, 0);
                v_buckets_4545_ = lean_ctor_get(v_m_4542_, 1);
                v_isSharedCheck_4594_ = (!lean_is_exclusive(v_m_4542_)) as u8;
                if v_isSharedCheck_4594_ == 0 {
                    v___x_4547_ = v_m_4542_;
                    v_isShared_4548_ = v_isSharedCheck_4594_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_4545_);
                    lean_inc(v_size_4544_);
                    lean_dec(v_m_4542_);
                    v___x_4547_ = lean_box(0);
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
                    v___x_4564_ = lean_unsigned_to_nat(1);
                    v_size_x27_4565_ = lean_nat_add(v_size_4544_, v___x_4564_);
                    lean_dec(v_size_4544_);
                    v___x_4566_ = lean_box((v_x3_4541_) as usize);
                    lean_inc(v_bkt_4562_);
                    v___x_4567_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4567_, 0, v_a_4543_);
                    lean_ctor_set(v___x_4567_, 1, v___x_4566_);
                    lean_ctor_set(v___x_4567_, 2, v_bkt_4562_);
                    v_buckets_x27_4568_ =
                        lean_array_uset(v_buckets_4545_, v___x_4561_, v___x_4567_);
                    v___x_4569_ = lean_unsigned_to_nat(4);
                    v___x_4570_ = lean_nat_mul(v_size_x27_4565_, v___x_4569_);
                    v___x_4571_ = lean_unsigned_to_nat(3);
                    v___x_4572_ = lean_nat_div(v___x_4570_, v___x_4571_);
                    lean_dec(v___x_4570_);
                    v___x_4573_ = lean_array_get_size(v_buckets_x27_4568_);
                    v___x_4574_ = lean_nat_dec_le(v___x_4572_, v___x_4573_);
                    lean_dec(v___x_4572_);
                    if v___x_4574_ == 0 {
                        v_val_4575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_4568_);
                        if v_isShared_4548_ == 0 {
                            lean_ctor_set(v___x_4547_, 1, v_val_4575_);
                            lean_ctor_set(v___x_4547_, 0, v_size_x27_4565_);
                            v___x_4577_ = v___x_4547_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_size_x27_4565_);
                            lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_val_4575_);
                            v___x_4577_ = v_reuseFailAlloc_4578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4548_ == 0 {
                            lean_ctor_set(v___x_4547_, 1, v_buckets_x27_4568_);
                            lean_ctor_set(v___x_4547_, 0, v_size_x27_4565_);
                            v___x_4580_ = v___x_4547_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_size_x27_4565_);
                            lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_buckets_x27_4568_);
                            v___x_4580_ = v_reuseFailAlloc_4581_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_4562_);
                    v___x_4582_ = lean_box(0);
                    v_buckets_x27_4583_ =
                        lean_array_uset(v_buckets_4545_, v___x_4561_, v___x_4582_);
                    lean_inc(v_a_4543_);
                    v_bkt_x27_4584_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_4541_, v_a_4543_, v_bkt_4562_);
                    v___x_4591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4543_, v_bkt_x27_4584_);
                    lean_dec(v_a_4543_);
                    if v___x_4591_ == 0 {
                        v___x_4592_ = lean_unsigned_to_nat(1);
                        v___x_4593_ = lean_nat_sub(v_size_4544_, v___x_4592_);
                        lean_dec(v_size_4544_);
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
                    lean_ctor_set(v___x_4547_, 1, v___x_4587_);
                    lean_ctor_set(v___x_4547_, 0, v___y_4586_);
                    v___x_4589_ = v___x_4547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___y_4586_);
                    lean_ctor_set(v_reuseFailAlloc_4590_, 1, v___x_4587_);
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
    mut v_x3_4595_: *mut LeanObject,
    mut v_m_4596_: *mut LeanObject,
    mut v_a_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x3_934__boxed_4598_: u8 = 0;
    let mut v_res_4599_: *mut LeanObject = core::ptr::null_mut();
    v_x3_934__boxed_4598_ = (lean_unbox(v_x3_4595_) as u8);
    v_res_4599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_934__boxed_4598_, v_m_4596_, v_a_4597_);
    return v_res_4599_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(
    mut v_x_4600_: *mut LeanObject,
    mut v_x_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4601_) == 0 {
                    return v_x_4600_;
                } else {
                    v_key_4602_ = lean_ctor_get(v_x_4601_, 0);
                    lean_inc(v_key_4602_);
                    v_value_4603_ = lean_ctor_get(v_x_4601_, 1);
                    lean_inc(v_value_4603_);
                    v_tail_4604_ = lean_ctor_get(v_x_4601_, 2);
                    lean_inc(v_tail_4604_);
                    lean_dec_ref_known(v_x_4601_, 3);
                    v___x_4605_ = (lean_unbox(v_value_4603_) as u8);
                    lean_dec(v_value_4603_);
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
    mut v_as_4608_: *mut LeanObject,
    mut v_i_4609_: usize,
    mut v_stop_4610_: usize,
    mut v_b_4611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: usize = 0;
    let mut v___x_4616_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4612_ = lean_usize_dec_eq(v_i_4609_, v_stop_4610_);
                if v___x_4612_ == 0 {
                    v___x_4613_ = lean_array_uget_borrowed(v_as_4608_, v_i_4609_);
                    lean_inc(v___x_4613_);
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
    mut v_as_4618_: *mut LeanObject,
    mut v_i_4619_: *mut LeanObject,
    mut v_stop_4620_: *mut LeanObject,
    mut v_b_4621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4622_: usize = 0;
    let mut v_stop_boxed_4623_: usize = 0;
    let mut v_res_4624_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4622_ = lean_unbox_usize(v_i_4619_);
    lean_dec(v_i_4619_);
    v_stop_boxed_4623_ = lean_unbox_usize(v_stop_4620_);
    lean_dec(v_stop_4620_);
    v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_4618_, v_i_boxed_4622_, v_stop_boxed_4623_, v_b_4621_);
    lean_dec_ref(v_as_4618_);
    return v_res_4624_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_FVarUses_add(
    mut v_a_4625_: *mut LeanObject,
    mut v_b_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u8 = 0;
    v_buckets_4627_ = lean_ctor_get(v_a_4625_, 1);
    v___x_4628_ = lean_unsigned_to_nat(0);
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
                let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
                v___x_4632_ = 0usize;
                v___x_4633_ = lean_usize_of_nat(v___x_4629_);
                v___x_4634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_4627_, v___x_4632_, v___x_4633_, v_b_4626_);
                return v___x_4634_;
            }
        } else {
            let mut v___x_4635_: usize = 0;
            let mut v___x_4636_: usize = 0;
            let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
            v___x_4635_ = 0usize;
            v___x_4636_ = lean_usize_of_nat(v___x_4629_);
            v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_4627_, v___x_4635_, v___x_4636_, v_b_4626_);
            return v___x_4637_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(
    mut v_a_4638_: *mut LeanObject,
    mut v_b_4639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4640_: *mut LeanObject = core::ptr::null_mut();
    v_res_4640_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_4638_, v_b_4639_);
    lean_dec_ref(v_a_4638_);
    return v_res_4640_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(
    mut v_00_u03b2_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_x_4643_: *mut LeanObject,
) -> u8 {
    let mut v___x_4644_: u8 = 0;
    v___x_4644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_4642_, v_x_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(
    mut v_00_u03b2_4645_: *mut LeanObject,
    mut v_a_4646_: *mut LeanObject,
    mut v_x_4647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4648_: u8 = 0;
    let mut v_r_4649_: *mut LeanObject = core::ptr::null_mut();
    v_res_4648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_4645_, v_a_4646_, v_x_4647_);
    lean_dec(v_x_4647_);
    lean_dec(v_a_4646_);
    v_r_4649_ = lean_box((v_res_4648_) as usize);
    return v_r_4649_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(
    mut v_00_u03b2_4650_: *mut LeanObject,
    mut v_data_4651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    v___x_4652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_4651_);
    return v___x_4652_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4653_: *mut LeanObject,
    mut v_i_4654_: *mut LeanObject,
    mut v_source_4655_: *mut LeanObject,
    mut v_target_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    v___x_4657_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_4654_, v_source_4655_, v_target_4656_);
    return v___x_4657_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_4658_: *mut LeanObject,
    mut v_x_4659_: *mut LeanObject,
    mut v_x_4660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_4659_, v_x_4660_);
    return v___x_4661_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(
    mut v_x_4664_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4664_) == 0 {
        let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
        v___x_4665_ = lean_unsigned_to_nat(0);
        return v___x_4665_;
    } else {
        let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
        v___x_4666_ = lean_unsigned_to_nat(1);
        return v___x_4666_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(
    mut v_x_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_4667_);
    lean_dec(v_x_4667_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(
    mut v_n_4669_: *mut LeanObject,
    mut v_x_4670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    v___x_4671_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_4670_);
    return v___x_4671_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(
    mut v_n_4672_: *mut LeanObject,
    mut v_x_4673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4674_: *mut LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_4672_, v_x_4673_);
    lean_dec(v_x_4673_);
    lean_dec(v_n_4672_);
    return v_res_4674_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(
    mut v_t_4675_: *mut LeanObject,
    mut v_k_4676_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4675_) == 0 {
        return v_k_4676_;
    } else {
        let mut v_uses_4677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
        v_uses_4677_ = lean_ctor_get(v_t_4675_, 0);
        lean_inc_ref(v_uses_4677_);
        lean_dec_ref_known(v_t_4675_, 1);
        v___x_4678_ = lean_apply_1(v_k_4676_, v_uses_4677_);
        return v___x_4678_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(
    mut v_n_4679_: *mut LeanObject,
    mut v_motive_4680_: *mut LeanObject,
    mut v_ctorIdx_4681_: *mut LeanObject,
    mut v_t_4682_: *mut LeanObject,
    mut v_h_4683_: *mut LeanObject,
    mut v_k_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    v___x_4685_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4682_, v_k_4684_);
    return v___x_4685_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(
    mut v_n_4686_: *mut LeanObject,
    mut v_motive_4687_: *mut LeanObject,
    mut v_ctorIdx_4688_: *mut LeanObject,
    mut v_t_4689_: *mut LeanObject,
    mut v_h_4690_: *mut LeanObject,
    mut v_k_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4692_: *mut LeanObject = core::ptr::null_mut();
    v_res_4692_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(
        v_n_4686_,
        v_motive_4687_,
        v_ctorIdx_4688_,
        v_t_4689_,
        v_h_4690_,
        v_k_4691_,
    );
    lean_dec(v_ctorIdx_4688_);
    lean_dec(v_n_4686_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(
    mut v_t_4693_: *mut LeanObject,
    mut v_none_4694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    v___x_4695_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4693_, v_none_4694_);
    return v___x_4695_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim(
    mut v_n_4696_: *mut LeanObject,
    mut v_motive_4697_: *mut LeanObject,
    mut v_t_4698_: *mut LeanObject,
    mut v_h_4699_: *mut LeanObject,
    mut v_none_4700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4698_, v_none_4700_);
    return v___x_4701_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(
    mut v_n_4702_: *mut LeanObject,
    mut v_motive_4703_: *mut LeanObject,
    mut v_t_4704_: *mut LeanObject,
    mut v_h_4705_: *mut LeanObject,
    mut v_none_4706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4707_: *mut LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(
        v_n_4702_,
        v_motive_4703_,
        v_t_4704_,
        v_h_4705_,
        v_none_4706_,
    );
    lean_dec(v_n_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(
    mut v_t_4708_: *mut LeanObject,
    mut v_some_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4708_, v_some_4709_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim(
    mut v_n_4711_: *mut LeanObject,
    mut v_motive_4712_: *mut LeanObject,
    mut v_t_4713_: *mut LeanObject,
    mut v_h_4714_: *mut LeanObject,
    mut v_some_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    v___x_4716_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_4713_, v_some_4715_);
    return v___x_4716_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(
    mut v_n_4717_: *mut LeanObject,
    mut v_motive_4718_: *mut LeanObject,
    mut v_t_4719_: *mut LeanObject,
    mut v_h_4720_: *mut LeanObject,
    mut v_some_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(
        v_n_4717_,
        v_motive_4718_,
        v_t_4719_,
        v_h_4720_,
        v_some_4721_,
    );
    lean_dec(v_n_4717_);
    return v_res_4722_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13() -> *mut LeanObject
{
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12;
    v___x_4748_ = l_Lean_mkAtom(v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14() -> *mut LeanObject
{
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    v___x_4749_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13,
    );
    v___x_4750_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4751_ = lean_array_push(v___x_4750_, v___x_4749_);
    return v___x_4751_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15() -> *mut LeanObject
{
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    v___x_4752_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14,
    );
    v___x_4753_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11;
    v___x_4754_ = lean_box(2);
    v___x_4755_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4755_, 0, v___x_4754_);
    lean_ctor_set(v___x_4755_, 1, v___x_4753_);
    lean_ctor_set(v___x_4755_, 2, v___x_4752_);
    return v___x_4755_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16() -> *mut LeanObject
{
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    v___x_4756_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15,
    );
    v___x_4757_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4758_ = lean_array_push(v___x_4757_, v___x_4756_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17() -> *mut LeanObject
{
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    v___x_4759_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16,
    );
    v___x_4760_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9;
    v___x_4761_ = lean_box(2);
    v___x_4762_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4762_, 0, v___x_4761_);
    lean_ctor_set(v___x_4762_, 1, v___x_4760_);
    lean_ctor_set(v___x_4762_, 2, v___x_4759_);
    return v___x_4762_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18() -> *mut LeanObject
{
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v___x_4763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17,
    );
    v___x_4764_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4765_ = lean_array_push(v___x_4764_, v___x_4763_);
    return v___x_4765_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19() -> *mut LeanObject
{
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    v___x_4766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18,
    );
    v___x_4767_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7;
    v___x_4768_ = lean_box(2);
    v___x_4769_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4769_, 0, v___x_4768_);
    lean_ctor_set(v___x_4769_, 1, v___x_4767_);
    lean_ctor_set(v___x_4769_, 2, v___x_4766_);
    return v___x_4769_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20() -> *mut LeanObject
{
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    v___x_4770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19,
    );
    v___x_4771_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5;
    v___x_4772_ = lean_array_push(v___x_4771_, v___x_4770_);
    return v___x_4772_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21() -> *mut LeanObject
{
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    v___x_4773_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20,
    );
    v___x_4774_ = l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4;
    v___x_4775_ = lean_box(2);
    v___x_4776_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4776_, 0, v___x_4775_);
    lean_ctor_set(v___x_4776_, 1, v___x_4774_);
    lean_ctor_set(v___x_4776_, 2, v___x_4773_);
    return v___x_4776_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1() -> *mut LeanObject {
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    v___x_4777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once),
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21,
    );
    return v___x_4777_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(
    mut v_numBVars_4778_: *mut LeanObject,
    mut v_n_4779_: *mut LeanObject,
    mut v_i_4780_: *mut LeanObject,
) -> u8 {
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: u8 = 0;
    v___x_4781_ = lean_unsigned_to_nat(1);
    v___x_4782_ = lean_nat_sub(v_numBVars_4778_, v___x_4781_);
    v___x_4783_ = lean_nat_sub(v___x_4782_, v_n_4779_);
    lean_dec(v___x_4782_);
    v___x_4784_ = lean_nat_dec_eq(v_i_4780_, v___x_4783_);
    lean_dec(v___x_4783_);
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
    mut v_numBVars_4787_: *mut LeanObject,
    mut v_n_4788_: *mut LeanObject,
    mut v_i_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4790_: u8 = 0;
    let mut v_r_4791_: *mut LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(
        v_numBVars_4787_,
        v_n_4788_,
        v_i_4789_,
    );
    lean_dec(v_i_4789_);
    lean_dec(v_n_4788_);
    lean_dec(v_numBVars_4787_);
    v_r_4791_ = lean_box((v_res_4790_) as usize);
    return v_r_4791_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(
    mut v_numBVars_4792_: *mut LeanObject,
    mut v_n_4793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_numBVars_4792_);
    v___f_4794_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4794_, 0, v_numBVars_4792_);
    lean_closure_set(v___f_4794_, 1, v_n_4793_);
    v___x_4795_ = l_Array_ofFn___redArg(v_numBVars_4792_, v___f_4794_);
    v___x_4796_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4796_, 0, v___x_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_single(
    mut v_numBVars_4797_: *mut LeanObject,
    mut v_n_4798_: *mut LeanObject,
    mut v_x_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_4797_, v_n_4798_);
    return v___x_4800_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_pop(
    mut v_numBVars_4805_: *mut LeanObject,
    mut v_x_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uses_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4806_) == 0 {
                    v___x_4807_ = l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0;
                    return v___x_4807_;
                } else {
                    v_uses_4808_ = lean_ctor_get(v_x_4806_, 0);
                    v_isSharedCheck_4821_ = (!lean_is_exclusive(v_x_4806_)) as u8;
                    if v_isSharedCheck_4821_ == 0 {
                        v___x_4810_ = v_x_4806_;
                        v_isShared_4811_ = v_isSharedCheck_4821_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_uses_4808_);
                        lean_dec(v_x_4806_);
                        v___x_4810_ = lean_box(0);
                        v_isShared_4811_ = v_isSharedCheck_4821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4812_ = lean_unsigned_to_nat(1);
                v___x_4813_ = lean_nat_add(v_numBVars_4805_, v___x_4812_);
                v___x_4814_ = lean_nat_sub(v___x_4813_, v___x_4812_);
                lean_dec(v___x_4813_);
                v___x_4815_ = lean_array_fget(v_uses_4808_, v___x_4814_);
                lean_dec(v___x_4814_);
                v___x_4816_ = lean_array_pop(v_uses_4808_);
                if v_isShared_4811_ == 0 {
                    lean_ctor_set(v___x_4810_, 0, v___x_4816_);
                    v___x_4818_ = v___x_4810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4816_);
                    v___x_4818_ = v_reuseFailAlloc_4820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4819_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4819_, 0, v___x_4815_);
                lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                return v___x_4819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(
    mut v_numBVars_4822_: *mut LeanObject,
    mut v_x_4823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4824_: *mut LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_4822_, v_x_4823_);
    lean_dec(v_numBVars_4822_);
    return v_res_4824_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
    mut v_as_4825_: *mut LeanObject,
    mut v_bs_4826_: *mut LeanObject,
    mut v_i_4827_: *mut LeanObject,
    mut v_cs_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: u8 = 0;
    let mut v_a_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: u8 = 0;
    let mut v___x_4836_: u8 = 0;
    let mut v___x_4837_: u8 = 0;
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = lean_array_get_size(v_as_4825_);
                v___x_4830_ = lean_nat_dec_lt(v_i_4827_, v___x_4829_);
                if v___x_4830_ == 0 {
                    lean_dec(v_i_4827_);
                    return v_cs_4828_;
                } else {
                    v___x_4831_ = lean_array_get_size(v_bs_4826_);
                    v___x_4832_ = lean_nat_dec_lt(v_i_4827_, v___x_4831_);
                    if v___x_4832_ == 0 {
                        lean_dec(v_i_4827_);
                        return v_cs_4828_;
                    } else {
                        v_a_4833_ = lean_array_fget_borrowed(v_as_4825_, v_i_4827_);
                        v_b_4834_ = lean_array_fget_borrowed(v_bs_4826_, v_i_4827_);
                        v___x_4835_ = (lean_unbox(v_a_4833_) as u8);
                        v___x_4836_ = (lean_unbox(v_b_4834_) as u8);
                        v___x_4837_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_4835_, v___x_4836_);
                        v___x_4838_ = lean_unsigned_to_nat(1);
                        v___x_4839_ = lean_nat_add(v_i_4827_, v___x_4838_);
                        lean_dec(v_i_4827_);
                        v___x_4840_ = lean_box((v___x_4837_) as usize);
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
    mut v_as_4843_: *mut LeanObject,
    mut v_bs_4844_: *mut LeanObject,
    mut v_i_4845_: *mut LeanObject,
    mut v_cs_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4847_: *mut LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
        v_as_4843_, v_bs_4844_, v_i_4845_, v_cs_4846_,
    );
    lean_dec_ref(v_bs_4844_);
    lean_dec_ref(v_as_4843_);
    return v_res_4847_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(
    mut v_a_4850_: *mut LeanObject,
    mut v_b_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uses_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_uses_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uses_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4850_) == 0 {
                    return v_b_4851_;
                } else {
                    if lean_obj_tag(v_b_4851_) == 0 {
                        v_uses_4852_ = lean_ctor_get(v_a_4850_, 0);
                        v_isSharedCheck_4859_ = (!lean_is_exclusive(v_a_4850_)) as u8;
                        if v_isSharedCheck_4859_ == 0 {
                            v___x_4854_ = v_a_4850_;
                            v_isShared_4855_ = v_isSharedCheck_4859_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_uses_4852_);
                            lean_dec(v_a_4850_);
                            v___x_4854_ = lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4859_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_uses_4860_ = lean_ctor_get(v_a_4850_, 0);
                        lean_inc_ref(v_uses_4860_);
                        lean_dec_ref_known(v_a_4850_, 1);
                        v_uses_4861_ = lean_ctor_get(v_b_4851_, 0);
                        v_isSharedCheck_4871_ = (!lean_is_exclusive(v_b_4851_)) as u8;
                        if v_isSharedCheck_4871_ == 0 {
                            v___x_4863_ = v_b_4851_;
                            v_isShared_4864_ = v_isSharedCheck_4871_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_uses_4861_);
                            lean_dec(v_b_4851_);
                            v___x_4863_ = lean_box(0);
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
                    v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_uses_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4857_;
            }
            3 => {
                v___x_4865_ = lean_unsigned_to_nat(0);
                v___x_4866_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0;
                v___x_4867_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(
                    v_uses_4860_,
                    v_uses_4861_,
                    v___x_4865_,
                    v___x_4866_,
                );
                lean_dec_ref(v_uses_4861_);
                lean_dec_ref(v_uses_4860_);
                if v_isShared_4864_ == 0 {
                    lean_ctor_set(v___x_4863_, 0, v___x_4867_);
                    v___x_4869_ = v___x_4863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4867_);
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
    mut v_numBVars_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_b_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_4873_, v_b_4874_);
    return v___x_4875_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(
    mut v_numBVars_4876_: *mut LeanObject,
    mut v_a_4877_: *mut LeanObject,
    mut v_b_4878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4879_: *mut LeanObject = core::ptr::null_mut();
    v_res_4879_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_4876_, v_a_4877_, v_b_4878_);
    lean_dec(v_numBVars_4876_);
    return v_res_4879_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_instAddBVarUses(
    mut v_numBVars_4880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v___x_4881_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_BVarUses_add___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4881_, 0, v_numBVars_4880_);
    return v___x_4881_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_over1Of2___redArg(
    mut v_f_4882_: *mut LeanObject,
    mut v_x_4883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4884_ = lean_ctor_get(v_x_4883_, 0);
                v_snd_4885_ = lean_ctor_get(v_x_4883_, 1);
                v_isSharedCheck_4893_ = (!lean_is_exclusive(v_x_4883_)) as u8;
                if v_isSharedCheck_4893_ == 0 {
                    v___x_4887_ = v_x_4883_;
                    v_isShared_4888_ = v_isSharedCheck_4893_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4885_);
                    lean_inc(v_fst_4884_);
                    lean_dec(v_x_4883_);
                    v___x_4887_ = lean_box(0);
                    v_isShared_4888_ = v_isSharedCheck_4893_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4889_ = lean_apply_1(v_f_4882_, v_fst_4884_);
                if v_isShared_4888_ == 0 {
                    lean_ctor_set(v___x_4887_, 0, v___x_4889_);
                    v___x_4891_ = v___x_4887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_snd_4885_);
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
    mut v_00_u03b1_u2081_4894_: *mut LeanObject,
    mut v_00_u03b1_u2082_4895_: *mut LeanObject,
    mut v_00_u03b2_4896_: *mut LeanObject,
    mut v_f_4897_: *mut LeanObject,
    mut v_x_4898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    v___x_4899_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_4897_, v_x_4898_);
    return v___x_4899_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData___lam__0(
    mut v_x_4900_: *mut LeanObject,
    mut v_new_4901_: *mut LeanObject,
    mut v_x_4902_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_new_4901_);
    return v_new_4901_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(
    mut v_x_4903_: *mut LeanObject,
    mut v_new_4904_: *mut LeanObject,
    mut v_x_4905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4906_: *mut LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_4903_, v_new_4904_, v_x_4905_);
    lean_dec_ref(v_x_4905_);
    lean_dec_ref(v_new_4904_);
    lean_dec(v_x_4903_);
    return v_res_4906_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_addMData(
    mut v_d_4908_: *mut LeanObject,
    mut v_e_4909_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_4909_) == 10 {
        let mut v_data_4910_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expr_4911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
        v_data_4910_ = lean_ctor_get(v_e_4909_, 0);
        lean_inc(v_data_4910_);
        v_expr_4911_ = lean_ctor_get(v_e_4909_, 1);
        lean_inc_ref(v_expr_4911_);
        lean_dec_ref_known(v_e_4909_, 2);
        v___f_4912_ = l_Lean_Elab_Tactic_Do_addMData___closed__0;
        v___x_4913_ = l_Lean_KVMap_mergeBy(v___f_4912_, v_d_4908_, v_data_4910_);
        lean_dec(v_data_4910_);
        v___x_4914_ = l_Lean_Expr_mdata___override(v___x_4913_, v_expr_4911_);
        return v___x_4914_;
    } else {
        let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
        v___x_4915_ = l_Lean_Expr_mdata___override(v_d_4908_, v_e_4909_);
        return v___x_4915_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(
    mut v_e_4916_: *mut LeanObject,
) -> u8 {
    let mut v___y_4918_: u8 = 0;
    let mut v___x_4919_: u8 = 0;
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: u8 = 0;
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: u8 = 0;
    let mut v___x_4924_: u8 = 0;
    let mut v___x_4925_: u8 = 0;
    let mut v_expr_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_4916_) {
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
                    v_expr_4926_ = lean_ctor_get(v_e_4916_, 1);
                    v_e_4916_ = v_expr_4926_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_4928_ = lean_ctor_get(v_e_4916_, 2);
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
    mut v_e_4931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4932_: u8 = 0;
    let mut v_r_4933_: *mut LeanObject = core::ptr::null_mut();
    v_res_4932_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_4931_);
    lean_dec_ref(v_e_4931_);
    v_r_4933_ = lean_box((v_res_4932_) as usize);
    return v_r_4933_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(
    mut v_val_4934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    v___x_4935_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4935_, 0, v_val_4934_);
    return v___x_4935_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(
    mut v_msgData_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
    mut v___y_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    v___x_4942_ = lean_st_ref_get(v___y_4940_);
    v_env_4943_ = lean_ctor_get(v___x_4942_, 0);
    lean_inc_ref(v_env_4943_);
    lean_dec(v___x_4942_);
    v___x_4944_ = lean_st_ref_get(v___y_4938_);
    v_mctx_4945_ = lean_ctor_get(v___x_4944_, 0);
    lean_inc_ref(v_mctx_4945_);
    lean_dec(v___x_4944_);
    v_lctx_4946_ = lean_ctor_get(v___y_4937_, 2);
    v_options_4947_ = lean_ctor_get(v___y_4939_, 2);
    lean_inc_ref(v_options_4947_);
    lean_inc_ref(v_lctx_4946_);
    v___x_4948_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4948_, 0, v_env_4943_);
    lean_ctor_set(v___x_4948_, 1, v_mctx_4945_);
    lean_ctor_set(v___x_4948_, 2, v_lctx_4946_);
    lean_ctor_set(v___x_4948_, 3, v_options_4947_);
    v___x_4949_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4949_, 0, v___x_4948_);
    lean_ctor_set(v___x_4949_, 1, v_msgData_4936_);
    v___x_4950_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4950_, 0, v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(
    mut v_msgData_4951_: *mut LeanObject,
    mut v___y_4952_: *mut LeanObject,
    mut v___y_4953_: *mut LeanObject,
    mut v___y_4954_: *mut LeanObject,
    mut v___y_4955_: *mut LeanObject,
    mut v___y_4956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4957_: *mut LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    lean_dec(v___y_4955_);
    lean_dec_ref(v___y_4954_);
    lean_dec(v___y_4953_);
    lean_dec_ref(v___y_4952_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
    mut v_msg_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4969_: u8 = 0;
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4964_ = lean_ctor_get(v___y_4961_, 5);
                v___x_4965_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
                v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
                v_isSharedCheck_4974_ = (!lean_is_exclusive(v___x_4965_)) as u8;
                if v_isSharedCheck_4974_ == 0 {
                    v___x_4968_ = v___x_4965_;
                    v_isShared_4969_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4966_);
                    lean_dec(v___x_4965_);
                    v___x_4968_ = lean_box(0);
                    v_isShared_4969_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4964_);
                v___x_4970_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4970_, 0, v_ref_4964_);
                lean_ctor_set(v___x_4970_, 1, v_a_4966_);
                if v_isShared_4969_ == 0 {
                    lean_ctor_set_tag(v___x_4968_, 1);
                    lean_ctor_set(v___x_4968_, 0, v___x_4970_);
                    v___x_4972_ = v___x_4968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4970_);
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
    mut v_msg_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4981_: *mut LeanObject = core::ptr::null_mut();
    v_res_4981_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(
        v_msg_4975_,
        v___y_4976_,
        v___y_4977_,
        v___y_4978_,
        v___y_4979_,
    );
    lean_dec(v___y_4979_);
    lean_dec_ref(v___y_4978_);
    lean_dec(v___y_4977_);
    lean_dec_ref(v___y_4976_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___lam__0(
    mut v_data_4982_: *mut LeanObject,
    mut v_expr_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    v___x_4984_ = l_Lean_Expr_mdata___override(v_data_4982_, v_expr_4983_);
    return v___x_4984_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___lam__1(
    mut v_typeName_4985_: *mut LeanObject,
    mut v_idx_4986_: *mut LeanObject,
    mut v_struct_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    v___x_4988_ = l_Lean_Expr_proj___override(v_typeName_4985_, v_idx_4986_, v_struct_4987_);
    return v___x_4988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(
    mut v_a_4989_: *mut LeanObject,
    mut v_b_4990_: *mut LeanObject,
    mut v_x_4991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4997_: u8 = 0;
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4991_) == 0 {
                    lean_dec(v_b_4990_);
                    lean_dec(v_a_4989_);
                    return v_x_4991_;
                } else {
                    v_key_4992_ = lean_ctor_get(v_x_4991_, 0);
                    v_value_4993_ = lean_ctor_get(v_x_4991_, 1);
                    v_tail_4994_ = lean_ctor_get(v_x_4991_, 2);
                    v_isSharedCheck_5006_ = (!lean_is_exclusive(v_x_4991_)) as u8;
                    if v_isSharedCheck_5006_ == 0 {
                        v___x_4996_ = v_x_4991_;
                        v_isShared_4997_ = v_isSharedCheck_5006_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4994_);
                        lean_inc(v_value_4993_);
                        lean_inc(v_key_4992_);
                        lean_dec(v_x_4991_);
                        v___x_4996_ = lean_box(0);
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
                        lean_ctor_set(v___x_4996_, 2, v___x_4999_);
                        v___x_5001_ = v___x_4996_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_key_4992_);
                        lean_ctor_set(v_reuseFailAlloc_5002_, 1, v_value_4993_);
                        lean_ctor_set(v_reuseFailAlloc_5002_, 2, v___x_4999_);
                        v___x_5001_ = v_reuseFailAlloc_5002_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_4993_);
                    lean_dec(v_key_4992_);
                    if v_isShared_4997_ == 0 {
                        lean_ctor_set(v___x_4996_, 1, v_b_4990_);
                        lean_ctor_set(v___x_4996_, 0, v_a_4989_);
                        v___x_5004_ = v___x_4996_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4989_);
                        lean_ctor_set(v_reuseFailAlloc_5005_, 1, v_b_4990_);
                        lean_ctor_set(v_reuseFailAlloc_5005_, 2, v_tail_4994_);
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
    mut v_m_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_b_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut v_val_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5010_ = lean_ctor_get(v_m_5007_, 0);
                v_buckets_5011_ = lean_ctor_get(v_m_5007_, 1);
                v_isSharedCheck_5054_ = (!lean_is_exclusive(v_m_5007_)) as u8;
                if v_isSharedCheck_5054_ == 0 {
                    v___x_5013_ = v_m_5007_;
                    v_isShared_5014_ = v_isSharedCheck_5054_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_5011_);
                    lean_inc(v_size_5010_);
                    lean_dec(v_m_5007_);
                    v___x_5013_ = lean_box(0);
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
                    v___x_5030_ = lean_unsigned_to_nat(1);
                    v_size_x27_5031_ = lean_nat_add(v_size_5010_, v___x_5030_);
                    lean_dec(v_size_5010_);
                    lean_inc(v_bkt_5028_);
                    v___x_5032_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5032_, 0, v_a_5008_);
                    lean_ctor_set(v___x_5032_, 1, v_b_5009_);
                    lean_ctor_set(v___x_5032_, 2, v_bkt_5028_);
                    v_buckets_x27_5033_ =
                        lean_array_uset(v_buckets_5011_, v___x_5027_, v___x_5032_);
                    v___x_5034_ = lean_unsigned_to_nat(4);
                    v___x_5035_ = lean_nat_mul(v_size_x27_5031_, v___x_5034_);
                    v___x_5036_ = lean_unsigned_to_nat(3);
                    v___x_5037_ = lean_nat_div(v___x_5035_, v___x_5036_);
                    lean_dec(v___x_5035_);
                    v___x_5038_ = lean_array_get_size(v_buckets_x27_5033_);
                    v___x_5039_ = lean_nat_dec_le(v___x_5037_, v___x_5038_);
                    lean_dec(v___x_5037_);
                    if v___x_5039_ == 0 {
                        v_val_5040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_5033_);
                        if v_isShared_5014_ == 0 {
                            lean_ctor_set(v___x_5013_, 1, v_val_5040_);
                            lean_ctor_set(v___x_5013_, 0, v_size_x27_5031_);
                            v___x_5042_ = v___x_5013_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_size_x27_5031_);
                            lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_val_5040_);
                            v___x_5042_ = v_reuseFailAlloc_5043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5014_ == 0 {
                            lean_ctor_set(v___x_5013_, 1, v_buckets_x27_5033_);
                            lean_ctor_set(v___x_5013_, 0, v_size_x27_5031_);
                            v___x_5045_ = v___x_5013_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_size_x27_5031_);
                            lean_ctor_set(v_reuseFailAlloc_5046_, 1, v_buckets_x27_5033_);
                            v___x_5045_ = v_reuseFailAlloc_5046_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_5028_);
                    v___x_5047_ = lean_box(0);
                    v_buckets_x27_5048_ =
                        lean_array_uset(v_buckets_5011_, v___x_5027_, v___x_5047_);
                    v___x_5049_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_5008_, v_b_5009_, v_bkt_5028_);
                    v___x_5050_ = lean_array_uset(v_buckets_x27_5048_, v___x_5027_, v___x_5049_);
                    if v_isShared_5014_ == 0 {
                        lean_ctor_set(v___x_5013_, 1, v___x_5050_);
                        v___x_5052_ = v___x_5013_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_size_5010_);
                        lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5050_);
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
    mut v___y_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v_r_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v_unused_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5057_ = lean_st_ref_get(v___y_5055_);
                v_ngen_5058_ = lean_ctor_get(v___x_5057_, 2);
                lean_inc_ref(v_ngen_5058_);
                lean_dec(v___x_5057_);
                v_namePrefix_5059_ = lean_ctor_get(v_ngen_5058_, 0);
                v_idx_5060_ = lean_ctor_get(v_ngen_5058_, 1);
                v_isSharedCheck_5089_ = (!lean_is_exclusive(v_ngen_5058_)) as u8;
                if v_isSharedCheck_5089_ == 0 {
                    v___x_5062_ = v_ngen_5058_;
                    v_isShared_5063_ = v_isSharedCheck_5089_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_5060_);
                    lean_inc(v_namePrefix_5059_);
                    lean_dec(v_ngen_5058_);
                    v___x_5062_ = lean_box(0);
                    v_isShared_5063_ = v_isSharedCheck_5089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5064_ = lean_st_ref_take(v___y_5055_);
                v_env_5065_ = lean_ctor_get(v___x_5064_, 0);
                v_nextMacroScope_5066_ = lean_ctor_get(v___x_5064_, 1);
                v_auxDeclNGen_5067_ = lean_ctor_get(v___x_5064_, 3);
                v_traceState_5068_ = lean_ctor_get(v___x_5064_, 4);
                v_cache_5069_ = lean_ctor_get(v___x_5064_, 5);
                v_messages_5070_ = lean_ctor_get(v___x_5064_, 6);
                v_infoState_5071_ = lean_ctor_get(v___x_5064_, 7);
                v_snapshotTasks_5072_ = lean_ctor_get(v___x_5064_, 8);
                v_isSharedCheck_5087_ = (!lean_is_exclusive(v___x_5064_)) as u8;
                if v_isSharedCheck_5087_ == 0 {
                    v_unused_5088_ = lean_ctor_get(v___x_5064_, 2);
                    lean_dec(v_unused_5088_);
                    v___x_5074_ = v___x_5064_;
                    v_isShared_5075_ = v_isSharedCheck_5087_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5072_);
                    lean_inc(v_infoState_5071_);
                    lean_inc(v_messages_5070_);
                    lean_inc(v_cache_5069_);
                    lean_inc(v_traceState_5068_);
                    lean_inc(v_auxDeclNGen_5067_);
                    lean_inc(v_nextMacroScope_5066_);
                    lean_inc(v_env_5065_);
                    lean_dec(v___x_5064_);
                    v___x_5074_ = lean_box(0);
                    v_isShared_5075_ = v_isSharedCheck_5087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_5060_);
                lean_inc(v_namePrefix_5059_);
                v_r_5076_ = l_Lean_Name_num___override(v_namePrefix_5059_, v_idx_5060_);
                v___x_5077_ = lean_unsigned_to_nat(1);
                v___x_5078_ = lean_nat_add(v_idx_5060_, v___x_5077_);
                lean_dec(v_idx_5060_);
                if v_isShared_5063_ == 0 {
                    lean_ctor_set(v___x_5062_, 1, v___x_5078_);
                    v___x_5080_ = v___x_5062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_namePrefix_5059_);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5078_);
                    v___x_5080_ = v_reuseFailAlloc_5086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5075_ == 0 {
                    lean_ctor_set(v___x_5074_, 2, v___x_5080_);
                    v___x_5082_ = v___x_5074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_env_5065_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_nextMacroScope_5066_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 2, v___x_5080_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 3, v_auxDeclNGen_5067_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 4, v_traceState_5068_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 5, v_cache_5069_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 6, v_messages_5070_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 7, v_infoState_5071_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 8, v_snapshotTasks_5072_);
                    v___x_5082_ = v_reuseFailAlloc_5085_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5083_ = lean_st_ref_set(v___y_5055_, v___x_5082_);
                v___x_5084_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5084_, 0, v_r_5076_);
                return v___x_5084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(
    mut v___y_5090_: *mut LeanObject,
    mut v___y_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5092_: *mut LeanObject = core::ptr::null_mut();
    v_res_5092_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5090_);
    lean_dec(v___y_5090_);
    return v_res_5092_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
    mut v___y_5095_: *mut LeanObject,
    mut v___y_5096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5098_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5096_);
                v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
                v_isSharedCheck_5106_ = (!lean_is_exclusive(v___x_5098_)) as u8;
                if v_isSharedCheck_5106_ == 0 {
                    v___x_5101_ = v___x_5098_;
                    v_isShared_5102_ = v_isSharedCheck_5106_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5099_);
                    lean_dec(v___x_5098_);
                    v___x_5101_ = lean_box(0);
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
                    v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
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
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5112_: *mut LeanObject = core::ptr::null_mut();
    v_res_5112_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
        v___y_5107_,
        v___y_5108_,
        v___y_5109_,
        v___y_5110_,
    );
    lean_dec(v___y_5110_);
    lean_dec_ref(v___y_5109_);
    lean_dec(v___y_5108_);
    lean_dec_ref(v___y_5107_);
    return v_res_5112_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(
    mut v_a_5113_: *mut LeanObject,
    mut v_x_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5121_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5114_) == 0 {
                    return v_x_5114_;
                } else {
                    v_key_5115_ = lean_ctor_get(v_x_5114_, 0);
                    v_value_5116_ = lean_ctor_get(v_x_5114_, 1);
                    v_tail_5117_ = lean_ctor_get(v_x_5114_, 2);
                    v_isSharedCheck_5126_ = (!lean_is_exclusive(v_x_5114_)) as u8;
                    if v_isSharedCheck_5126_ == 0 {
                        v___x_5119_ = v_x_5114_;
                        v_isShared_5120_ = v_isSharedCheck_5126_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5117_);
                        lean_inc(v_value_5116_);
                        lean_inc(v_key_5115_);
                        lean_dec(v_x_5114_);
                        v___x_5119_ = lean_box(0);
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
                        lean_ctor_set(v___x_5119_, 2, v___x_5122_);
                        v___x_5124_ = v___x_5119_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_key_5115_);
                        lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_value_5116_);
                        lean_ctor_set(v_reuseFailAlloc_5125_, 2, v___x_5122_);
                        v___x_5124_ = v_reuseFailAlloc_5125_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5119_);
                    lean_dec(v_value_5116_);
                    lean_dec(v_key_5115_);
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
    mut v_a_5127_: *mut LeanObject,
    mut v_x_5128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5129_: *mut LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5127_, v_x_5128_);
    lean_dec(v_a_5127_);
    return v_res_5129_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(
    mut v_m_5130_: *mut LeanObject,
    mut v_a_5131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut v_unused_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5132_ = lean_ctor_get(v_m_5130_, 0);
                v_buckets_5133_ = lean_ctor_get(v_m_5130_, 1);
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
                    lean_inc(v_bkt_5147_);
                    lean_inc_ref(v_buckets_5133_);
                    lean_inc(v_size_5132_);
                    v_isSharedCheck_5161_ = (!lean_is_exclusive(v_m_5130_)) as u8;
                    if v_isSharedCheck_5161_ == 0 {
                        v_unused_5162_ = lean_ctor_get(v_m_5130_, 1);
                        lean_dec(v_unused_5162_);
                        v_unused_5163_ = lean_ctor_get(v_m_5130_, 0);
                        lean_dec(v_unused_5163_);
                        v___x_5150_ = v_m_5130_;
                        v_isShared_5151_ = v_isSharedCheck_5161_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5130_);
                        v___x_5150_ = lean_box(0);
                        v_isShared_5151_ = v_isSharedCheck_5161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5152_ = lean_box(0);
                v_buckets_x27_5153_ = lean_array_uset(v_buckets_5133_, v___x_5146_, v___x_5152_);
                v___x_5154_ = lean_unsigned_to_nat(1);
                v___x_5155_ = lean_nat_sub(v_size_5132_, v___x_5154_);
                lean_dec(v_size_5132_);
                v___x_5156_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5131_, v_bkt_5147_);
                v___x_5157_ = lean_array_uset(v_buckets_x27_5153_, v___x_5146_, v___x_5156_);
                if v_isShared_5151_ == 0 {
                    lean_ctor_set(v___x_5150_, 1, v___x_5157_);
                    lean_ctor_set(v___x_5150_, 0, v___x_5155_);
                    v___x_5159_ = v___x_5150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5155_);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 1, v___x_5157_);
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
    mut v_m_5164_: *mut LeanObject,
    mut v_a_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5166_: *mut LeanObject = core::ptr::null_mut();
    v_res_5166_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_5164_, v_a_5165_);
    lean_dec(v_a_5165_);
    return v_res_5166_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(
    mut v_a_5167_: *mut LeanObject,
    mut v_fallback_5168_: *mut LeanObject,
    mut v_x_5169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5169_) == 0 {
                    lean_inc(v_fallback_5168_);
                    return v_fallback_5168_;
                } else {
                    v_key_5170_ = lean_ctor_get(v_x_5169_, 0);
                    v_value_5171_ = lean_ctor_get(v_x_5169_, 1);
                    v_tail_5172_ = lean_ctor_get(v_x_5169_, 2);
                    v___x_5173_ = l_Lean_instBEqFVarId_beq(v_key_5170_, v_a_5167_);
                    if v___x_5173_ == 0 {
                        v_x_5169_ = v_tail_5172_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_5171_);
                        return v_value_5171_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(
    mut v_a_5175_: *mut LeanObject,
    mut v_fallback_5176_: *mut LeanObject,
    mut v_x_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5178_: *mut LeanObject = core::ptr::null_mut();
    v_res_5178_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_5175_, v_fallback_5176_, v_x_5177_);
    lean_dec(v_x_5177_);
    lean_dec(v_fallback_5176_);
    lean_dec(v_a_5175_);
    return v_res_5178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(
    mut v_m_5179_: *mut LeanObject,
    mut v_a_5180_: *mut LeanObject,
    mut v_fallback_5181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_5182_ = lean_ctor_get(v_m_5179_, 1);
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
    mut v_m_5198_: *mut LeanObject,
    mut v_a_5199_: *mut LeanObject,
    mut v_fallback_5200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5201_: *mut LeanObject = core::ptr::null_mut();
    v_res_5201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_5198_, v_a_5199_, v_fallback_5200_);
    lean_dec(v_fallback_5200_);
    lean_dec(v_a_5199_);
    lean_dec_ref(v_m_5198_);
    return v_res_5201_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2() -> *mut LeanObject {
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    v___x_5205_ = lean_box(0);
    v___x_5206_ = lean_unsigned_to_nat(16);
    v___x_5207_ = lean_mk_array(v___x_5206_, v___x_5205_);
    return v___x_5207_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3() -> *mut LeanObject {
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    v___x_5208_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once),
        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2,
    );
    v___x_5209_ = lean_unsigned_to_nat(0);
    v___x_5210_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5210_, 0, v___x_5209_);
    lean_ctor_set(v___x_5210_, 1, v___x_5208_);
    return v___x_5210_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__1() -> *mut LeanObject {
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    v___x_5213_ = l_Lean_Elab_Tactic_Do_countUses___closed__0;
    v___x_5214_ = l_Lean_stringToMessageData(v___x_5213_);
    return v___x_5214_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__3() -> *mut LeanObject {
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    v___x_5216_ = l_Lean_Elab_Tactic_Do_countUses___closed__2;
    v___x_5217_ = l_Lean_stringToMessageData(v___x_5216_);
    return v___x_5217_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_countUses___closed__5() -> *mut LeanObject {
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    v___x_5219_ = l_Lean_Elab_Tactic_Do_countUses___closed__4;
    v___x_5220_ = l_Lean_stringToMessageData(v___x_5219_);
    return v___x_5220_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses(
    mut v_e_5221_: *mut LeanObject,
    mut v_subst_5222_: *mut LeanObject,
    mut v_a_5223_: *mut LeanObject,
    mut v_a_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_deBruijnIndex_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: u8 = 0;
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v_fst_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5275_: u8 = 0;
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v_binderName_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5289_: u8 = 0;
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v_fst_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_a_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_binderName_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5329_: u8 = 0;
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5341_: u8 = 0;
    let mut v_fst_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut v_declName_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_5370_: u8 = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5378_: u8 = 0;
    let mut v_fst_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v_snd_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v_val_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_unused_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_a_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v_reuseFailAlloc_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut v_a_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5425_: u8 = 0;
    let mut v_data_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___f_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_typeName_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v___f_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5452_: u8 = 0;
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_5221_) {
                0 => {
                    v_deBruijnIndex_5228_ = lean_ctor_get(v_e_5221_, 0);
                    v___x_5229_ = lean_array_get_size(v_subst_5222_);
                    v___x_5230_ = lean_nat_dec_lt(v_deBruijnIndex_5228_, v___x_5229_);
                    if v___x_5230_ == 0 {
                        lean_inc(v_deBruijnIndex_5228_);
                        lean_dec_ref_known(v_e_5221_, 1);
                        lean_dec_ref(v_subst_5222_);
                        v___x_5231_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUses___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUses___closed__1,
                        );
                        v___x_5232_ = l_Nat_reprFast(v_deBruijnIndex_5228_);
                        v___x_5233_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_5233_, 0, v___x_5232_);
                        v___x_5234_ = l_Lean_MessageData_ofFormat(v___x_5233_);
                        v___x_5235_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5235_, 0, v___x_5231_);
                        lean_ctor_set(v___x_5235_, 1, v___x_5234_);
                        v___x_5236_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUses___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUses___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUses___closed__3,
                        );
                        v___x_5237_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5237_, 0, v___x_5235_);
                        lean_ctor_set(v___x_5237_, 1, v___x_5236_);
                        v___x_5238_ = l_Nat_reprFast(v___x_5229_);
                        v___x_5239_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_5239_, 0, v___x_5238_);
                        v___x_5240_ = l_Lean_MessageData_ofFormat(v___x_5239_);
                        v___x_5241_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5241_, 0, v___x_5237_);
                        lean_ctor_set(v___x_5241_, 1, v___x_5240_);
                        v___x_5242_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_5241_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
                        return v___x_5242_;
                    } else {
                        v___x_5243_ = lean_unsigned_to_nat(1);
                        v___x_5244_ = lean_nat_sub(v___x_5229_, v___x_5243_);
                        v___x_5245_ = lean_nat_sub(v___x_5244_, v_deBruijnIndex_5228_);
                        lean_dec(v___x_5244_);
                        v___x_5246_ = lean_array_fget(v_subst_5222_, v___x_5245_);
                        lean_dec(v___x_5245_);
                        lean_dec_ref(v_subst_5222_);
                        v___x_5247_ = 1;
                        v___x_5248_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                        );
                        v___x_5249_ = lean_box((v___x_5247_) as usize);
                        v___x_5250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_5248_, v___x_5246_, v___x_5249_);
                        v___x_5251_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5251_, 0, v_e_5221_);
                        lean_ctor_set(v___x_5251_, 1, v___x_5250_);
                        v___x_5252_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5252_, 0, v___x_5251_);
                        return v___x_5252_;
                    }
                }
                1 => {
                    lean_dec_ref(v_subst_5222_);
                    v_fvarId_5253_ = lean_ctor_get(v_e_5221_, 0);
                    v___x_5254_ = 1;
                    v___x_5255_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                    );
                    v___x_5256_ = lean_box((v___x_5254_) as usize);
                    lean_inc(v_fvarId_5253_);
                    v___x_5257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_5255_, v_fvarId_5253_, v___x_5256_);
                    v___x_5258_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5258_, 0, v_e_5221_);
                    lean_ctor_set(v___x_5258_, 1, v___x_5257_);
                    v___x_5259_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5259_, 0, v___x_5258_);
                    return v___x_5259_;
                }
                5 => {
                    v_fn_5260_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc_ref(v_fn_5260_);
                    v_arg_5261_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc_ref(v_arg_5261_);
                    lean_dec_ref_known(v_e_5221_, 2);
                    lean_inc_ref(v_subst_5222_);
                    v___x_5262_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_fn_5260_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if lean_obj_tag(v___x_5262_) == 0 {
                        v_a_5263_ = lean_ctor_get(v___x_5262_, 0);
                        lean_inc(v_a_5263_);
                        lean_dec_ref_known(v___x_5262_, 1);
                        v_fst_5264_ = lean_ctor_get(v_a_5263_, 0);
                        lean_inc(v_fst_5264_);
                        v_snd_5265_ = lean_ctor_get(v_a_5263_, 1);
                        lean_inc(v_snd_5265_);
                        lean_dec(v_a_5263_);
                        v___x_5266_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_arg_5261_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if lean_obj_tag(v___x_5266_) == 0 {
                            v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
                            v_isSharedCheck_5285_ = (!lean_is_exclusive(v___x_5266_)) as u8;
                            if v_isSharedCheck_5285_ == 0 {
                                v___x_5269_ = v___x_5266_;
                                v_isShared_5270_ = v_isSharedCheck_5285_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5267_);
                                lean_dec(v___x_5266_);
                                v___x_5269_ = lean_box(0);
                                v_isShared_5270_ = v_isSharedCheck_5285_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_5265_);
                            lean_dec(v_fst_5264_);
                            return v___x_5266_;
                        }
                    } else {
                        lean_dec_ref(v_arg_5261_);
                        lean_dec_ref(v_subst_5222_);
                        return v___x_5262_;
                    }
                }
                6 => {
                    v_binderName_5286_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc(v_binderName_5286_);
                    v_binderType_5287_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc_ref(v_binderType_5287_);
                    v_body_5288_ = lean_ctor_get(v_e_5221_, 2);
                    lean_inc_ref(v_body_5288_);
                    v_binderInfo_5289_ = lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5290_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if lean_obj_tag(v___x_5290_) == 0 {
                        v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
                        lean_inc(v_a_5291_);
                        lean_dec_ref_known(v___x_5290_, 1);
                        lean_inc_ref(v_subst_5222_);
                        v___x_5292_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_binderType_5287_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if lean_obj_tag(v___x_5292_) == 0 {
                            v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
                            lean_inc(v_a_5293_);
                            lean_dec_ref_known(v___x_5292_, 1);
                            v_fst_5294_ = lean_ctor_get(v_a_5293_, 0);
                            lean_inc(v_fst_5294_);
                            v_snd_5295_ = lean_ctor_get(v_a_5293_, 1);
                            lean_inc(v_snd_5295_);
                            lean_dec(v_a_5293_);
                            lean_inc(v_a_5291_);
                            v___x_5296_ = lean_array_push(v_subst_5222_, v_a_5291_);
                            v___x_5297_ = l_Lean_Elab_Tactic_Do_countUses(
                                v_body_5288_,
                                v___x_5296_,
                                v_a_5223_,
                                v_a_5224_,
                                v_a_5225_,
                                v_a_5226_,
                            );
                            if lean_obj_tag(v___x_5297_) == 0 {
                                v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
                                v_isSharedCheck_5317_ = (!lean_is_exclusive(v___x_5297_)) as u8;
                                if v_isSharedCheck_5317_ == 0 {
                                    v___x_5300_ = v___x_5297_;
                                    v_isShared_5301_ = v_isSharedCheck_5317_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5298_);
                                    lean_dec(v___x_5297_);
                                    v___x_5300_ = lean_box(0);
                                    v_isShared_5301_ = v_isSharedCheck_5317_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_5295_);
                                lean_dec(v_fst_5294_);
                                lean_dec(v_a_5291_);
                                lean_dec(v_binderName_5286_);
                                return v___x_5297_;
                            }
                        } else {
                            lean_dec(v_a_5291_);
                            lean_dec_ref(v_body_5288_);
                            lean_dec(v_binderName_5286_);
                            lean_dec_ref(v_subst_5222_);
                            return v___x_5292_;
                        }
                    } else {
                        lean_dec_ref(v_body_5288_);
                        lean_dec_ref(v_binderType_5287_);
                        lean_dec(v_binderName_5286_);
                        lean_dec_ref(v_subst_5222_);
                        v_a_5318_ = lean_ctor_get(v___x_5290_, 0);
                        v_isSharedCheck_5325_ = (!lean_is_exclusive(v___x_5290_)) as u8;
                        if v_isSharedCheck_5325_ == 0 {
                            v___x_5320_ = v___x_5290_;
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5318_);
                            lean_dec(v___x_5290_);
                            v___x_5320_ = lean_box(0);
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 9;
                            continue;
                        }
                    }
                }
                7 => {
                    v_binderName_5326_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc(v_binderName_5326_);
                    v_binderType_5327_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc_ref(v_binderType_5327_);
                    v_body_5328_ = lean_ctor_get(v_e_5221_, 2);
                    lean_inc_ref(v_body_5328_);
                    v_binderInfo_5329_ = lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5330_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if lean_obj_tag(v___x_5330_) == 0 {
                        v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
                        lean_inc(v_a_5331_);
                        lean_dec_ref_known(v___x_5330_, 1);
                        lean_inc_ref(v_subst_5222_);
                        v___x_5332_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_binderType_5327_,
                            v_subst_5222_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if lean_obj_tag(v___x_5332_) == 0 {
                            v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
                            lean_inc(v_a_5333_);
                            lean_dec_ref_known(v___x_5332_, 1);
                            v_fst_5334_ = lean_ctor_get(v_a_5333_, 0);
                            lean_inc(v_fst_5334_);
                            v_snd_5335_ = lean_ctor_get(v_a_5333_, 1);
                            lean_inc(v_snd_5335_);
                            lean_dec(v_a_5333_);
                            lean_inc(v_a_5331_);
                            v___x_5336_ = lean_array_push(v_subst_5222_, v_a_5331_);
                            v___x_5337_ = l_Lean_Elab_Tactic_Do_countUses(
                                v_body_5328_,
                                v___x_5336_,
                                v_a_5223_,
                                v_a_5224_,
                                v_a_5225_,
                                v_a_5226_,
                            );
                            if lean_obj_tag(v___x_5337_) == 0 {
                                v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
                                v_isSharedCheck_5357_ = (!lean_is_exclusive(v___x_5337_)) as u8;
                                if v_isSharedCheck_5357_ == 0 {
                                    v___x_5340_ = v___x_5337_;
                                    v_isShared_5341_ = v_isSharedCheck_5357_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5338_);
                                    lean_dec(v___x_5337_);
                                    v___x_5340_ = lean_box(0);
                                    v_isShared_5341_ = v_isSharedCheck_5357_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_5335_);
                                lean_dec(v_fst_5334_);
                                lean_dec(v_a_5331_);
                                lean_dec(v_binderName_5326_);
                                return v___x_5337_;
                            }
                        } else {
                            lean_dec(v_a_5331_);
                            lean_dec_ref(v_body_5328_);
                            lean_dec(v_binderName_5326_);
                            lean_dec_ref(v_subst_5222_);
                            return v___x_5332_;
                        }
                    } else {
                        lean_dec_ref(v_body_5328_);
                        lean_dec_ref(v_binderType_5327_);
                        lean_dec(v_binderName_5326_);
                        lean_dec_ref(v_subst_5222_);
                        v_a_5358_ = lean_ctor_get(v___x_5330_, 0);
                        v_isSharedCheck_5365_ = (!lean_is_exclusive(v___x_5330_)) as u8;
                        if v_isSharedCheck_5365_ == 0 {
                            v___x_5360_ = v___x_5330_;
                            v_isShared_5361_ = v_isSharedCheck_5365_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5358_);
                            lean_dec(v___x_5330_);
                            v___x_5360_ = lean_box(0);
                            v_isShared_5361_ = v_isSharedCheck_5365_;
                            state = 15;
                            continue;
                        }
                    }
                }
                8 => {
                    v_declName_5366_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc(v_declName_5366_);
                    v_type_5367_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc_ref(v_type_5367_);
                    v_value_5368_ = lean_ctor_get(v_e_5221_, 2);
                    lean_inc_ref(v_value_5368_);
                    v_body_5369_ = lean_ctor_get(v_e_5221_, 3);
                    lean_inc_ref(v_body_5369_);
                    v_nondep_5370_ = lean_ctor_get_uint8(
                        v_e_5221_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_5221_, 4);
                    v___x_5371_ =
                        l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(
                            v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
                        );
                    if lean_obj_tag(v___x_5371_) == 0 {
                        v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
                        lean_inc_n(v_a_5372_, 2);
                        lean_dec_ref_known(v___x_5371_, 1);
                        lean_inc_ref(v_subst_5222_);
                        v___x_5373_ = lean_array_push(v_subst_5222_, v_a_5372_);
                        v___x_5374_ = l_Lean_Elab_Tactic_Do_countUses(
                            v_body_5369_,
                            v___x_5373_,
                            v_a_5223_,
                            v_a_5224_,
                            v_a_5225_,
                            v_a_5226_,
                        );
                        if lean_obj_tag(v___x_5374_) == 0 {
                            v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
                            v_isSharedCheck_5417_ = (!lean_is_exclusive(v___x_5374_)) as u8;
                            if v_isSharedCheck_5417_ == 0 {
                                v___x_5377_ = v___x_5374_;
                                v_isShared_5378_ = v_isSharedCheck_5417_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_5375_);
                                lean_dec(v___x_5374_);
                                v___x_5377_ = lean_box(0);
                                v_isShared_5378_ = v_isSharedCheck_5417_;
                                state = 17;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5372_);
                            lean_dec_ref(v_value_5368_);
                            lean_dec_ref(v_type_5367_);
                            lean_dec(v_declName_5366_);
                            lean_dec_ref(v_subst_5222_);
                            return v___x_5374_;
                        }
                    } else {
                        lean_dec_ref(v_body_5369_);
                        lean_dec_ref(v_value_5368_);
                        lean_dec_ref(v_type_5367_);
                        lean_dec(v_declName_5366_);
                        lean_dec_ref(v_subst_5222_);
                        v_a_5418_ = lean_ctor_get(v___x_5371_, 0);
                        v_isSharedCheck_5425_ = (!lean_is_exclusive(v___x_5371_)) as u8;
                        if v_isSharedCheck_5425_ == 0 {
                            v___x_5420_ = v___x_5371_;
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5418_);
                            lean_dec(v___x_5371_);
                            v___x_5420_ = lean_box(0);
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 25;
                            continue;
                        }
                    }
                }
                10 => {
                    v_data_5426_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc(v_data_5426_);
                    v_expr_5427_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc_ref(v_expr_5427_);
                    lean_dec_ref_known(v_e_5221_, 2);
                    v___x_5428_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_expr_5427_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if lean_obj_tag(v___x_5428_) == 0 {
                        v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
                        v_isSharedCheck_5438_ = (!lean_is_exclusive(v___x_5428_)) as u8;
                        if v_isSharedCheck_5438_ == 0 {
                            v___x_5431_ = v___x_5428_;
                            v_isShared_5432_ = v_isSharedCheck_5438_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_5429_);
                            lean_dec(v___x_5428_);
                            v___x_5431_ = lean_box(0);
                            v_isShared_5432_ = v_isSharedCheck_5438_;
                            state = 27;
                            continue;
                        }
                    } else {
                        lean_dec(v_data_5426_);
                        return v___x_5428_;
                    }
                }
                11 => {
                    v_typeName_5439_ = lean_ctor_get(v_e_5221_, 0);
                    lean_inc(v_typeName_5439_);
                    v_idx_5440_ = lean_ctor_get(v_e_5221_, 1);
                    lean_inc(v_idx_5440_);
                    v_struct_5441_ = lean_ctor_get(v_e_5221_, 2);
                    lean_inc_ref(v_struct_5441_);
                    lean_dec_ref_known(v_e_5221_, 3);
                    v___x_5442_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_struct_5441_,
                        v_subst_5222_,
                        v_a_5223_,
                        v_a_5224_,
                        v_a_5225_,
                        v_a_5226_,
                    );
                    if lean_obj_tag(v___x_5442_) == 0 {
                        v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5452_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5452_ == 0 {
                            v___x_5445_ = v___x_5442_;
                            v_isShared_5446_ = v_isSharedCheck_5452_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_5443_);
                            lean_dec(v___x_5442_);
                            v___x_5445_ = lean_box(0);
                            v_isShared_5446_ = v_isSharedCheck_5452_;
                            state = 29;
                            continue;
                        }
                    } else {
                        lean_dec(v_idx_5440_);
                        lean_dec(v_typeName_5439_);
                        return v___x_5442_;
                    }
                }
                _ => {
                    lean_dec_ref(v_subst_5222_);
                    v___x_5453_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                    );
                    v___x_5454_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5454_, 0, v_e_5221_);
                    lean_ctor_set(v___x_5454_, 1, v___x_5453_);
                    v___x_5455_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5455_, 0, v___x_5454_);
                    return v___x_5455_;
                }
            },
            1 => {
                v_fst_5271_ = lean_ctor_get(v_a_5267_, 0);
                v_snd_5272_ = lean_ctor_get(v_a_5267_, 1);
                v_isSharedCheck_5284_ = (!lean_is_exclusive(v_a_5267_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v___x_5274_ = v_a_5267_;
                    v_isShared_5275_ = v_isSharedCheck_5284_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5272_);
                    lean_inc(v_fst_5271_);
                    lean_dec(v_a_5267_);
                    v___x_5274_ = lean_box(0);
                    v_isShared_5275_ = v_isSharedCheck_5284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5276_ = l_Lean_Expr_app___override(v_fst_5264_, v_fst_5271_);
                v___x_5277_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5265_, v_snd_5272_);
                lean_dec(v_snd_5265_);
                if v_isShared_5275_ == 0 {
                    lean_ctor_set(v___x_5274_, 1, v___x_5277_);
                    lean_ctor_set(v___x_5274_, 0, v___x_5276_);
                    v___x_5279_ = v___x_5274_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5276_);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5277_);
                    v___x_5279_ = v_reuseFailAlloc_5283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5270_ == 0 {
                    lean_ctor_set(v___x_5269_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5281_;
            }
            5 => {
                v_fst_5302_ = lean_ctor_get(v_a_5298_, 0);
                v_snd_5303_ = lean_ctor_get(v_a_5298_, 1);
                v_isSharedCheck_5316_ = (!lean_is_exclusive(v_a_5298_)) as u8;
                if v_isSharedCheck_5316_ == 0 {
                    v___x_5305_ = v_a_5298_;
                    v_isShared_5306_ = v_isSharedCheck_5316_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_5303_);
                    lean_inc(v_fst_5302_);
                    lean_dec(v_a_5298_);
                    v___x_5305_ = lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5316_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5307_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5295_, v_snd_5303_);
                lean_dec(v_snd_5295_);
                v___x_5308_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_5307_, v_a_5291_);
                lean_dec(v_a_5291_);
                v___x_5309_ = l_Lean_Expr_lam___override(
                    v_binderName_5286_,
                    v_fst_5294_,
                    v_fst_5302_,
                    v_binderInfo_5289_,
                );
                if v_isShared_5306_ == 0 {
                    lean_ctor_set(v___x_5305_, 1, v___x_5308_);
                    lean_ctor_set(v___x_5305_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5305_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5309_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 1, v___x_5308_);
                    v___x_5311_ = v_reuseFailAlloc_5315_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5301_ == 0 {
                    lean_ctor_set(v___x_5300_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5300_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
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
                    v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5323_;
            }
            11 => {
                v_fst_5342_ = lean_ctor_get(v_a_5338_, 0);
                v_snd_5343_ = lean_ctor_get(v_a_5338_, 1);
                v_isSharedCheck_5356_ = (!lean_is_exclusive(v_a_5338_)) as u8;
                if v_isSharedCheck_5356_ == 0 {
                    v___x_5345_ = v_a_5338_;
                    v_isShared_5346_ = v_isSharedCheck_5356_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_5343_);
                    lean_inc(v_fst_5342_);
                    lean_dec(v_a_5338_);
                    v___x_5345_ = lean_box(0);
                    v_isShared_5346_ = v_isSharedCheck_5356_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5347_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_5335_, v_snd_5343_);
                lean_dec(v_snd_5335_);
                v___x_5348_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_5347_, v_a_5331_);
                lean_dec(v_a_5331_);
                v___x_5349_ = l_Lean_Expr_forallE___override(
                    v_binderName_5326_,
                    v_fst_5334_,
                    v_fst_5342_,
                    v_binderInfo_5329_,
                );
                if v_isShared_5346_ == 0 {
                    lean_ctor_set(v___x_5345_, 1, v___x_5348_);
                    lean_ctor_set(v___x_5345_, 0, v___x_5349_);
                    v___x_5351_ = v___x_5345_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5349_);
                    lean_ctor_set(v_reuseFailAlloc_5355_, 1, v___x_5348_);
                    v___x_5351_ = v_reuseFailAlloc_5355_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5341_ == 0 {
                    lean_ctor_set(v___x_5340_, 0, v___x_5351_);
                    v___x_5353_ = v___x_5340_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5351_);
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
                    v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5363_;
            }
            17 => {
                v_fst_5379_ = lean_ctor_get(v_a_5375_, 0);
                lean_inc(v_fst_5379_);
                v_snd_5380_ = lean_ctor_get(v_a_5375_, 1);
                lean_inc(v_snd_5380_);
                lean_dec(v_a_5375_);
                if v_isShared_5378_ == 0 {
                    lean_ctor_set_tag(v___x_5377_, 1);
                    lean_ctor_set(v___x_5377_, 0, v_value_5368_);
                    v___x_5382_ = v___x_5377_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_value_5368_);
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
                lean_dec(v_a_5372_);
                if lean_obj_tag(v___x_5383_) == 0 {
                    v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
                    v_isSharedCheck_5407_ = (!lean_is_exclusive(v___x_5383_)) as u8;
                    if v_isSharedCheck_5407_ == 0 {
                        v___x_5386_ = v___x_5383_;
                        v_isShared_5387_ = v_isSharedCheck_5407_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_5384_);
                        lean_dec(v___x_5383_);
                        v___x_5386_ = lean_box(0);
                        v_isShared_5387_ = v_isSharedCheck_5407_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5379_);
                    lean_dec(v_declName_5366_);
                    v_a_5408_ = lean_ctor_get(v___x_5383_, 0);
                    v_isSharedCheck_5415_ = (!lean_is_exclusive(v___x_5383_)) as u8;
                    if v_isSharedCheck_5415_ == 0 {
                        v___x_5410_ = v___x_5383_;
                        v_isShared_5411_ = v_isSharedCheck_5415_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_5408_);
                        lean_dec(v___x_5383_);
                        v___x_5410_ = lean_box(0);
                        v_isShared_5411_ = v_isSharedCheck_5415_;
                        state = 23;
                        continue;
                    }
                }
            }
            19 => {
                v_snd_5388_ = lean_ctor_get(v_a_5384_, 1);
                lean_inc(v_snd_5388_);
                v_fst_5389_ = lean_ctor_get(v_snd_5388_, 0);
                lean_inc(v_fst_5389_);
                if lean_obj_tag(v_fst_5389_) == 1 {
                    v_fst_5390_ = lean_ctor_get(v_a_5384_, 0);
                    lean_inc(v_fst_5390_);
                    lean_dec(v_a_5384_);
                    v_snd_5391_ = lean_ctor_get(v_snd_5388_, 1);
                    v_isSharedCheck_5403_ = (!lean_is_exclusive(v_snd_5388_)) as u8;
                    if v_isSharedCheck_5403_ == 0 {
                        v_unused_5404_ = lean_ctor_get(v_snd_5388_, 0);
                        lean_dec(v_unused_5404_);
                        v___x_5393_ = v_snd_5388_;
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_snd_5391_);
                        lean_dec(v_snd_5388_);
                        v___x_5393_ = lean_box(0);
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5389_);
                    lean_dec(v_snd_5388_);
                    lean_del_object(v___x_5386_);
                    lean_dec(v_a_5384_);
                    lean_dec(v_fst_5379_);
                    lean_dec(v_declName_5366_);
                    v___x_5405_ = lean_obj_once(
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
                v_val_5395_ = lean_ctor_get(v_fst_5389_, 0);
                lean_inc(v_val_5395_);
                lean_dec_ref_known(v_fst_5389_, 1);
                v___x_5396_ = l_Lean_Expr_letE___override(
                    v_declName_5366_,
                    v_fst_5390_,
                    v_val_5395_,
                    v_fst_5379_,
                    v_nondep_5370_,
                );
                if v_isShared_5394_ == 0 {
                    lean_ctor_set(v___x_5393_, 0, v___x_5396_);
                    v___x_5398_ = v___x_5393_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5396_);
                    lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_snd_5391_);
                    v___x_5398_ = v_reuseFailAlloc_5402_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5387_ == 0 {
                    lean_ctor_set(v___x_5386_, 0, v___x_5398_);
                    v___x_5400_ = v___x_5386_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
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
                    v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
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
                    v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
                    v___x_5423_ = v_reuseFailAlloc_5424_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5423_;
            }
            27 => {
                v___f_5433_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_countUses___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_5433_, 0, v_data_5426_);
                v___x_5434_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5433_, v_a_5429_);
                if v_isShared_5432_ == 0 {
                    lean_ctor_set(v___x_5431_, 0, v___x_5434_);
                    v___x_5436_ = v___x_5431_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5436_;
            }
            29 => {
                v___f_5447_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_countUses___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_5447_, 0, v_typeName_5439_);
                lean_closure_set(v___f_5447_, 1, v_idx_5440_);
                v___x_5448_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5447_, v_a_5443_);
                if v_isShared_5446_ == 0 {
                    lean_ctor_set(v___x_5445_, 0, v___x_5448_);
                    v___x_5450_ = v___x_5445_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5448_);
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
    mut v_fvarId_5456_: *mut LeanObject,
    mut v_ty_5457_: *mut LeanObject,
    mut v_val_x3f_5458_: *mut LeanObject,
    mut v_bodyUses_5459_: *mut LeanObject,
    mut v_subst_5460_: *mut LeanObject,
    mut v_a_5461_: *mut LeanObject,
    mut v_a_5462_: *mut LeanObject,
    mut v_a_5463_: *mut LeanObject,
    mut v_a_5464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v_fst_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___y_5477_: u8 = 0;
    let mut v___y_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: u8 = 0;
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5516_: u8 = 0;
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_a_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_subst_5460_);
                v___x_5466_ = l_Lean_Elab_Tactic_Do_countUses(
                    v_ty_5457_,
                    v_subst_5460_,
                    v_a_5461_,
                    v_a_5462_,
                    v_a_5463_,
                    v_a_5464_,
                );
                if lean_obj_tag(v___x_5466_) == 0 {
                    v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5522_ = (!lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5522_ == 0 {
                        v___x_5469_ = v___x_5466_;
                        v_isShared_5470_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5467_);
                        lean_dec(v___x_5466_);
                        v___x_5469_ = lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_subst_5460_);
                    lean_dec_ref(v_bodyUses_5459_);
                    lean_dec(v_val_x3f_5458_);
                    v_a_5523_ = lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5530_ = (!lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5466_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5523_);
                        lean_dec(v___x_5466_);
                        v___x_5525_ = lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5471_ = lean_ctor_get(v_a_5467_, 0);
                v_snd_5472_ = lean_ctor_get(v_a_5467_, 1);
                v_isSharedCheck_5521_ = (!lean_is_exclusive(v_a_5467_)) as u8;
                if v_isSharedCheck_5521_ == 0 {
                    v___x_5474_ = v_a_5467_;
                    v_isShared_5475_ = v_isSharedCheck_5521_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5472_);
                    lean_inc(v_fst_5471_);
                    lean_dec(v_a_5467_);
                    v___x_5474_ = lean_box(0);
                    v_isShared_5475_ = v_isSharedCheck_5521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_val_x3f_5458_) == 0 {
                    lean_dec_ref(v_subst_5460_);
                    v___x_5505_ = lean_obj_once(
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
                    v_val_5506_ = lean_ctor_get(v_val_x3f_5458_, 0);
                    lean_inc(v_val_5506_);
                    lean_dec_ref_known(v_val_x3f_5458_, 1);
                    v___x_5507_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_val_5506_,
                        v_subst_5460_,
                        v_a_5461_,
                        v_a_5462_,
                        v_a_5463_,
                        v_a_5464_,
                    );
                    if lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
                        lean_inc(v_a_5508_);
                        lean_dec_ref_known(v___x_5507_, 1);
                        v___f_5509_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
                        v___x_5510_ =
                            l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_5509_, v_a_5508_);
                        v_fst_5511_ = lean_ctor_get(v___x_5510_, 0);
                        lean_inc(v_fst_5511_);
                        v_snd_5512_ = lean_ctor_get(v___x_5510_, 1);
                        lean_inc(v_snd_5512_);
                        lean_dec_ref(v___x_5510_);
                        v_fst_5494_ = v_fst_5511_;
                        v_snd_5495_ = v_snd_5512_;
                        state = 6;
                        continue;
                    } else {
                        lean_del_object(v___x_5474_);
                        lean_dec(v_snd_5472_);
                        lean_dec(v_fst_5471_);
                        lean_del_object(v___x_5469_);
                        lean_dec_ref(v_bodyUses_5459_);
                        v_a_5513_ = lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5520_ = (!lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5520_ == 0 {
                            v___x_5515_ = v___x_5507_;
                            v_isShared_5516_ = v_isSharedCheck_5520_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5513_);
                            lean_dec(v___x_5507_);
                            v___x_5515_ = lean_box(0);
                            v_isShared_5516_ = v_isSharedCheck_5520_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_5480_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_5479_, v_fvarId_5456_);
                v___x_5481_ = lean_box(0);
                v___x_5482_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                v___x_5483_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_5477_);
                v___x_5484_ = l_Lean_KVMap_setNat(v___x_5481_, v___x_5482_, v___x_5483_);
                v___x_5485_ = l_Lean_Elab_Tactic_Do_addMData(v___x_5484_, v_fst_5471_);
                if v_isShared_5475_ == 0 {
                    lean_ctor_set(v___x_5474_, 1, v___x_5480_);
                    lean_ctor_set(v___x_5474_, 0, v___y_5478_);
                    v___x_5487_ = v___x_5474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___y_5478_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 1, v___x_5480_);
                    v___x_5487_ = v_reuseFailAlloc_5492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5488_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5488_, 0, v___x_5485_);
                lean_ctor_set(v___x_5488_, 1, v___x_5487_);
                if v_isShared_5470_ == 0 {
                    lean_ctor_set(v___x_5469_, 0, v___x_5488_);
                    v___x_5490_ = v___x_5469_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
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
                v___x_5497_ = lean_box((v___x_5496_) as usize);
                v___x_5498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_5459_, v_fvarId_5456_, v___x_5497_);
                lean_dec(v___x_5497_);
                v___x_5499_ = (lean_unbox(v___x_5498_) as u8);
                v___x_5500_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_5499_, v___x_5496_);
                if v___x_5500_ == 0 {
                    v___x_5501_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_5459_, v_snd_5472_);
                    lean_dec_ref(v_bodyUses_5459_);
                    v___x_5502_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_5501_, v_snd_5495_);
                    lean_dec_ref(v___x_5501_);
                    v___x_5503_ = (lean_unbox(v___x_5498_) as u8);
                    lean_dec(v___x_5498_);
                    v___y_5477_ = v___x_5503_;
                    v___y_5478_ = v_fst_5494_;
                    v___y_5479_ = v___x_5502_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_snd_5495_);
                    lean_dec(v_snd_5472_);
                    v___x_5504_ = (lean_unbox(v___x_5498_) as u8);
                    lean_dec(v___x_5498_);
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
                    v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
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
                    v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
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
    mut v_fvarId_5531_: *mut LeanObject,
    mut v_ty_5532_: *mut LeanObject,
    mut v_val_x3f_5533_: *mut LeanObject,
    mut v_bodyUses_5534_: *mut LeanObject,
    mut v_subst_5535_: *mut LeanObject,
    mut v_a_5536_: *mut LeanObject,
    mut v_a_5537_: *mut LeanObject,
    mut v_a_5538_: *mut LeanObject,
    mut v_a_5539_: *mut LeanObject,
    mut v_a_5540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5541_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5539_);
    lean_dec_ref(v_a_5538_);
    lean_dec(v_a_5537_);
    lean_dec_ref(v_a_5536_);
    lean_dec(v_fvarId_5531_);
    return v_res_5541_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUses___boxed(
    mut v_e_5542_: *mut LeanObject,
    mut v_subst_5543_: *mut LeanObject,
    mut v_a_5544_: *mut LeanObject,
    mut v_a_5545_: *mut LeanObject,
    mut v_a_5546_: *mut LeanObject,
    mut v_a_5547_: *mut LeanObject,
    mut v_a_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5549_: *mut LeanObject = core::ptr::null_mut();
    v_res_5549_ = l_Lean_Elab_Tactic_Do_countUses(
        v_e_5542_,
        v_subst_5543_,
        v_a_5544_,
        v_a_5545_,
        v_a_5546_,
        v_a_5547_,
    );
    lean_dec(v_a_5547_);
    lean_dec_ref(v_a_5546_);
    lean_dec(v_a_5545_);
    lean_dec_ref(v_a_5544_);
    return v_res_5549_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(
    mut v_00_u03b2_5550_: *mut LeanObject,
    mut v_m_5551_: *mut LeanObject,
    mut v_a_5552_: *mut LeanObject,
    mut v_fallback_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    v___x_5554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_5551_, v_a_5552_, v_fallback_5553_);
    return v___x_5554_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(
    mut v_00_u03b2_5555_: *mut LeanObject,
    mut v_m_5556_: *mut LeanObject,
    mut v_a_5557_: *mut LeanObject,
    mut v_fallback_5558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5559_: *mut LeanObject = core::ptr::null_mut();
    v_res_5559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_5555_, v_m_5556_, v_a_5557_, v_fallback_5558_);
    lean_dec(v_fallback_5558_);
    lean_dec(v_a_5557_);
    lean_dec_ref(v_m_5556_);
    return v_res_5559_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(
    mut v_00_u03b2_5560_: *mut LeanObject,
    mut v_m_5561_: *mut LeanObject,
    mut v_a_5562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_5561_, v_a_5562_);
    return v___x_5563_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(
    mut v_00_u03b2_5564_: *mut LeanObject,
    mut v_m_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5567_: *mut LeanObject = core::ptr::null_mut();
    v_res_5567_ =
        l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(
            v_00_u03b2_5564_,
            v_m_5565_,
            v_a_5566_,
        );
    lean_dec(v_a_5566_);
    return v_res_5567_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(
    mut v_00_u03b1_5568_: *mut LeanObject,
    mut v_msg_5569_: *mut LeanObject,
    mut v___y_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
    mut v___y_5573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5576_: *mut LeanObject,
    mut v_msg_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
    mut v___y_5580_: *mut LeanObject,
    mut v___y_5581_: *mut LeanObject,
    mut v___y_5582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5583_: *mut LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(
        v_00_u03b1_5576_,
        v_msg_5577_,
        v___y_5578_,
        v___y_5579_,
        v___y_5580_,
        v___y_5581_,
    );
    lean_dec(v___y_5581_);
    lean_dec_ref(v___y_5580_);
    lean_dec(v___y_5579_);
    lean_dec_ref(v___y_5578_);
    return v_res_5583_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(
    mut v_00_u03b2_5584_: *mut LeanObject,
    mut v_m_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_b_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    v___x_5588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_5585_, v_a_5586_, v_b_5587_);
    return v___x_5588_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(
    mut v___y_5589_: *mut LeanObject,
    mut v___y_5590_: *mut LeanObject,
    mut v___y_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    v___x_5594_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_5592_);
    return v___x_5594_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5600_: *mut LeanObject = core::ptr::null_mut();
    v_res_5600_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    lean_dec(v___y_5598_);
    lean_dec_ref(v___y_5597_);
    lean_dec(v___y_5596_);
    lean_dec_ref(v___y_5595_);
    return v_res_5600_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(
    mut v_00_u03b2_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
    mut v_fallback_5603_: *mut LeanObject,
    mut v_x_5604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_5602_, v_fallback_5603_, v_x_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_5606_: *mut LeanObject,
    mut v_a_5607_: *mut LeanObject,
    mut v_fallback_5608_: *mut LeanObject,
    mut v_x_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5610_: *mut LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_5606_, v_a_5607_, v_fallback_5608_, v_x_5609_);
    lean_dec(v_x_5609_);
    lean_dec(v_fallback_5608_);
    lean_dec(v_a_5607_);
    return v_res_5610_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(
    mut v_00_u03b2_5611_: *mut LeanObject,
    mut v_a_5612_: *mut LeanObject,
    mut v_x_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    v___x_5614_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_5612_, v_x_5613_);
    return v___x_5614_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(
    mut v_00_u03b2_5615_: *mut LeanObject,
    mut v_a_5616_: *mut LeanObject,
    mut v_x_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5618_: *mut LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_5615_, v_a_5616_, v_x_5617_);
    lean_dec(v_a_5616_);
    return v_res_5618_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(
    mut v_00_u03b2_5619_: *mut LeanObject,
    mut v_a_5620_: *mut LeanObject,
    mut v_b_5621_: *mut LeanObject,
    mut v_x_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_5620_, v_b_5621_, v_x_5622_);
    return v___x_5623_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(
    mut v_as_5626_: *mut LeanObject,
    mut v_i_5627_: usize,
    mut v_stop_5628_: usize,
    mut v_b_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: usize = 0;
    let mut v___x_5637_: usize = 0;
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v___y_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5635_ = lean_usize_dec_eq(v_i_5627_, v_stop_5628_);
                if v___x_5635_ == 0 {
                    v___x_5636_ = 1usize;
                    v___x_5637_ = lean_usize_sub(v_i_5627_, v___x_5636_);
                    v___x_5638_ = lean_array_uget_borrowed(v_as_5626_, v___x_5637_);
                    if lean_obj_tag(v___x_5638_) == 0 {
                        v_i_5627_ = v___x_5637_;
                        state = 0;
                        continue;
                    } else {
                        v_val_5640_ = lean_ctor_get(v___x_5638_, 0);
                        v_fst_5641_ = lean_ctor_get(v_b_5629_, 0);
                        lean_inc(v_fst_5641_);
                        v_snd_5642_ = lean_ctor_get(v_b_5629_, 1);
                        lean_inc(v_snd_5642_);
                        lean_dec_ref(v_b_5629_);
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
                        lean_dec(v___x_5643_);
                        if lean_obj_tag(v___x_5647_) == 0 {
                            v_a_5648_ = lean_ctor_get(v___x_5647_, 0);
                            lean_inc(v_a_5648_);
                            lean_dec_ref_known(v___x_5647_, 1);
                            v_snd_5649_ = lean_ctor_get(v_a_5648_, 1);
                            lean_inc(v_snd_5649_);
                            v_fst_5650_ = lean_ctor_get(v_a_5648_, 0);
                            lean_inc(v_fst_5650_);
                            lean_dec(v_a_5648_);
                            v_fst_5651_ = lean_ctor_get(v_snd_5649_, 0);
                            v_snd_5652_ = lean_ctor_get(v_snd_5649_, 1);
                            v_isSharedCheck_5667_ = (!lean_is_exclusive(v_snd_5649_)) as u8;
                            if v_isSharedCheck_5667_ == 0 {
                                v___x_5654_ = v_snd_5649_;
                                v_isShared_5655_ = v_isSharedCheck_5667_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_5652_);
                                lean_inc(v_fst_5651_);
                                lean_dec(v_snd_5649_);
                                v___x_5654_ = lean_box(0);
                                v_isShared_5655_ = v_isSharedCheck_5667_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_5641_);
                            v_a_5668_ = lean_ctor_get(v___x_5647_, 0);
                            v_isSharedCheck_5675_ = (!lean_is_exclusive(v___x_5647_)) as u8;
                            if v_isSharedCheck_5675_ == 0 {
                                v___x_5670_ = v___x_5647_;
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5668_);
                                lean_dec(v___x_5647_);
                                v___x_5670_ = lean_box(0);
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5676_, 0, v_b_5629_);
                    return v___x_5676_;
                }
            }
            1 => {
                if lean_obj_tag(v_fst_5651_) == 0 {
                    lean_inc(v_val_5640_);
                    v___x_5663_ = l_Lean_LocalDecl_setType(v_val_5640_, v_fst_5650_);
                    v___y_5657_ = v___x_5663_;
                    state = 2;
                    continue;
                } else {
                    v_val_5664_ = lean_ctor_get(v_fst_5651_, 0);
                    lean_inc(v_val_5664_);
                    lean_dec_ref_known(v_fst_5651_, 1);
                    lean_inc(v_val_5640_);
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
                    lean_ctor_set(v___x_5654_, 0, v___x_5658_);
                    v___x_5660_ = v___x_5654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5658_);
                    lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_snd_5652_);
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
                    v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
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
    mut v_as_5677_: *mut LeanObject,
    mut v_i_5678_: *mut LeanObject,
    mut v_stop_5679_: *mut LeanObject,
    mut v_b_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5686_: usize = 0;
    let mut v_stop_boxed_5687_: usize = 0;
    let mut v_res_5688_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5686_ = lean_unbox_usize(v_i_5678_);
    lean_dec(v_i_5678_);
    v_stop_boxed_5687_ = lean_unbox_usize(v_stop_5679_);
    lean_dec(v_stop_5679_);
    v_res_5688_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_5677_, v_i_boxed_5686_, v_stop_boxed_5687_, v_b_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    lean_dec(v___y_5684_);
    lean_dec_ref(v___y_5683_);
    lean_dec(v___y_5682_);
    lean_dec_ref(v___y_5681_);
    lean_dec_ref(v_as_5677_);
    return v_res_5688_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(
    mut v_x_5689_: *mut LeanObject,
    mut v_x_5690_: *mut LeanObject,
    mut v___y_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: usize = 0;
    let mut v___x_5707_: usize = 0;
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v_vs_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5713_: u8 = 0;
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: usize = 0;
    let mut v___x_5721_: usize = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5689_) == 0 {
                    v_cs_5696_ = lean_ctor_get(v_x_5689_, 0);
                    v_isSharedCheck_5709_ = (!lean_is_exclusive(v_x_5689_)) as u8;
                    if v_isSharedCheck_5709_ == 0 {
                        v___x_5698_ = v_x_5689_;
                        v_isShared_5699_ = v_isSharedCheck_5709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_5696_);
                        lean_dec(v_x_5689_);
                        v___x_5698_ = lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5710_ = lean_ctor_get(v_x_5689_, 0);
                    v_isSharedCheck_5723_ = (!lean_is_exclusive(v_x_5689_)) as u8;
                    if v_isSharedCheck_5723_ == 0 {
                        v___x_5712_ = v_x_5689_;
                        v_isShared_5713_ = v_isSharedCheck_5723_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_5710_);
                        lean_dec(v_x_5689_);
                        v___x_5712_ = lean_box(0);
                        v_isShared_5713_ = v_isSharedCheck_5723_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5700_ = lean_array_get_size(v_cs_5696_);
                v___x_5701_ = lean_unsigned_to_nat(0);
                v___x_5702_ = lean_nat_dec_lt(v___x_5701_, v___x_5700_);
                if v___x_5702_ == 0 {
                    lean_dec_ref(v_cs_5696_);
                    if v_isShared_5699_ == 0 {
                        lean_ctor_set(v___x_5698_, 0, v_x_5690_);
                        v___x_5704_ = v___x_5698_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5705_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_x_5690_);
                        v___x_5704_ = v_reuseFailAlloc_5705_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5698_);
                    v___x_5706_ = lean_usize_of_nat(v___x_5700_);
                    v___x_5707_ = 0usize;
                    v___x_5708_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_5696_, v___x_5706_, v___x_5707_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                    lean_dec_ref(v_cs_5696_);
                    return v___x_5708_;
                }
            }
            2 => {
                return v___x_5704_;
            }
            3 => {
                v___x_5714_ = lean_array_get_size(v_vs_5710_);
                v___x_5715_ = lean_unsigned_to_nat(0);
                v___x_5716_ = lean_nat_dec_lt(v___x_5715_, v___x_5714_);
                if v___x_5716_ == 0 {
                    lean_dec_ref(v_vs_5710_);
                    if v_isShared_5713_ == 0 {
                        lean_ctor_set_tag(v___x_5712_, 0);
                        lean_ctor_set(v___x_5712_, 0, v_x_5690_);
                        v___x_5718_ = v___x_5712_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_x_5690_);
                        v___x_5718_ = v_reuseFailAlloc_5719_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5712_);
                    v___x_5720_ = lean_usize_of_nat(v___x_5714_);
                    v___x_5721_ = 0usize;
                    v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_5710_, v___x_5720_, v___x_5721_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                    lean_dec_ref(v_vs_5710_);
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
    mut v_as_5724_: *mut LeanObject,
    mut v_i_5725_: usize,
    mut v_stop_5726_: usize,
    mut v_b_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5733_: u8 = 0;
    let mut v___x_5734_: usize = 0;
    let mut v___x_5735_: usize = 0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5733_ = lean_usize_dec_eq(v_i_5725_, v_stop_5726_);
                if v___x_5733_ == 0 {
                    v___x_5734_ = 1usize;
                    v___x_5735_ = lean_usize_sub(v_i_5725_, v___x_5734_);
                    v___x_5736_ = lean_array_uget_borrowed(v_as_5724_, v___x_5735_);
                    lean_inc(v___x_5736_);
                    v___x_5737_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_5736_, v_b_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
                    if lean_obj_tag(v___x_5737_) == 0 {
                        v_a_5738_ = lean_ctor_get(v___x_5737_, 0);
                        lean_inc(v_a_5738_);
                        lean_dec_ref_known(v___x_5737_, 1);
                        v_i_5725_ = v___x_5735_;
                        v_b_5727_ = v_a_5738_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5737_;
                    }
                } else {
                    v___x_5740_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5740_, 0, v_b_5727_);
                    return v___x_5740_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_as_5741_: *mut LeanObject,
    mut v_i_5742_: *mut LeanObject,
    mut v_stop_5743_: *mut LeanObject,
    mut v_b_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5750_: usize = 0;
    let mut v_stop_boxed_5751_: usize = 0;
    let mut v_res_5752_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5750_ = lean_unbox_usize(v_i_5742_);
    lean_dec(v_i_5742_);
    v_stop_boxed_5751_ = lean_unbox_usize(v_stop_5743_);
    lean_dec(v_stop_5743_);
    v_res_5752_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_5741_, v_i_boxed_5750_, v_stop_boxed_5751_, v_b_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
    lean_dec(v___y_5748_);
    lean_dec_ref(v___y_5747_);
    lean_dec(v___y_5746_);
    lean_dec_ref(v___y_5745_);
    lean_dec_ref(v_as_5741_);
    return v_res_5752_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(
    mut v_x_5753_: *mut LeanObject,
    mut v_x_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5760_: *mut LeanObject = core::ptr::null_mut();
    v_res_5760_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_5753_, v_x_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
    lean_dec(v___y_5758_);
    lean_dec_ref(v___y_5757_);
    lean_dec(v___y_5756_);
    lean_dec_ref(v___y_5755_);
    return v_res_5760_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(
    mut v_t_5761_: *mut LeanObject,
    mut v_init_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: u8 = 0;
    v_root_5768_ = lean_ctor_get(v_t_5761_, 0);
    lean_inc_ref(v_root_5768_);
    v_tail_5769_ = lean_ctor_get(v_t_5761_, 1);
    lean_inc_ref(v_tail_5769_);
    lean_dec_ref(v_t_5761_);
    v___x_5770_ = lean_array_get_size(v_tail_5769_);
    v___x_5771_ = lean_unsigned_to_nat(0);
    v___x_5772_ = lean_nat_dec_lt(v___x_5771_, v___x_5770_);
    if v___x_5772_ == 0 {
        let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_tail_5769_);
        v___x_5773_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_5768_, v_init_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
        return v___x_5773_;
    } else {
        let mut v___x_5774_: usize = 0;
        let mut v___x_5775_: usize = 0;
        let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
        v___x_5774_ = lean_usize_of_nat(v___x_5770_);
        v___x_5775_ = 0usize;
        v___x_5776_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_5769_, v___x_5774_, v___x_5775_, v_init_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
        lean_dec_ref(v_tail_5769_);
        if lean_obj_tag(v___x_5776_) == 0 {
            let mut v_a_5777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
            v_a_5777_ = lean_ctor_get(v___x_5776_, 0);
            lean_inc(v_a_5777_);
            lean_dec_ref_known(v___x_5776_, 1);
            v___x_5778_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_5768_, v_a_5777_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
            return v___x_5778_;
        } else {
            lean_dec_ref(v_root_5768_);
            return v___x_5776_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(
    mut v_t_5779_: *mut LeanObject,
    mut v_init_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5786_: *mut LeanObject = core::ptr::null_mut();
    v_res_5786_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_5779_, v_init_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
    lean_dec(v___y_5784_);
    lean_dec_ref(v___y_5783_);
    lean_dec(v___y_5782_);
    lean_dec_ref(v___y_5781_);
    return v_res_5786_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
    mut v_lctx_5787_: *mut LeanObject,
    mut v_init_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    v_decls_5794_ = lean_ctor_get(v_lctx_5787_, 1);
    lean_inc_ref(v_decls_5794_);
    lean_dec_ref(v_lctx_5787_);
    v___x_5795_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_5794_, v_init_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_);
    return v___x_5795_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(
    mut v_lctx_5796_: *mut LeanObject,
    mut v_init_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5803_: *mut LeanObject = core::ptr::null_mut();
    v_res_5803_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
        v_lctx_5796_,
        v_init_5797_,
        v___y_5798_,
        v___y_5799_,
        v___y_5800_,
        v___y_5801_,
    );
    lean_dec(v___y_5801_);
    lean_dec_ref(v___y_5800_);
    lean_dec(v___y_5799_);
    lean_dec_ref(v___y_5798_);
    return v_res_5803_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(
    mut v_sz_5804_: usize,
    mut v_i_5805_: usize,
    mut v_bs_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5809_: u8 = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: usize = 0;
    let mut v___x_5817_: usize = 0;
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5822_: u8 = 0;
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5834_: u8 = 0;
    let mut v_unused_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5809_ = lean_usize_dec_lt(v_i_5805_, v_sz_5804_);
                if v___x_5809_ == 0 {
                    v___x_5810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5810_, 0, v_bs_5806_);
                    return v___x_5810_;
                } else {
                    v_v_5811_ = lean_array_uget(v_bs_5806_, v_i_5805_);
                    v___x_5812_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5813_ = lean_array_uset(v_bs_5806_, v_i_5805_, v___x_5812_);
                    if lean_obj_tag(v_v_5811_) == 0 {
                        v_a_5815_ = v_v_5811_;
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_5834_ = (!lean_is_exclusive(v_v_5811_)) as u8;
                        if v_isSharedCheck_5834_ == 0 {
                            v_unused_5835_ = lean_ctor_get(v_v_5811_, 0);
                            lean_dec(v_unused_5835_);
                            v___x_5821_ = v_v_5811_;
                            v_isShared_5822_ = v_isSharedCheck_5834_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_v_5811_);
                            v___x_5821_ = lean_box(0);
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
                v___x_5826_ = lean_unsigned_to_nat(1);
                v___x_5827_ = lean_nat_sub(v___x_5825_, v___x_5826_);
                v___x_5828_ = lean_array_get(v___x_5824_, v___x_5823_, v___x_5827_);
                lean_dec(v___x_5827_);
                v___x_5829_ = lean_array_pop(v___x_5823_);
                v___x_5830_ = lean_st_ref_set(v___y_5807_, v___x_5829_);
                if v_isShared_5822_ == 0 {
                    lean_ctor_set(v___x_5821_, 0, v___x_5828_);
                    v___x_5832_ = v___x_5821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5828_);
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
    mut v_sz_5836_: *mut LeanObject,
    mut v_i_5837_: *mut LeanObject,
    mut v_bs_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5841_: usize = 0;
    let mut v_i_boxed_5842_: usize = 0;
    let mut v_res_5843_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5841_ = lean_unbox_usize(v_sz_5836_);
    lean_dec(v_sz_5836_);
    v_i_boxed_5842_ = lean_unbox_usize(v_i_5837_);
    lean_dec(v_i_5837_);
    v_res_5843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_5841_, v_i_boxed_5842_, v_bs_5838_, v___y_5839_);
    lean_dec(v___y_5839_);
    return v_res_5843_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(
    mut v_x_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v_sz_5855_: usize = 0;
    let mut v___x_5856_: usize = 0;
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5861_: u8 = 0;
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5872_: u8 = 0;
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_vs_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v_sz_5882_: usize = 0;
    let mut v___x_5883_: usize = 0;
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_a_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_isSharedCheck_5904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5844_) == 0 {
                    v_cs_5851_ = lean_ctor_get(v_x_5844_, 0);
                    v_isSharedCheck_5877_ = (!lean_is_exclusive(v_x_5844_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v___x_5853_ = v_x_5844_;
                        v_isShared_5854_ = v_isSharedCheck_5877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_5851_);
                        lean_dec(v_x_5844_);
                        v___x_5853_ = lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5878_ = lean_ctor_get(v_x_5844_, 0);
                    v_isSharedCheck_5904_ = (!lean_is_exclusive(v_x_5844_)) as u8;
                    if v_isSharedCheck_5904_ == 0 {
                        v___x_5880_ = v_x_5844_;
                        v_isShared_5881_ = v_isSharedCheck_5904_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_vs_5878_);
                        lean_dec(v_x_5844_);
                        v___x_5880_ = lean_box(0);
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
                if lean_obj_tag(v___x_5857_) == 0 {
                    v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5868_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5868_ == 0 {
                        v___x_5860_ = v___x_5857_;
                        v_isShared_5861_ = v_isSharedCheck_5868_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5858_);
                        lean_dec(v___x_5857_);
                        v___x_5860_ = lean_box(0);
                        v_isShared_5861_ = v_isSharedCheck_5868_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5853_);
                    v_a_5869_ = lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5876_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5876_ == 0 {
                        v___x_5871_ = v___x_5857_;
                        v_isShared_5872_ = v_isSharedCheck_5876_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5869_);
                        lean_dec(v___x_5857_);
                        v___x_5871_ = lean_box(0);
                        v_isShared_5872_ = v_isSharedCheck_5876_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5854_ == 0 {
                    lean_ctor_set(v___x_5853_, 0, v_a_5858_);
                    v___x_5863_ = v___x_5853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5858_);
                    v___x_5863_ = v_reuseFailAlloc_5867_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5861_ == 0 {
                    lean_ctor_set(v___x_5860_, 0, v___x_5863_);
                    v___x_5865_ = v___x_5860_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5863_);
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
                    v_reuseFailAlloc_5875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
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
                if lean_obj_tag(v___x_5884_) == 0 {
                    v_a_5885_ = lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5895_ = (!lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5895_ == 0 {
                        v___x_5887_ = v___x_5884_;
                        v_isShared_5888_ = v_isSharedCheck_5895_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5885_);
                        lean_dec(v___x_5884_);
                        v___x_5887_ = lean_box(0);
                        v_isShared_5888_ = v_isSharedCheck_5895_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5880_);
                    v_a_5896_ = lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5903_ = (!lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5903_ == 0 {
                        v___x_5898_ = v___x_5884_;
                        v_isShared_5899_ = v_isSharedCheck_5903_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5896_);
                        lean_dec(v___x_5884_);
                        v___x_5898_ = lean_box(0);
                        v_isShared_5899_ = v_isSharedCheck_5903_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5881_ == 0 {
                    lean_ctor_set(v___x_5880_, 0, v_a_5885_);
                    v___x_5890_ = v___x_5880_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5885_);
                    v___x_5890_ = v_reuseFailAlloc_5894_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5888_ == 0 {
                    lean_ctor_set(v___x_5887_, 0, v___x_5890_);
                    v___x_5892_ = v___x_5887_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
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
                    v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
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
    mut v_bs_5907_: *mut LeanObject,
    mut v___y_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
    mut v___y_5911_: *mut LeanObject,
    mut v___y_5912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5914_: u8 = 0;
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: usize = 0;
    let mut v___x_5922_: usize = 0;
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5928_: u8 = 0;
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5914_ = lean_usize_dec_lt(v_i_5906_, v_sz_5905_);
                if v___x_5914_ == 0 {
                    v___x_5915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5915_, 0, v_bs_5907_);
                    return v___x_5915_;
                } else {
                    v_v_5916_ = lean_array_uget_borrowed(v_bs_5907_, v_i_5906_);
                    lean_inc(v_v_5916_);
                    v___x_5917_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_5916_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
                    if lean_obj_tag(v___x_5917_) == 0 {
                        v_a_5918_ = lean_ctor_get(v___x_5917_, 0);
                        lean_inc(v_a_5918_);
                        lean_dec_ref_known(v___x_5917_, 1);
                        v___x_5919_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5920_ = lean_array_uset(v_bs_5907_, v_i_5906_, v___x_5919_);
                        v___x_5921_ = 1usize;
                        v___x_5922_ = lean_usize_add(v_i_5906_, v___x_5921_);
                        v___x_5923_ = lean_array_uset(v_bs_x27_5920_, v_i_5906_, v_a_5918_);
                        v_i_5906_ = v___x_5922_;
                        v_bs_5907_ = v___x_5923_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5907_);
                        v_a_5925_ = lean_ctor_get(v___x_5917_, 0);
                        v_isSharedCheck_5932_ = (!lean_is_exclusive(v___x_5917_)) as u8;
                        if v_isSharedCheck_5932_ == 0 {
                            v___x_5927_ = v___x_5917_;
                            v_isShared_5928_ = v_isSharedCheck_5932_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5925_);
                            lean_dec(v___x_5917_);
                            v___x_5927_ = lean_box(0);
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
                    v_reuseFailAlloc_5931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5925_);
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
    mut v_sz_5933_: *mut LeanObject,
    mut v_i_5934_: *mut LeanObject,
    mut v_bs_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5942_: usize = 0;
    let mut v_i_boxed_5943_: usize = 0;
    let mut v_res_5944_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5942_ = lean_unbox_usize(v_sz_5933_);
    lean_dec(v_sz_5933_);
    v_i_boxed_5943_ = lean_unbox_usize(v_i_5934_);
    lean_dec(v_i_5934_);
    v_res_5944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_5942_, v_i_boxed_5943_, v_bs_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
    lean_dec(v___y_5940_);
    lean_dec_ref(v___y_5939_);
    lean_dec(v___y_5938_);
    lean_dec_ref(v___y_5937_);
    lean_dec(v___y_5936_);
    return v_res_5944_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(
    mut v_x_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
    mut v___y_5948_: *mut LeanObject,
    mut v___y_5949_: *mut LeanObject,
    mut v___y_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5952_: *mut LeanObject = core::ptr::null_mut();
    v_res_5952_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
    lean_dec(v___y_5950_);
    lean_dec_ref(v___y_5949_);
    lean_dec(v___y_5948_);
    lean_dec_ref(v___y_5947_);
    lean_dec(v___y_5946_);
    return v_res_5952_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(
    mut v_t_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
    mut v___y_5956_: *mut LeanObject,
    mut v___y_5957_: *mut LeanObject,
    mut v___y_5958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_5963_: usize = 0;
    let mut v_tailOff_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5970_: usize = 0;
    let mut v___x_5971_: usize = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5976_: u8 = 0;
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_a_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5995_: u8 = 0;
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5999_: u8 = 0;
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5960_ = lean_ctor_get(v_t_5953_, 0);
                v_tail_5961_ = lean_ctor_get(v_t_5953_, 1);
                v_size_5962_ = lean_ctor_get(v_t_5953_, 2);
                v_shift_5963_ = lean_ctor_get_usize(v_t_5953_, 4);
                v_tailOff_5964_ = lean_ctor_get(v_t_5953_, 3);
                v_isSharedCheck_6000_ = (!lean_is_exclusive(v_t_5953_)) as u8;
                if v_isSharedCheck_6000_ == 0 {
                    v___x_5966_ = v_t_5953_;
                    v_isShared_5967_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_5964_);
                    lean_inc(v_size_5962_);
                    lean_inc(v_tail_5961_);
                    lean_inc(v_root_5960_);
                    lean_dec(v_t_5953_);
                    v___x_5966_ = lean_box(0);
                    v_isShared_5967_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5968_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_5960_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_);
                if lean_obj_tag(v___x_5968_) == 0 {
                    v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
                    lean_inc(v_a_5969_);
                    lean_dec_ref_known(v___x_5968_, 1);
                    v_sz_5970_ = lean_array_size(v_tail_5961_);
                    v___x_5971_ = 0usize;
                    v___x_5972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_5970_, v___x_5971_, v_tail_5961_, v___y_5954_);
                    if lean_obj_tag(v___x_5972_) == 0 {
                        v_a_5973_ = lean_ctor_get(v___x_5972_, 0);
                        v_isSharedCheck_5983_ = (!lean_is_exclusive(v___x_5972_)) as u8;
                        if v_isSharedCheck_5983_ == 0 {
                            v___x_5975_ = v___x_5972_;
                            v_isShared_5976_ = v_isSharedCheck_5983_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5973_);
                            lean_dec(v___x_5972_);
                            v___x_5975_ = lean_box(0);
                            v_isShared_5976_ = v_isSharedCheck_5983_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5969_);
                        lean_del_object(v___x_5966_);
                        lean_dec(v_tailOff_5964_);
                        lean_dec(v_size_5962_);
                        v_a_5984_ = lean_ctor_get(v___x_5972_, 0);
                        v_isSharedCheck_5991_ = (!lean_is_exclusive(v___x_5972_)) as u8;
                        if v_isSharedCheck_5991_ == 0 {
                            v___x_5986_ = v___x_5972_;
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5984_);
                            lean_dec(v___x_5972_);
                            v___x_5986_ = lean_box(0);
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5966_);
                    lean_dec(v_tailOff_5964_);
                    lean_dec(v_size_5962_);
                    lean_dec_ref(v_tail_5961_);
                    v_a_5992_ = lean_ctor_get(v___x_5968_, 0);
                    v_isSharedCheck_5999_ = (!lean_is_exclusive(v___x_5968_)) as u8;
                    if v_isSharedCheck_5999_ == 0 {
                        v___x_5994_ = v___x_5968_;
                        v_isShared_5995_ = v_isSharedCheck_5999_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5992_);
                        lean_dec(v___x_5968_);
                        v___x_5994_ = lean_box(0);
                        v_isShared_5995_ = v_isSharedCheck_5999_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5967_ == 0 {
                    lean_ctor_set(v___x_5966_, 1, v_a_5973_);
                    lean_ctor_set(v___x_5966_, 0, v_a_5969_);
                    v___x_5978_ = v___x_5966_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5982_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5969_);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 1, v_a_5973_);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_size_5962_);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 3, v_tailOff_5964_);
                    lean_ctor_set_usize(v_reuseFailAlloc_5982_, 4, v_shift_5963_);
                    v___x_5978_ = v_reuseFailAlloc_5982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5976_ == 0 {
                    lean_ctor_set(v___x_5975_, 0, v___x_5978_);
                    v___x_5980_ = v___x_5975_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5978_);
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
                    v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
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
                    v_reuseFailAlloc_5998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
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
    mut v_t_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
    mut v___y_6005_: *mut LeanObject,
    mut v___y_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6008_: *mut LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(
        v_t_6001_,
        v___y_6002_,
        v___y_6003_,
        v___y_6004_,
        v___y_6005_,
        v___y_6006_,
    );
    lean_dec(v___y_6006_);
    lean_dec_ref(v___y_6005_);
    lean_dec(v___y_6004_);
    lean_dec_ref(v___y_6003_);
    lean_dec(v___y_6002_);
    return v_res_6008_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_countUsesLCtx(
    mut v_ctx_6009_: *mut LeanObject,
    mut v_targetUses_6010_: *mut LeanObject,
    mut v_a_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
    mut v_a_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6030_: u8 = 0;
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_a_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v_a_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6048_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_6016_ = lean_ctor_get(v_ctx_6009_, 1);
                lean_inc_ref(v_decls_6016_);
                v_fvarIdToDecl_6017_ = lean_ctor_get(v_ctx_6009_, 0);
                lean_inc_ref(v_fvarIdToDecl_6017_);
                v_auxDeclToFullName_6018_ = lean_ctor_get(v_ctx_6009_, 2);
                lean_inc(v_auxDeclToFullName_6018_);
                v_size_6019_ = lean_ctor_get(v_decls_6016_, 2);
                v_decls_6020_ = lean_mk_empty_array_with_capacity(v_size_6019_);
                v___x_6021_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6021_, 0, v_decls_6020_);
                lean_ctor_set(v___x_6021_, 1, v_targetUses_6010_);
                v___x_6022_ =
                    l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(
                        v_ctx_6009_,
                        v___x_6021_,
                        v_a_6011_,
                        v_a_6012_,
                        v_a_6013_,
                        v_a_6014_,
                    );
                if lean_obj_tag(v___x_6022_) == 0 {
                    v_a_6023_ = lean_ctor_get(v___x_6022_, 0);
                    lean_inc(v_a_6023_);
                    lean_dec_ref_known(v___x_6022_, 1);
                    v_fst_6024_ = lean_ctor_get(v_a_6023_, 0);
                    lean_inc(v_fst_6024_);
                    lean_dec(v_a_6023_);
                    v___x_6025_ = lean_st_mk_ref(v_fst_6024_);
                    v___x_6026_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_6016_, v___x_6025_, v_a_6011_, v_a_6012_, v_a_6013_, v_a_6014_);
                    if lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = lean_ctor_get(v___x_6026_, 0);
                        v_isSharedCheck_6036_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6036_ == 0 {
                            v___x_6029_ = v___x_6026_;
                            v_isShared_6030_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6027_);
                            lean_dec(v___x_6026_);
                            v___x_6029_ = lean_box(0);
                            v_isShared_6030_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6025_);
                        lean_dec(v_auxDeclToFullName_6018_);
                        lean_dec_ref(v_fvarIdToDecl_6017_);
                        v_a_6037_ = lean_ctor_get(v___x_6026_, 0);
                        v_isSharedCheck_6044_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6039_ = v___x_6026_;
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6037_);
                            lean_dec(v___x_6026_);
                            v___x_6039_ = lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_auxDeclToFullName_6018_);
                    lean_dec_ref(v_fvarIdToDecl_6017_);
                    lean_dec_ref(v_decls_6016_);
                    v_a_6045_ = lean_ctor_get(v___x_6022_, 0);
                    v_isSharedCheck_6052_ = (!lean_is_exclusive(v___x_6022_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v___x_6047_ = v___x_6022_;
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6045_);
                        lean_dec(v___x_6022_);
                        v___x_6047_ = lean_box(0);
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6031_ = lean_st_ref_get(v___x_6025_);
                lean_dec(v___x_6025_);
                lean_dec(v___x_6031_);
                v___x_6032_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6032_, 0, v_fvarIdToDecl_6017_);
                lean_ctor_set(v___x_6032_, 1, v_a_6027_);
                lean_ctor_set(v___x_6032_, 2, v_auxDeclToFullName_6018_);
                if v_isShared_6030_ == 0 {
                    lean_ctor_set(v___x_6029_, 0, v___x_6032_);
                    v___x_6034_ = v___x_6029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6032_);
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
                    v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
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
                    v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
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
    mut v_ctx_6053_: *mut LeanObject,
    mut v_targetUses_6054_: *mut LeanObject,
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
    mut v_a_6057_: *mut LeanObject,
    mut v_a_6058_: *mut LeanObject,
    mut v_a_6059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6060_: *mut LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(
        v_ctx_6053_,
        v_targetUses_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
    );
    lean_dec(v_a_6058_);
    lean_dec_ref(v_a_6057_);
    lean_dec(v_a_6056_);
    lean_dec_ref(v_a_6055_);
    return v_res_6060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(
    mut v_sz_6061_: usize,
    mut v_i_6062_: usize,
    mut v_bs_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_6061_, v_i_6062_, v_bs_6063_, v___y_6064_);
    return v___x_6070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(
    mut v_sz_6071_: *mut LeanObject,
    mut v_i_6072_: *mut LeanObject,
    mut v_bs_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6080_: usize = 0;
    let mut v_i_boxed_6081_: usize = 0;
    let mut v_res_6082_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6080_ = lean_unbox_usize(v_sz_6071_);
    lean_dec(v_sz_6071_);
    v_i_boxed_6081_ = lean_unbox_usize(v_i_6072_);
    lean_dec(v_i_6072_);
    v_res_6082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_6080_, v_i_boxed_6081_, v_bs_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
    lean_dec(v___y_6078_);
    lean_dec_ref(v___y_6077_);
    lean_dec(v___y_6076_);
    lean_dec_ref(v___y_6075_);
    lean_dec(v___y_6074_);
    return v_res_6082_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_doNotDup(
    mut v_u_6083_: u8,
    mut v_rhs_6084_: *mut LeanObject,
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
    mut v_u_6090_: *mut LeanObject,
    mut v_rhs_6091_: *mut LeanObject,
    mut v_elimTrivial_6092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_boxed_6093_: u8 = 0;
    let mut v_elimTrivial_boxed_6094_: u8 = 0;
    let mut v_res_6095_: u8 = 0;
    let mut v_r_6096_: *mut LeanObject = core::ptr::null_mut();
    v_u_boxed_6093_ = (lean_unbox(v_u_6090_) as u8);
    v_elimTrivial_boxed_6094_ = (lean_unbox(v_elimTrivial_6092_) as u8);
    v_res_6095_ =
        l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_6093_, v_rhs_6091_, v_elimTrivial_boxed_6094_);
    lean_dec_ref(v_rhs_6091_);
    v_r_6096_ = lean_box((v_res_6095_) as usize);
    return v_r_6096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(
    mut v_elimTrivial_6099_: u8,
    mut v_e_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
    mut v___y_6104_: *mut LeanObject,
    mut v___y_6105_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_6100_) == 8 {
        let mut v_type_6107_: *mut LeanObject = core::ptr::null_mut();
        v_type_6107_ = lean_ctor_get(v_e_6100_, 1);
        if lean_obj_tag(v_type_6107_) == 10 {
            let mut v_value_6108_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_6109_: *mut LeanObject = core::ptr::null_mut();
            let mut v_data_6110_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
            let mut v_uses_6114_: u8 = 0;
            let mut v___x_6115_: u8 = 0;
            v_value_6108_ = lean_ctor_get(v_e_6100_, 2);
            v_body_6109_ = lean_ctor_get(v_e_6100_, 3);
            v_data_6110_ = lean_ctor_get(v_type_6107_, 0);
            v___x_6111_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
            v___x_6112_ = lean_unsigned_to_nat(2);
            v___x_6113_ = l_Lean_KVMap_getNat(v_data_6110_, v___x_6111_, v___x_6112_);
            v_uses_6114_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_6113_);
            lean_dec(v___x_6113_);
            v___x_6115_ =
                l_Lean_Elab_Tactic_Do_doNotDup(v_uses_6114_, v_value_6108_, v_elimTrivial_6099_);
            if v___x_6115_ == 0 {
                let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
                v___x_6116_ = lean_expr_instantiate1(v_body_6109_, v_value_6108_);
                v___x_6117_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6117_, 0, v___x_6116_);
                v___x_6118_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6118_, 0, v___x_6117_);
                return v___x_6118_;
            } else {
                let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
                v___x_6119_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
                v___x_6120_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6120_, 0, v___x_6119_);
                return v___x_6120_;
            }
        } else {
            let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
            v___x_6121_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
            v___x_6122_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6122_, 0, v___x_6121_);
            return v___x_6122_;
        }
    } else {
        let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
        v___x_6123_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0;
        v___x_6124_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6124_, 0, v___x_6123_);
        return v___x_6124_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(
    mut v_elimTrivial_6125_: *mut LeanObject,
    mut v_e_6126_: *mut LeanObject,
    mut v___y_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
    mut v___y_6132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_6133_: u8 = 0;
    let mut v_res_6134_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_6133_ = (lean_unbox(v_elimTrivial_6125_) as u8);
    v_res_6134_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(
        v_elimTrivial_boxed_6133_,
        v_e_6126_,
        v___y_6127_,
        v___y_6128_,
        v___y_6129_,
        v___y_6130_,
        v___y_6131_,
    );
    lean_dec(v___y_6131_);
    lean_dec_ref(v___y_6130_);
    lean_dec(v___y_6129_);
    lean_dec_ref(v___y_6128_);
    lean_dec(v___y_6127_);
    lean_dec_ref(v_e_6126_);
    return v_res_6134_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(
    mut v_e_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
    mut v___y_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    v___x_6142_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6142_, 0, v_e_6135_);
    v___x_6143_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6143_, 0, v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(
    mut v_e_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6151_: *mut LeanObject = core::ptr::null_mut();
    v_res_6151_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(
        v_e_6144_,
        v___y_6145_,
        v___y_6146_,
        v___y_6147_,
        v___y_6148_,
        v___y_6149_,
    );
    lean_dec(v___y_6149_);
    lean_dec_ref(v___y_6148_);
    lean_dec(v___y_6147_);
    lean_dec_ref(v___y_6146_);
    lean_dec(v___y_6145_);
    return v_res_6151_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    v___x_6157_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6158_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6158_, 0, v___x_6157_);
    return v___x_6158_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    v___x_6159_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
    v___x_6160_ = l_Lean_MessageData_ofFormat(v___x_6159_);
    return v___x_6160_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    v___x_6161_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
    v___x_6162_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2;
    v___x_6163_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_6163_, 0, v___x_6162_);
    lean_ctor_set(v___x_6163_, 1, v___x_6161_);
    return v___x_6163_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(
    mut v_ref_6164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    v___x_6166_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
    v___x_6167_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6167_, 0, v_ref_6164_);
    lean_ctor_set(v___x_6167_, 1, v___x_6166_);
    v___x_6168_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6168_, 0, v___x_6167_);
    return v___x_6168_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(
    mut v_ref_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6171_: *mut LeanObject = core::ptr::null_mut();
    v_res_6171_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_6169_);
    return v_res_6171_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(
    mut v_x_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut v_fileName_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6202_: u8 = 0;
    let mut v_cancelTk_x3f_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6204_: u8 = 0;
    let mut v_inheritedTraceOptions_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: u8 = 0;
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6190_ = lean_ctor_get(v___y_6177_, 0);
                v_fileMap_6191_ = lean_ctor_get(v___y_6177_, 1);
                v_options_6192_ = lean_ctor_get(v___y_6177_, 2);
                v_currRecDepth_6193_ = lean_ctor_get(v___y_6177_, 3);
                v_maxRecDepth_6194_ = lean_ctor_get(v___y_6177_, 4);
                v_ref_6195_ = lean_ctor_get(v___y_6177_, 5);
                v_currNamespace_6196_ = lean_ctor_get(v___y_6177_, 6);
                v_openDecls_6197_ = lean_ctor_get(v___y_6177_, 7);
                v_initHeartbeats_6198_ = lean_ctor_get(v___y_6177_, 8);
                v_maxHeartbeats_6199_ = lean_ctor_get(v___y_6177_, 9);
                v_quotContext_6200_ = lean_ctor_get(v___y_6177_, 10);
                v_currMacroScope_6201_ = lean_ctor_get(v___y_6177_, 11);
                v_diag_6202_ = lean_ctor_get_uint8(
                    v___y_6177_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6203_ = lean_ctor_get(v___y_6177_, 12);
                v_suppressElabErrors_6204_ = lean_ctor_get_uint8(
                    v___y_6177_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6205_ = lean_ctor_get(v___y_6177_, 13);
                v___x_6211_ = lean_unsigned_to_nat(0);
                v___x_6212_ = lean_nat_dec_eq(v_maxRecDepth_6194_, v___x_6211_);
                if v___x_6212_ == 0 {
                    v___x_6213_ = lean_nat_dec_eq(v_currRecDepth_6193_, v_maxRecDepth_6194_);
                    if v___x_6213_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        lean_dec_ref(v_x_6172_);
                        lean_inc(v_ref_6195_);
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
                if lean_obj_tag(v___y_6181_) == 0 {
                    return v___y_6181_;
                } else {
                    v_a_6182_ = lean_ctor_get(v___y_6181_, 0);
                    v_isSharedCheck_6189_ = (!lean_is_exclusive(v___y_6181_)) as u8;
                    if v_isSharedCheck_6189_ == 0 {
                        v___x_6184_ = v___y_6181_;
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6182_);
                        lean_dec(v___y_6181_);
                        v___x_6184_ = lean_box(0);
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
                    v_reuseFailAlloc_6188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
                    v___x_6187_ = v_reuseFailAlloc_6188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6187_;
            }
            4 => {
                v___x_6207_ = lean_unsigned_to_nat(1);
                v___x_6208_ = lean_nat_add(v_currRecDepth_6193_, v___x_6207_);
                lean_inc_ref(v_inheritedTraceOptions_6205_);
                lean_inc(v_cancelTk_x3f_6203_);
                lean_inc(v_currMacroScope_6201_);
                lean_inc(v_quotContext_6200_);
                lean_inc(v_maxHeartbeats_6199_);
                lean_inc(v_initHeartbeats_6198_);
                lean_inc(v_openDecls_6197_);
                lean_inc(v_currNamespace_6196_);
                lean_inc(v_ref_6195_);
                lean_inc(v_maxRecDepth_6194_);
                lean_inc_ref(v_options_6192_);
                lean_inc_ref(v_fileMap_6191_);
                lean_inc_ref(v_fileName_6190_);
                v___x_6209_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6209_, 0, v_fileName_6190_);
                lean_ctor_set(v___x_6209_, 1, v_fileMap_6191_);
                lean_ctor_set(v___x_6209_, 2, v_options_6192_);
                lean_ctor_set(v___x_6209_, 3, v___x_6208_);
                lean_ctor_set(v___x_6209_, 4, v_maxRecDepth_6194_);
                lean_ctor_set(v___x_6209_, 5, v_ref_6195_);
                lean_ctor_set(v___x_6209_, 6, v_currNamespace_6196_);
                lean_ctor_set(v___x_6209_, 7, v_openDecls_6197_);
                lean_ctor_set(v___x_6209_, 8, v_initHeartbeats_6198_);
                lean_ctor_set(v___x_6209_, 9, v_maxHeartbeats_6199_);
                lean_ctor_set(v___x_6209_, 10, v_quotContext_6200_);
                lean_ctor_set(v___x_6209_, 11, v_currMacroScope_6201_);
                lean_ctor_set(v___x_6209_, 12, v_cancelTk_x3f_6203_);
                lean_ctor_set(v___x_6209_, 13, v_inheritedTraceOptions_6205_);
                lean_ctor_set_uint8(
                    v___x_6209_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_6202_,
                );
                lean_ctor_set_uint8(
                    v___x_6209_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6204_,
                );
                lean_inc(v___y_6178_);
                lean_inc(v___y_6176_);
                lean_inc_ref(v___y_6175_);
                lean_inc(v___y_6174_);
                lean_inc(v___y_6173_);
                v___x_6210_ = lean_apply_7(
                    v_x_6172_,
                    v___y_6173_,
                    v___y_6174_,
                    v___y_6175_,
                    v___y_6176_,
                    v___x_6209_,
                    v___y_6178_,
                    lean_box(0),
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
    mut v_x_6215_: *mut LeanObject,
    mut v___y_6216_: *mut LeanObject,
    mut v___y_6217_: *mut LeanObject,
    mut v___y_6218_: *mut LeanObject,
    mut v___y_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
    mut v___y_6221_: *mut LeanObject,
    mut v___y_6222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6223_: *mut LeanObject = core::ptr::null_mut();
    v_res_6223_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_);
    lean_dec(v___y_6221_);
    lean_dec_ref(v___y_6220_);
    lean_dec(v___y_6219_);
    lean_dec_ref(v___y_6218_);
    lean_dec(v___y_6217_);
    lean_dec(v___y_6216_);
    return v_res_6223_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(
    mut v_a_6224_: *mut LeanObject,
    mut v_x_6225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: u8 = 0;
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6225_) == 0 {
                    v___x_6226_ = lean_box(0);
                    return v___x_6226_;
                } else {
                    v_key_6227_ = lean_ctor_get(v_x_6225_, 0);
                    v_value_6228_ = lean_ctor_get(v_x_6225_, 1);
                    v_tail_6229_ = lean_ctor_get(v_x_6225_, 2);
                    v___x_6230_ = l_Lean_ExprStructEq_beq(v_key_6227_, v_a_6224_);
                    if v___x_6230_ == 0 {
                        v_x_6225_ = v_tail_6229_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_6228_);
                        v___x_6232_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6232_, 0, v_value_6228_);
                        return v___x_6232_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(
    mut v_a_6233_: *mut LeanObject,
    mut v_x_6234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6235_: *mut LeanObject = core::ptr::null_mut();
    v_res_6235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_6233_, v_x_6234_);
    lean_dec(v_x_6234_);
    lean_dec_ref(v_a_6233_);
    return v_res_6235_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(
    mut v_m_6236_: *mut LeanObject,
    mut v_a_6237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_6238_ = lean_ctor_get(v_m_6236_, 1);
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
    mut v_m_6254_: *mut LeanObject,
    mut v_a_6255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6256_: *mut LeanObject = core::ptr::null_mut();
    v_res_6256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_6254_, v_a_6255_);
    lean_dec_ref(v_a_6255_);
    lean_dec_ref(v_m_6254_);
    return v_res_6256_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(
    mut v_k_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v_b_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_6264_);
    lean_inc_ref(v___y_6263_);
    lean_inc(v___y_6262_);
    lean_inc_ref(v___y_6261_);
    lean_inc(v___y_6259_);
    lean_inc(v___y_6258_);
    v___x_6266_ = lean_apply_8(
        v_k_6257_,
        v_b_6260_,
        v___y_6258_,
        v___y_6259_,
        v___y_6261_,
        v___y_6262_,
        v___y_6263_,
        v___y_6264_,
        lean_box(0),
    );
    return v___x_6266_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(
    mut v_k_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v_b_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
    mut v___y_6272_: *mut LeanObject,
    mut v___y_6273_: *mut LeanObject,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6276_: *mut LeanObject = core::ptr::null_mut();
    v_res_6276_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_6267_, v___y_6268_, v___y_6269_, v_b_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
    lean_dec(v___y_6274_);
    lean_dec_ref(v___y_6273_);
    lean_dec(v___y_6272_);
    lean_dec_ref(v___y_6271_);
    lean_dec(v___y_6269_);
    lean_dec(v___y_6268_);
    return v_res_6276_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(
    mut v_name_6277_: *mut LeanObject,
    mut v_type_6278_: *mut LeanObject,
    mut v_val_6279_: *mut LeanObject,
    mut v_k_6280_: *mut LeanObject,
    mut v_nondep_6281_: u8,
    mut v_kind_6282_: u8,
    mut v___y_6283_: *mut LeanObject,
    mut v___y_6284_: *mut LeanObject,
    mut v___y_6285_: *mut LeanObject,
    mut v___y_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6284_);
                lean_inc(v___y_6283_);
                v___f_6290_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_6290_, 0, v_k_6280_);
                lean_closure_set(v___f_6290_, 1, v___y_6283_);
                lean_closure_set(v___f_6290_, 2, v___y_6284_);
                v___x_6291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_6291_) == 0 {
                    return v___x_6291_;
                } else {
                    v_a_6292_ = lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6299_ = (!lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6299_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6292_);
                        lean_dec(v___x_6291_);
                        v___x_6294_ = lean_box(0);
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
                    v_reuseFailAlloc_6298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6292_);
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
    mut v_name_6300_: *mut LeanObject,
    mut v_type_6301_: *mut LeanObject,
    mut v_val_6302_: *mut LeanObject,
    mut v_k_6303_: *mut LeanObject,
    mut v_nondep_6304_: *mut LeanObject,
    mut v_kind_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
    mut v___y_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
    mut v___y_6309_: *mut LeanObject,
    mut v___y_6310_: *mut LeanObject,
    mut v___y_6311_: *mut LeanObject,
    mut v___y_6312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_6313_: u8 = 0;
    let mut v_kind_boxed_6314_: u8 = 0;
    let mut v_res_6315_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6313_ = (lean_unbox(v_nondep_6304_) as u8);
    v_kind_boxed_6314_ = (lean_unbox(v_kind_6305_) as u8);
    v_res_6315_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_6300_, v_type_6301_, v_val_6302_, v_k_6303_, v_nondep_boxed_6313_, v_kind_boxed_6314_, v___y_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_, v___y_6311_);
    lean_dec(v___y_6311_);
    lean_dec_ref(v___y_6310_);
    lean_dec(v___y_6309_);
    lean_dec_ref(v___y_6308_);
    lean_dec(v___y_6307_);
    lean_dec(v___y_6306_);
    return v_res_6315_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_name_6316_: *mut LeanObject,
    mut v_bi_6317_: u8,
    mut v_type_6318_: *mut LeanObject,
    mut v_k_6319_: *mut LeanObject,
    mut v_kind_6320_: u8,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
    mut v___y_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
    mut v___y_6325_: *mut LeanObject,
    mut v___y_6326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6322_);
                lean_inc(v___y_6321_);
                v___f_6328_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_6328_, 0, v_k_6319_);
                lean_closure_set(v___f_6328_, 1, v___y_6321_);
                lean_closure_set(v___f_6328_, 2, v___y_6322_);
                v___x_6329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_6329_) == 0 {
                    return v___x_6329_;
                } else {
                    v_a_6330_ = lean_ctor_get(v___x_6329_, 0);
                    v_isSharedCheck_6337_ = (!lean_is_exclusive(v___x_6329_)) as u8;
                    if v_isSharedCheck_6337_ == 0 {
                        v___x_6332_ = v___x_6329_;
                        v_isShared_6333_ = v_isSharedCheck_6337_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6330_);
                        lean_dec(v___x_6329_);
                        v___x_6332_ = lean_box(0);
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
                    v_reuseFailAlloc_6336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_a_6330_);
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
    mut v_name_6338_: *mut LeanObject,
    mut v_bi_6339_: *mut LeanObject,
    mut v_type_6340_: *mut LeanObject,
    mut v_k_6341_: *mut LeanObject,
    mut v_kind_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
    mut v___y_6344_: *mut LeanObject,
    mut v___y_6345_: *mut LeanObject,
    mut v___y_6346_: *mut LeanObject,
    mut v___y_6347_: *mut LeanObject,
    mut v___y_6348_: *mut LeanObject,
    mut v___y_6349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_6350_: u8 = 0;
    let mut v_kind_boxed_6351_: u8 = 0;
    let mut v_res_6352_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_6350_ = (lean_unbox(v_bi_6339_) as u8);
    v_kind_boxed_6351_ = (lean_unbox(v_kind_6342_) as u8);
    v_res_6352_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_6338_, v_bi_boxed_6350_, v_type_6340_, v_k_6341_, v_kind_boxed_6351_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
    lean_dec(v___y_6348_);
    lean_dec_ref(v___y_6347_);
    lean_dec(v___y_6346_);
    lean_dec_ref(v___y_6345_);
    lean_dec(v___y_6344_);
    lean_dec(v___y_6343_);
    return v_res_6352_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(
    mut v___x_6353_: *mut LeanObject,
    mut v___y_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
    mut v___y_6356_: *mut LeanObject,
    mut v___y_6357_: *mut LeanObject,
    mut v___y_6358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    v___x_6360_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6360_, 0, v___x_6353_);
    return v___x_6360_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(
    mut v___x_6361_: *mut LeanObject,
    mut v___y_6362_: *mut LeanObject,
    mut v___y_6363_: *mut LeanObject,
    mut v___y_6364_: *mut LeanObject,
    mut v___y_6365_: *mut LeanObject,
    mut v___y_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6368_: *mut LeanObject = core::ptr::null_mut();
    v_res_6368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_);
    lean_dec(v___y_6366_);
    lean_dec_ref(v___y_6365_);
    lean_dec(v___y_6364_);
    lean_dec_ref(v___y_6363_);
    lean_dec(v___y_6362_);
    return v_res_6368_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(
    mut v_00_u03b1_6369_: *mut LeanObject,
    mut v_x_6370_: *mut LeanObject,
    mut v___y_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
    mut v___y_6375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    v___x_6377_ = lean_apply_1(v_x_6370_, lean_box(0));
    v___x_6378_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6378_, 0, v___x_6377_);
    return v___x_6378_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_6379_: *mut LeanObject,
    mut v_x_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
    mut v___y_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
    mut v___y_6385_: *mut LeanObject,
    mut v___y_6386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6387_: *mut LeanObject = core::ptr::null_mut();
    v_res_6387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_6379_, v_x_6380_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_, v___y_6385_);
    lean_dec(v___y_6385_);
    lean_dec_ref(v___y_6384_);
    lean_dec(v___y_6383_);
    lean_dec_ref(v___y_6382_);
    lean_dec(v___y_6381_);
    return v_res_6387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(
    mut v_x_6388_: *mut LeanObject,
    mut v_x_6389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6389_) == 0 {
                    return v_x_6388_;
                } else {
                    v_key_6390_ = lean_ctor_get(v_x_6389_, 0);
                    v_value_6391_ = lean_ctor_get(v_x_6389_, 1);
                    v_tail_6392_ = lean_ctor_get(v_x_6389_, 2);
                    v_isSharedCheck_6415_ = (!lean_is_exclusive(v_x_6389_)) as u8;
                    if v_isSharedCheck_6415_ == 0 {
                        v___x_6394_ = v_x_6389_;
                        v_isShared_6395_ = v_isSharedCheck_6415_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6392_);
                        lean_inc(v_value_6391_);
                        lean_inc(v_key_6390_);
                        lean_dec(v_x_6389_);
                        v___x_6394_ = lean_box(0);
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
                lean_inc(v___x_6409_);
                if v_isShared_6395_ == 0 {
                    lean_ctor_set(v___x_6394_, 2, v___x_6409_);
                    v___x_6411_ = v___x_6394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6414_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_key_6390_);
                    lean_ctor_set(v_reuseFailAlloc_6414_, 1, v_value_6391_);
                    lean_ctor_set(v_reuseFailAlloc_6414_, 2, v___x_6409_);
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
    mut v_i_6416_: *mut LeanObject,
    mut v_source_6417_: *mut LeanObject,
    mut v_target_6418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v_es_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6419_ = lean_array_get_size(v_source_6417_);
                v___x_6420_ = lean_nat_dec_lt(v_i_6416_, v___x_6419_);
                if v___x_6420_ == 0 {
                    lean_dec_ref(v_source_6417_);
                    lean_dec(v_i_6416_);
                    return v_target_6418_;
                } else {
                    v_es_6421_ = lean_array_fget(v_source_6417_, v_i_6416_);
                    v___x_6422_ = lean_box(0);
                    v_source_6423_ = lean_array_fset(v_source_6417_, v_i_6416_, v___x_6422_);
                    v_target_6424_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_6418_, v_es_6421_);
                    v___x_6425_ = lean_unsigned_to_nat(1);
                    v___x_6426_ = lean_nat_add(v_i_6416_, v___x_6425_);
                    lean_dec(v_i_6416_);
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
    mut v_data_6428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    v___x_6429_ = lean_array_get_size(v_data_6428_);
    v___x_6430_ = lean_unsigned_to_nat(2);
    v_nbuckets_6431_ = lean_nat_mul(v___x_6429_, v___x_6430_);
    v___x_6432_ = lean_unsigned_to_nat(0);
    v___x_6433_ = lean_box(0);
    v___x_6434_ = lean_mk_array(v_nbuckets_6431_, v___x_6433_);
    v___x_6435_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_6432_, v_data_6428_, v___x_6434_);
    return v___x_6435_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(
    mut v_a_6436_: *mut LeanObject,
    mut v_b_6437_: *mut LeanObject,
    mut v_x_6438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6445_: u8 = 0;
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6438_) == 0 {
                    lean_dec(v_b_6437_);
                    lean_dec_ref(v_a_6436_);
                    return v_x_6438_;
                } else {
                    v_key_6439_ = lean_ctor_get(v_x_6438_, 0);
                    v_value_6440_ = lean_ctor_get(v_x_6438_, 1);
                    v_tail_6441_ = lean_ctor_get(v_x_6438_, 2);
                    v_isSharedCheck_6453_ = (!lean_is_exclusive(v_x_6438_)) as u8;
                    if v_isSharedCheck_6453_ == 0 {
                        v___x_6443_ = v_x_6438_;
                        v_isShared_6444_ = v_isSharedCheck_6453_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6441_);
                        lean_inc(v_value_6440_);
                        lean_inc(v_key_6439_);
                        lean_dec(v_x_6438_);
                        v___x_6443_ = lean_box(0);
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
                        lean_ctor_set(v___x_6443_, 2, v___x_6446_);
                        v___x_6448_ = v___x_6443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6449_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_key_6439_);
                        lean_ctor_set(v_reuseFailAlloc_6449_, 1, v_value_6440_);
                        lean_ctor_set(v_reuseFailAlloc_6449_, 2, v___x_6446_);
                        v___x_6448_ = v_reuseFailAlloc_6449_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_6440_);
                    lean_dec(v_key_6439_);
                    if v_isShared_6444_ == 0 {
                        lean_ctor_set(v___x_6443_, 1, v_b_6437_);
                        lean_ctor_set(v___x_6443_, 0, v_a_6436_);
                        v___x_6451_ = v___x_6443_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6452_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_a_6436_);
                        lean_ctor_set(v_reuseFailAlloc_6452_, 1, v_b_6437_);
                        lean_ctor_set(v_reuseFailAlloc_6452_, 2, v_tail_6441_);
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
    mut v_a_6454_: *mut LeanObject,
    mut v_x_6455_: *mut LeanObject,
) -> u8 {
    let mut v___x_6456_: u8 = 0;
    let mut v_key_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6455_) == 0 {
                    v___x_6456_ = 0;
                    return v___x_6456_;
                } else {
                    v_key_6457_ = lean_ctor_get(v_x_6455_, 0);
                    v_tail_6458_ = lean_ctor_get(v_x_6455_, 2);
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
    mut v_a_6461_: *mut LeanObject,
    mut v_x_6462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6463_: u8 = 0;
    let mut v_r_6464_: *mut LeanObject = core::ptr::null_mut();
    v_res_6463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_6461_, v_x_6462_);
    lean_dec(v_x_6462_);
    lean_dec_ref(v_a_6461_);
    v_r_6464_ = lean_box((v_res_6463_) as usize);
    return v_r_6464_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(
    mut v_m_6465_: *mut LeanObject,
    mut v_a_6466_: *mut LeanObject,
    mut v_b_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6472_: u8 = 0;
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: u8 = 0;
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: u8 = 0;
    let mut v_val_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6468_ = lean_ctor_get(v_m_6465_, 0);
                v_buckets_6469_ = lean_ctor_get(v_m_6465_, 1);
                v_isSharedCheck_6512_ = (!lean_is_exclusive(v_m_6465_)) as u8;
                if v_isSharedCheck_6512_ == 0 {
                    v___x_6471_ = v_m_6465_;
                    v_isShared_6472_ = v_isSharedCheck_6512_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_6469_);
                    lean_inc(v_size_6468_);
                    lean_dec(v_m_6465_);
                    v___x_6471_ = lean_box(0);
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
                    v___x_6488_ = lean_unsigned_to_nat(1);
                    v_size_x27_6489_ = lean_nat_add(v_size_6468_, v___x_6488_);
                    lean_dec(v_size_6468_);
                    lean_inc(v_bkt_6486_);
                    v___x_6490_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6490_, 0, v_a_6466_);
                    lean_ctor_set(v___x_6490_, 1, v_b_6467_);
                    lean_ctor_set(v___x_6490_, 2, v_bkt_6486_);
                    v_buckets_x27_6491_ =
                        lean_array_uset(v_buckets_6469_, v___x_6485_, v___x_6490_);
                    v___x_6492_ = lean_unsigned_to_nat(4);
                    v___x_6493_ = lean_nat_mul(v_size_x27_6489_, v___x_6492_);
                    v___x_6494_ = lean_unsigned_to_nat(3);
                    v___x_6495_ = lean_nat_div(v___x_6493_, v___x_6494_);
                    lean_dec(v___x_6493_);
                    v___x_6496_ = lean_array_get_size(v_buckets_x27_6491_);
                    v___x_6497_ = lean_nat_dec_le(v___x_6495_, v___x_6496_);
                    lean_dec(v___x_6495_);
                    if v___x_6497_ == 0 {
                        v_val_6498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_6491_);
                        if v_isShared_6472_ == 0 {
                            lean_ctor_set(v___x_6471_, 1, v_val_6498_);
                            lean_ctor_set(v___x_6471_, 0, v_size_x27_6489_);
                            v___x_6500_ = v___x_6471_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6501_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6501_, 0, v_size_x27_6489_);
                            lean_ctor_set(v_reuseFailAlloc_6501_, 1, v_val_6498_);
                            v___x_6500_ = v_reuseFailAlloc_6501_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6472_ == 0 {
                            lean_ctor_set(v___x_6471_, 1, v_buckets_x27_6491_);
                            lean_ctor_set(v___x_6471_, 0, v_size_x27_6489_);
                            v___x_6503_ = v___x_6471_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6504_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_size_x27_6489_);
                            lean_ctor_set(v_reuseFailAlloc_6504_, 1, v_buckets_x27_6491_);
                            v___x_6503_ = v_reuseFailAlloc_6504_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_6486_);
                    v___x_6505_ = lean_box(0);
                    v_buckets_x27_6506_ =
                        lean_array_uset(v_buckets_6469_, v___x_6485_, v___x_6505_);
                    v___x_6507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_6466_, v_b_6467_, v_bkt_6486_);
                    v___x_6508_ = lean_array_uset(v_buckets_x27_6506_, v___x_6485_, v___x_6507_);
                    if v_isShared_6472_ == 0 {
                        lean_ctor_set(v___x_6471_, 1, v___x_6508_);
                        v___x_6510_ = v___x_6471_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6511_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_size_6468_);
                        lean_ctor_set(v_reuseFailAlloc_6511_, 1, v___x_6508_);
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
    mut v_a_6513_: *mut LeanObject,
    mut v_e_6514_: *mut LeanObject,
    mut v_a_6515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6517_ = lean_st_ref_take(v_a_6513_);
    v___x_6518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_6517_, v_e_6514_, v_a_6515_);
    v___x_6519_ = lean_st_ref_set(v_a_6513_, v___x_6518_);
    v___x_6520_ = lean_box(0);
    return v___x_6520_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(
    mut v_a_6521_: *mut LeanObject,
    mut v_e_6522_: *mut LeanObject,
    mut v_a_6523_: *mut LeanObject,
    mut v___y_6524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6525_: *mut LeanObject = core::ptr::null_mut();
    v_res_6525_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_6521_, v_e_6522_, v_a_6523_);
    lean_dec(v_a_6521_);
    return v_res_6525_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(
    mut v_fvars_6529_: *mut LeanObject,
    mut v_pre_6530_: *mut LeanObject,
    mut v_post_6531_: *mut LeanObject,
    mut v_usedLetOnly_6532_: u8,
    mut v_skipConstInApp_6533_: u8,
    mut v_skipInstances_6534_: u8,
    mut v_body_6535_: *mut LeanObject,
    mut v_x_6536_: *mut LeanObject,
    mut v___y_6537_: *mut LeanObject,
    mut v___y_6538_: *mut LeanObject,
    mut v___y_6539_: *mut LeanObject,
    mut v___y_6540_: *mut LeanObject,
    mut v___y_6541_: *mut LeanObject,
    mut v___y_6542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    v___x_6544_ = lean_array_push(v_fvars_6529_, v_x_6536_);
    v___x_6545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_6530_, v_post_6531_, v_usedLetOnly_6532_, v_skipConstInApp_6533_, v_skipInstances_6534_, v___x_6544_, v_body_6535_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_);
    return v___x_6545_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(
    mut v_fvars_6546_: *mut LeanObject,
    mut v_pre_6547_: *mut LeanObject,
    mut v_post_6548_: *mut LeanObject,
    mut v_usedLetOnly_6549_: *mut LeanObject,
    mut v_skipConstInApp_6550_: *mut LeanObject,
    mut v_skipInstances_6551_: *mut LeanObject,
    mut v_body_6552_: *mut LeanObject,
    mut v_x_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
    mut v___y_6559_: *mut LeanObject,
    mut v___y_6560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_6561_: u8 = 0;
    let mut v_skipConstInApp_boxed_6562_: u8 = 0;
    let mut v_skipInstances_boxed_6563_: u8 = 0;
    let mut v_res_6564_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6561_ = (lean_unbox(v_usedLetOnly_6549_) as u8);
    v_skipConstInApp_boxed_6562_ = (lean_unbox(v_skipConstInApp_6550_) as u8);
    v_skipInstances_boxed_6563_ = (lean_unbox(v_skipInstances_6551_) as u8);
    v_res_6564_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_6546_, v_pre_6547_, v_post_6548_, v_usedLetOnly_boxed_6561_, v_skipConstInApp_boxed_6562_, v_skipInstances_boxed_6563_, v_body_6552_, v_x_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
    lean_dec(v___y_6559_);
    lean_dec_ref(v___y_6558_);
    lean_dec(v___y_6557_);
    lean_dec_ref(v___y_6556_);
    lean_dec(v___y_6555_);
    lean_dec(v___y_6554_);
    return v_res_6564_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(
    mut v_pre_6565_: *mut LeanObject,
    mut v_post_6566_: *mut LeanObject,
    mut v_usedLetOnly_6567_: u8,
    mut v_skipConstInApp_6568_: u8,
    mut v_skipInstances_6569_: u8,
    mut v_e_6570_: *mut LeanObject,
    mut v_a_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6582_: u8 = 0;
    let mut v_e_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6597_: u8 = 0;
    let mut v_a_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6601_: u8 = 0;
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_post_6566_);
                lean_inc(v___y_6576_);
                lean_inc_ref(v___y_6575_);
                lean_inc(v___y_6574_);
                lean_inc_ref(v___y_6573_);
                lean_inc(v___y_6572_);
                lean_inc_ref(v_e_6570_);
                v___x_6578_ = lean_apply_7(
                    v_post_6566_,
                    v_e_6570_,
                    v___y_6572_,
                    v___y_6573_,
                    v___y_6574_,
                    v___y_6575_,
                    v___y_6576_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6578_) == 0 {
                    v_a_6579_ = lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6597_ = (!lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6597_ == 0 {
                        v___x_6581_ = v___x_6578_;
                        v_isShared_6582_ = v_isSharedCheck_6597_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6579_);
                        lean_dec(v___x_6578_);
                        v___x_6581_ = lean_box(0);
                        v_isShared_6582_ = v_isSharedCheck_6597_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_6570_);
                    lean_dec_ref(v_post_6566_);
                    lean_dec_ref(v_pre_6565_);
                    v_a_6598_ = lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6605_ = (!lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6605_ == 0 {
                        v___x_6600_ = v___x_6578_;
                        v_isShared_6601_ = v_isSharedCheck_6605_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6598_);
                        lean_dec(v___x_6578_);
                        v___x_6600_ = lean_box(0);
                        v_isShared_6601_ = v_isSharedCheck_6605_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_6579_) {
                0 => {
                    lean_dec_ref(v_e_6570_);
                    lean_dec_ref(v_post_6566_);
                    lean_dec_ref(v_pre_6565_);
                    v_e_6583_ = lean_ctor_get(v_a_6579_, 0);
                    lean_inc_ref(v_e_6583_);
                    lean_dec_ref_known(v_a_6579_, 1);
                    if v_isShared_6582_ == 0 {
                        lean_ctor_set(v___x_6581_, 0, v_e_6583_);
                        v___x_6585_ = v___x_6581_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6586_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_e_6583_);
                        v___x_6585_ = v_reuseFailAlloc_6586_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_6581_);
                    lean_dec_ref(v_e_6570_);
                    v_e_6587_ = lean_ctor_get(v_a_6579_, 0);
                    lean_inc_ref(v_e_6587_);
                    lean_dec_ref_known(v_a_6579_, 1);
                    v___x_6588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6565_, v_post_6566_, v_usedLetOnly_6567_, v_skipConstInApp_6568_, v_skipInstances_6569_, v_e_6587_, v_a_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
                    return v___x_6588_;
                }
                _ => {
                    lean_dec_ref(v_post_6566_);
                    lean_dec_ref(v_pre_6565_);
                    v_e_x3f_6589_ = lean_ctor_get(v_a_6579_, 0);
                    lean_inc(v_e_x3f_6589_);
                    lean_dec_ref_known(v_a_6579_, 1);
                    if lean_obj_tag(v_e_x3f_6589_) == 0 {
                        if v_isShared_6582_ == 0 {
                            lean_ctor_set(v___x_6581_, 0, v_e_6570_);
                            v___x_6591_ = v___x_6581_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6592_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6592_, 0, v_e_6570_);
                            v___x_6591_ = v_reuseFailAlloc_6592_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_6570_);
                        v_val_6593_ = lean_ctor_get(v_e_x3f_6589_, 0);
                        lean_inc(v_val_6593_);
                        lean_dec_ref_known(v_e_x3f_6589_, 1);
                        if v_isShared_6582_ == 0 {
                            lean_ctor_set(v___x_6581_, 0, v_val_6593_);
                            v___x_6595_ = v___x_6581_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6596_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6596_, 0, v_val_6593_);
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
                    v_reuseFailAlloc_6604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_a_6598_);
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
    mut v_pre_6606_: *mut LeanObject,
    mut v_post_6607_: *mut LeanObject,
    mut v_usedLetOnly_6608_: u8,
    mut v_skipConstInApp_6609_: u8,
    mut v_skipInstances_6610_: u8,
    mut v_fvars_6611_: *mut LeanObject,
    mut v_e_6612_: *mut LeanObject,
    mut v_a_6613_: *mut LeanObject,
    mut v___y_6614_: *mut LeanObject,
    mut v___y_6615_: *mut LeanObject,
    mut v___y_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_6612_) == 6 {
        let mut v_binderName_6620_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_6621_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_6622_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_6623_: u8 = 0;
        let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_6620_ = lean_ctor_get(v_e_6612_, 0);
        lean_inc(v_binderName_6620_);
        v_binderType_6621_ = lean_ctor_get(v_e_6612_, 1);
        lean_inc_ref(v_binderType_6621_);
        v_body_6622_ = lean_ctor_get(v_e_6612_, 2);
        lean_inc_ref(v_body_6622_);
        v_binderInfo_6623_ = lean_ctor_get_uint8(
            v_e_6612_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_6612_, 3);
        v___x_6624_ = lean_expr_instantiate_rev(v_binderType_6621_, v_fvars_6611_);
        lean_dec_ref(v_binderType_6621_);
        lean_inc_ref(v_post_6607_);
        lean_inc_ref(v_pre_6606_);
        v___x_6625_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v___x_6624_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
        if lean_obj_tag(v___x_6625_) == 0 {
            let mut v_a_6626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6631_: u8 = 0;
            let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
            v_a_6626_ = lean_ctor_get(v___x_6625_, 0);
            lean_inc(v_a_6626_);
            lean_dec_ref_known(v___x_6625_, 1);
            v___x_6627_ = lean_box((v_usedLetOnly_6608_) as usize);
            v___x_6628_ = lean_box((v_skipConstInApp_6609_) as usize);
            v___x_6629_ = lean_box((v_skipInstances_6610_) as usize);
            v___f_6630_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
            lean_closure_set(v___f_6630_, 0, v_fvars_6611_);
            lean_closure_set(v___f_6630_, 1, v_pre_6606_);
            lean_closure_set(v___f_6630_, 2, v_post_6607_);
            lean_closure_set(v___f_6630_, 3, v___x_6627_);
            lean_closure_set(v___f_6630_, 4, v___x_6628_);
            lean_closure_set(v___f_6630_, 5, v___x_6629_);
            lean_closure_set(v___f_6630_, 6, v_body_6622_);
            v___x_6631_ = 0;
            v___x_6632_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_6620_, v_binderInfo_6623_, v_a_6626_, v___f_6630_, v___x_6631_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
            return v___x_6632_;
        } else {
            lean_dec_ref(v_body_6622_);
            lean_dec(v_binderName_6620_);
            lean_dec_ref(v_fvars_6611_);
            lean_dec_ref(v_post_6607_);
            lean_dec_ref(v_pre_6606_);
            return v___x_6625_;
        }
    } else {
        let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
        v___x_6633_ = lean_expr_instantiate_rev(v_e_6612_, v_fvars_6611_);
        lean_dec_ref(v_e_6612_);
        lean_inc_ref(v_post_6607_);
        lean_inc_ref(v_pre_6606_);
        v___x_6634_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v___x_6633_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
        if lean_obj_tag(v___x_6634_) == 0 {
            let mut v_a_6635_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6636_: u8 = 0;
            let mut v___x_6637_: u8 = 0;
            let mut v___x_6638_: u8 = 0;
            let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
            v_a_6635_ = lean_ctor_get(v___x_6634_, 0);
            lean_inc(v_a_6635_);
            lean_dec_ref_known(v___x_6634_, 1);
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
            lean_dec_ref(v_fvars_6611_);
            if lean_obj_tag(v___x_6639_) == 0 {
                let mut v_a_6640_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
                v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
                lean_inc(v_a_6640_);
                lean_dec_ref_known(v___x_6639_, 1);
                v___x_6641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6606_, v_post_6607_, v_usedLetOnly_6608_, v_skipConstInApp_6609_, v_skipInstances_6610_, v_a_6640_, v_a_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
                return v___x_6641_;
            } else {
                lean_dec_ref(v_post_6607_);
                lean_dec_ref(v_pre_6606_);
                return v___x_6639_;
            }
        } else {
            lean_dec_ref(v_fvars_6611_);
            lean_dec_ref(v_post_6607_);
            lean_dec_ref(v_pre_6606_);
            return v___x_6634_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(
    mut v_fvars_6642_: *mut LeanObject,
    mut v_pre_6643_: *mut LeanObject,
    mut v_post_6644_: *mut LeanObject,
    mut v_usedLetOnly_6645_: u8,
    mut v_skipConstInApp_6646_: u8,
    mut v_skipInstances_6647_: u8,
    mut v_body_6648_: *mut LeanObject,
    mut v_x_6649_: *mut LeanObject,
    mut v___y_6650_: *mut LeanObject,
    mut v___y_6651_: *mut LeanObject,
    mut v___y_6652_: *mut LeanObject,
    mut v___y_6653_: *mut LeanObject,
    mut v___y_6654_: *mut LeanObject,
    mut v___y_6655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    v___x_6657_ = lean_array_push(v_fvars_6642_, v_x_6649_);
    v___x_6658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_6643_, v_post_6644_, v_usedLetOnly_6645_, v_skipConstInApp_6646_, v_skipInstances_6647_, v___x_6657_, v_body_6648_, v___y_6650_, v___y_6651_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
    return v___x_6658_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(
    mut v_fvars_6659_: *mut LeanObject,
    mut v_pre_6660_: *mut LeanObject,
    mut v_post_6661_: *mut LeanObject,
    mut v_usedLetOnly_6662_: *mut LeanObject,
    mut v_skipConstInApp_6663_: *mut LeanObject,
    mut v_skipInstances_6664_: *mut LeanObject,
    mut v_body_6665_: *mut LeanObject,
    mut v_x_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
    mut v___y_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_6674_: u8 = 0;
    let mut v_skipConstInApp_boxed_6675_: u8 = 0;
    let mut v_skipInstances_boxed_6676_: u8 = 0;
    let mut v_res_6677_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6674_ = (lean_unbox(v_usedLetOnly_6662_) as u8);
    v_skipConstInApp_boxed_6675_ = (lean_unbox(v_skipConstInApp_6663_) as u8);
    v_skipInstances_boxed_6676_ = (lean_unbox(v_skipInstances_6664_) as u8);
    v_res_6677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_6659_, v_pre_6660_, v_post_6661_, v_usedLetOnly_boxed_6674_, v_skipConstInApp_boxed_6675_, v_skipInstances_boxed_6676_, v_body_6665_, v_x_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
    lean_dec(v___y_6672_);
    lean_dec_ref(v___y_6671_);
    lean_dec(v___y_6670_);
    lean_dec_ref(v___y_6669_);
    lean_dec(v___y_6668_);
    lean_dec(v___y_6667_);
    return v_res_6677_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(
    mut v_pre_6678_: *mut LeanObject,
    mut v_post_6679_: *mut LeanObject,
    mut v_usedLetOnly_6680_: u8,
    mut v_skipConstInApp_6681_: u8,
    mut v_skipInstances_6682_: u8,
    mut v_fvars_6683_: *mut LeanObject,
    mut v_e_6684_: *mut LeanObject,
    mut v_a_6685_: *mut LeanObject,
    mut v___y_6686_: *mut LeanObject,
    mut v___y_6687_: *mut LeanObject,
    mut v___y_6688_: *mut LeanObject,
    mut v___y_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_6684_) == 8 {
        let mut v_declName_6692_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_6693_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_6694_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_6695_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nondep_6696_: u8 = 0;
        let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
        v_declName_6692_ = lean_ctor_get(v_e_6684_, 0);
        lean_inc(v_declName_6692_);
        v_type_6693_ = lean_ctor_get(v_e_6684_, 1);
        lean_inc_ref(v_type_6693_);
        v_value_6694_ = lean_ctor_get(v_e_6684_, 2);
        lean_inc_ref(v_value_6694_);
        v_body_6695_ = lean_ctor_get(v_e_6684_, 3);
        lean_inc_ref(v_body_6695_);
        v_nondep_6696_ = lean_ctor_get_uint8(
            v_e_6684_,
            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
        );
        lean_dec_ref_known(v_e_6684_, 4);
        v___x_6697_ = lean_expr_instantiate_rev(v_type_6693_, v_fvars_6683_);
        lean_dec_ref(v_type_6693_);
        lean_inc_ref(v_post_6679_);
        lean_inc_ref(v_pre_6678_);
        v___x_6698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6697_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
        if lean_obj_tag(v___x_6698_) == 0 {
            let mut v_a_6699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
            v_a_6699_ = lean_ctor_get(v___x_6698_, 0);
            lean_inc(v_a_6699_);
            lean_dec_ref_known(v___x_6698_, 1);
            v___x_6700_ = lean_expr_instantiate_rev(v_value_6694_, v_fvars_6683_);
            lean_dec_ref(v_value_6694_);
            lean_inc_ref(v_post_6679_);
            lean_inc_ref(v_pre_6678_);
            v___x_6701_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6700_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
            if lean_obj_tag(v___x_6701_) == 0 {
                let mut v_a_6702_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_6706_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6707_: u8 = 0;
                let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
                v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
                lean_inc(v_a_6702_);
                lean_dec_ref_known(v___x_6701_, 1);
                v___x_6703_ = lean_box((v_usedLetOnly_6680_) as usize);
                v___x_6704_ = lean_box((v_skipConstInApp_6681_) as usize);
                v___x_6705_ = lean_box((v_skipInstances_6682_) as usize);
                v___f_6706_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
                lean_closure_set(v___f_6706_, 0, v_fvars_6683_);
                lean_closure_set(v___f_6706_, 1, v_pre_6678_);
                lean_closure_set(v___f_6706_, 2, v_post_6679_);
                lean_closure_set(v___f_6706_, 3, v___x_6703_);
                lean_closure_set(v___f_6706_, 4, v___x_6704_);
                lean_closure_set(v___f_6706_, 5, v___x_6705_);
                lean_closure_set(v___f_6706_, 6, v_body_6695_);
                v___x_6707_ = 0;
                v___x_6708_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_6692_, v_a_6699_, v_a_6702_, v___f_6706_, v_nondep_6696_, v___x_6707_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
                return v___x_6708_;
            } else {
                lean_dec(v_a_6699_);
                lean_dec_ref(v_body_6695_);
                lean_dec(v_declName_6692_);
                lean_dec_ref(v_fvars_6683_);
                lean_dec_ref(v_post_6679_);
                lean_dec_ref(v_pre_6678_);
                return v___x_6701_;
            }
        } else {
            lean_dec_ref(v_body_6695_);
            lean_dec_ref(v_value_6694_);
            lean_dec(v_declName_6692_);
            lean_dec_ref(v_fvars_6683_);
            lean_dec_ref(v_post_6679_);
            lean_dec_ref(v_pre_6678_);
            return v___x_6698_;
        }
    } else {
        let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
        v___x_6709_ = lean_expr_instantiate_rev(v_e_6684_, v_fvars_6683_);
        lean_dec_ref(v_e_6684_);
        lean_inc_ref(v_post_6679_);
        lean_inc_ref(v_pre_6678_);
        v___x_6710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v___x_6709_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
        if lean_obj_tag(v___x_6710_) == 0 {
            let mut v_a_6711_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6712_: u8 = 0;
            let mut v___x_6713_: u8 = 0;
            let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
            v_a_6711_ = lean_ctor_get(v___x_6710_, 0);
            lean_inc(v_a_6711_);
            lean_dec_ref_known(v___x_6710_, 1);
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
            lean_dec_ref(v_fvars_6683_);
            if lean_obj_tag(v___x_6714_) == 0 {
                let mut v_a_6715_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
                v_a_6715_ = lean_ctor_get(v___x_6714_, 0);
                lean_inc(v_a_6715_);
                lean_dec_ref_known(v___x_6714_, 1);
                v___x_6716_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6678_, v_post_6679_, v_usedLetOnly_6680_, v_skipConstInApp_6681_, v_skipInstances_6682_, v_a_6715_, v_a_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
                return v___x_6716_;
            } else {
                lean_dec_ref(v_post_6679_);
                lean_dec_ref(v_pre_6678_);
                return v___x_6714_;
            }
        } else {
            lean_dec_ref(v_fvars_6683_);
            lean_dec_ref(v_post_6679_);
            lean_dec_ref(v_pre_6678_);
            return v___x_6710_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_6718_: *mut LeanObject = core::ptr::null_mut();
    v___x_6717_ = lean_box(0);
    v_dummy_6718_ = l_Lean_Expr_sort___override(v___x_6717_);
    return v_dummy_6718_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(
    mut v_pre_6719_: *mut LeanObject,
    mut v_post_6720_: *mut LeanObject,
    mut v_usedLetOnly_6721_: u8,
    mut v_skipConstInApp_6722_: u8,
    mut v_skipInstances_6723_: u8,
    mut v_sz_6724_: usize,
    mut v_i_6725_: usize,
    mut v_bs_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6734_: u8 = 0;
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: usize = 0;
    let mut v___x_6742_: usize = 0;
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6734_ = lean_usize_dec_lt(v_i_6725_, v_sz_6724_);
                if v___x_6734_ == 0 {
                    lean_dec_ref(v_post_6720_);
                    lean_dec_ref(v_pre_6719_);
                    v___x_6735_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6735_, 0, v_bs_6726_);
                    return v___x_6735_;
                } else {
                    v_v_6736_ = lean_array_uget_borrowed(v_bs_6726_, v_i_6725_);
                    lean_inc(v_v_6736_);
                    lean_inc_ref(v_post_6720_);
                    lean_inc_ref(v_pre_6719_);
                    v___x_6737_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6719_, v_post_6720_, v_usedLetOnly_6721_, v_skipConstInApp_6722_, v_skipInstances_6723_, v_v_6736_, v___y_6727_, v___y_6728_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_);
                    if lean_obj_tag(v___x_6737_) == 0 {
                        v_a_6738_ = lean_ctor_get(v___x_6737_, 0);
                        lean_inc(v_a_6738_);
                        lean_dec_ref_known(v___x_6737_, 1);
                        v___x_6739_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6740_ = lean_array_uset(v_bs_6726_, v_i_6725_, v___x_6739_);
                        v___x_6741_ = 1usize;
                        v___x_6742_ = lean_usize_add(v_i_6725_, v___x_6741_);
                        v___x_6743_ = lean_array_uset(v_bs_x27_6740_, v_i_6725_, v_a_6738_);
                        v_i_6725_ = v___x_6742_;
                        v_bs_6726_ = v___x_6743_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6726_);
                        lean_dec_ref(v_post_6720_);
                        lean_dec_ref(v_pre_6719_);
                        v_a_6745_ = lean_ctor_get(v___x_6737_, 0);
                        v_isSharedCheck_6752_ = (!lean_is_exclusive(v___x_6737_)) as u8;
                        if v_isSharedCheck_6752_ == 0 {
                            v___x_6747_ = v___x_6737_;
                            v_isShared_6748_ = v_isSharedCheck_6752_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6745_);
                            lean_dec(v___x_6737_);
                            v___x_6747_ = lean_box(0);
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
                    v_reuseFailAlloc_6751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_a_6745_);
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
    mut v_pre_6753_: *mut LeanObject,
    mut v_post_6754_: *mut LeanObject,
    mut v_usedLetOnly_6755_: u8,
    mut v_skipConstInApp_6756_: u8,
    mut v_skipInstances_6757_: u8,
    mut v___x_6758_: *mut LeanObject,
    mut v___y_6759_: *mut LeanObject,
    mut v_b_6760_: *mut LeanObject,
    mut v_a_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6772_: u8 = 0;
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6778_: u8 = 0;
    let mut v_a_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6753_, v_post_6754_, v_usedLetOnly_6755_, v_skipConstInApp_6756_, v_skipInstances_6757_, v___x_6758_, v___y_6759_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_);
                if lean_obj_tag(v___x_6768_) == 0 {
                    v_a_6769_ = lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6778_ = (!lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6778_ == 0 {
                        v___x_6771_ = v___x_6768_;
                        v_isShared_6772_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6769_);
                        lean_dec(v___x_6768_);
                        v___x_6771_ = lean_box(0);
                        v_isShared_6772_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_6760_);
                    v_a_6779_ = lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6786_ = (!lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6786_ == 0 {
                        v___x_6781_ = v___x_6768_;
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6779_);
                        lean_dec(v___x_6768_);
                        v___x_6781_ = lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6773_ = lean_array_fset(v_b_6760_, v_a_6761_, v_a_6769_);
                v___x_6774_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6774_, 0, v___x_6773_);
                if v_isShared_6772_ == 0 {
                    lean_ctor_set(v___x_6771_, 0, v___x_6774_);
                    v___x_6776_ = v___x_6771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6777_, 0, v___x_6774_);
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
                    v_reuseFailAlloc_6785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_a_6779_);
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
    mut v_pre_6787_: *mut LeanObject,
    mut v_post_6788_: *mut LeanObject,
    mut v_usedLetOnly_6789_: *mut LeanObject,
    mut v_skipConstInApp_6790_: *mut LeanObject,
    mut v_skipInstances_6791_: *mut LeanObject,
    mut v___x_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v_b_6794_: *mut LeanObject,
    mut v_a_6795_: *mut LeanObject,
    mut v___y_6796_: *mut LeanObject,
    mut v___y_6797_: *mut LeanObject,
    mut v___y_6798_: *mut LeanObject,
    mut v___y_6799_: *mut LeanObject,
    mut v___y_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_6802_: u8 = 0;
    let mut v_skipConstInApp_boxed_6803_: u8 = 0;
    let mut v_skipInstances_boxed_6804_: u8 = 0;
    let mut v_res_6805_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6802_ = (lean_unbox(v_usedLetOnly_6789_) as u8);
    v_skipConstInApp_boxed_6803_ = (lean_unbox(v_skipConstInApp_6790_) as u8);
    v_skipInstances_boxed_6804_ = (lean_unbox(v_skipInstances_6791_) as u8);
    v_res_6805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_6787_, v_post_6788_, v_usedLetOnly_boxed_6802_, v_skipConstInApp_boxed_6803_, v_skipInstances_boxed_6804_, v___x_6792_, v___y_6793_, v_b_6794_, v_a_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_);
    lean_dec(v___y_6800_);
    lean_dec_ref(v___y_6799_);
    lean_dec(v___y_6798_);
    lean_dec_ref(v___y_6797_);
    lean_dec(v___y_6796_);
    lean_dec(v_a_6795_);
    lean_dec(v___y_6793_);
    return v_res_6805_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(
    mut v_upperBound_6806_: *mut LeanObject,
    mut v___x_6807_: *mut LeanObject,
    mut v_pre_6808_: *mut LeanObject,
    mut v_post_6809_: *mut LeanObject,
    mut v_usedLetOnly_6810_: u8,
    mut v_skipConstInApp_6811_: u8,
    mut v_skipInstances_6812_: u8,
    mut v_a_6813_: *mut LeanObject,
    mut v_b_6814_: *mut LeanObject,
    mut v___y_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
    mut v___y_6818_: *mut LeanObject,
    mut v___y_6819_: *mut LeanObject,
    mut v___y_6820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6828_: u8 = 0;
    let mut v_a_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6837_: u8 = 0;
    let mut v_a_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6841_: u8 = 0;
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_6856_: u8 = 0;
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6846_ = lean_nat_dec_lt(v_a_6813_, v_upperBound_6806_);
                if v___x_6846_ == 0 {
                    lean_dec(v_a_6813_);
                    lean_dec_ref(v_post_6809_);
                    lean_dec_ref(v_pre_6808_);
                    v___x_6847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6847_, 0, v_b_6814_);
                    return v___x_6847_;
                } else {
                    v___x_6848_ = lean_array_fget_borrowed(v_b_6814_, v_a_6813_);
                    v___x_6849_ = lean_array_get_size(v___x_6807_);
                    v___x_6850_ = lean_nat_dec_lt(v_a_6813_, v___x_6849_);
                    if v___x_6850_ == 0 {
                        lean_inc(v___x_6848_);
                        v___x_6851_ = lean_box((v_usedLetOnly_6810_) as usize);
                        v___x_6852_ = lean_box((v_skipConstInApp_6811_) as usize);
                        v___x_6853_ = lean_box((v_skipInstances_6812_) as usize);
                        lean_inc(v_a_6813_);
                        lean_inc(v___y_6815_);
                        lean_inc_ref(v_post_6809_);
                        lean_inc_ref(v_pre_6808_);
                        v___f_6854_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                        lean_closure_set(v___f_6854_, 0, v_pre_6808_);
                        lean_closure_set(v___f_6854_, 1, v_post_6809_);
                        lean_closure_set(v___f_6854_, 2, v___x_6851_);
                        lean_closure_set(v___f_6854_, 3, v___x_6852_);
                        lean_closure_set(v___f_6854_, 4, v___x_6853_);
                        lean_closure_set(v___f_6854_, 5, v___x_6848_);
                        lean_closure_set(v___f_6854_, 6, v___y_6815_);
                        lean_closure_set(v___f_6854_, 7, v_b_6814_);
                        lean_closure_set(v___f_6854_, 8, v_a_6813_);
                        v___y_6823_ = v___f_6854_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6855_ = lean_array_fget_borrowed(v___x_6807_, v_a_6813_);
                        v_isInstance_6856_ = lean_ctor_get_uint8(
                            v___x_6855_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_6856_ == 0 {
                            lean_inc(v___x_6848_);
                            v___x_6857_ = lean_box((v_usedLetOnly_6810_) as usize);
                            v___x_6858_ = lean_box((v_skipConstInApp_6811_) as usize);
                            v___x_6859_ = lean_box((v_skipInstances_6812_) as usize);
                            lean_inc(v_a_6813_);
                            lean_inc(v___y_6815_);
                            lean_inc_ref(v_post_6809_);
                            lean_inc_ref(v_pre_6808_);
                            v___f_6860_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                            lean_closure_set(v___f_6860_, 0, v_pre_6808_);
                            lean_closure_set(v___f_6860_, 1, v_post_6809_);
                            lean_closure_set(v___f_6860_, 2, v___x_6857_);
                            lean_closure_set(v___f_6860_, 3, v___x_6858_);
                            lean_closure_set(v___f_6860_, 4, v___x_6859_);
                            lean_closure_set(v___f_6860_, 5, v___x_6848_);
                            lean_closure_set(v___f_6860_, 6, v___y_6815_);
                            lean_closure_set(v___f_6860_, 7, v_b_6814_);
                            lean_closure_set(v___f_6860_, 8, v_a_6813_);
                            v___y_6823_ = v___f_6860_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6861_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6861_, 0, v_b_6814_);
                            v___f_6862_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 7, 1);
                            lean_closure_set(v___f_6862_, 0, v___x_6861_);
                            v___y_6823_ = v___f_6862_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_6820_);
                lean_inc_ref(v___y_6819_);
                lean_inc(v___y_6818_);
                lean_inc_ref(v___y_6817_);
                lean_inc(v___y_6816_);
                v___x_6824_ = lean_apply_6(
                    v___y_6823_,
                    v___y_6816_,
                    v___y_6817_,
                    v___y_6818_,
                    v___y_6819_,
                    v___y_6820_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6824_) == 0 {
                    v_a_6825_ = lean_ctor_get(v___x_6824_, 0);
                    v_isSharedCheck_6837_ = (!lean_is_exclusive(v___x_6824_)) as u8;
                    if v_isSharedCheck_6837_ == 0 {
                        v___x_6827_ = v___x_6824_;
                        v_isShared_6828_ = v_isSharedCheck_6837_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6825_);
                        lean_dec(v___x_6824_);
                        v___x_6827_ = lean_box(0);
                        v_isShared_6828_ = v_isSharedCheck_6837_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6813_);
                    lean_dec_ref(v_post_6809_);
                    lean_dec_ref(v_pre_6808_);
                    v_a_6838_ = lean_ctor_get(v___x_6824_, 0);
                    v_isSharedCheck_6845_ = (!lean_is_exclusive(v___x_6824_)) as u8;
                    if v_isSharedCheck_6845_ == 0 {
                        v___x_6840_ = v___x_6824_;
                        v_isShared_6841_ = v_isSharedCheck_6845_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6838_);
                        lean_dec(v___x_6824_);
                        v___x_6840_ = lean_box(0);
                        v_isShared_6841_ = v_isSharedCheck_6845_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6825_) == 0 {
                    lean_dec(v_a_6813_);
                    lean_dec_ref(v_post_6809_);
                    lean_dec_ref(v_pre_6808_);
                    v_a_6829_ = lean_ctor_get(v_a_6825_, 0);
                    lean_inc(v_a_6829_);
                    lean_dec_ref_known(v_a_6825_, 1);
                    if v_isShared_6828_ == 0 {
                        lean_ctor_set(v___x_6827_, 0, v_a_6829_);
                        v___x_6831_ = v___x_6827_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6832_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6829_);
                        v___x_6831_ = v_reuseFailAlloc_6832_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6827_);
                    v_a_6833_ = lean_ctor_get(v_a_6825_, 0);
                    lean_inc(v_a_6833_);
                    lean_dec_ref_known(v_a_6825_, 1);
                    v___x_6834_ = lean_unsigned_to_nat(1);
                    v___x_6835_ = lean_nat_add(v_a_6813_, v___x_6834_);
                    lean_dec(v_a_6813_);
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
                    v_reuseFailAlloc_6844_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_a_6838_);
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
    mut v_pre_6864_: *mut LeanObject,
    mut v_post_6865_: *mut LeanObject,
    mut v_usedLetOnly_6866_: u8,
    mut v_skipConstInApp_6867_: u8,
    mut v_x_6868_: *mut LeanObject,
    mut v_x_6869_: *mut LeanObject,
    mut v_x_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
    mut v___y_6876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6886_: usize = 0;
    let mut v___x_6887_: usize = 0;
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6895_: u8 = 0;
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6899_: u8 = 0;
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6912_: u8 = 0;
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6916_: u8 = 0;
    let mut v_a_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6924_: u8 = 0;
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6868_) == 5 {
                    v_fn_6928_ = lean_ctor_get(v_x_6868_, 0);
                    lean_inc_ref(v_fn_6928_);
                    v_arg_6929_ = lean_ctor_get(v_x_6868_, 1);
                    lean_inc_ref(v_arg_6929_);
                    lean_dec_ref_known(v_x_6868_, 2);
                    v___x_6930_ = lean_array_set(v_x_6869_, v_x_6870_, v_arg_6929_);
                    v___x_6931_ = lean_unsigned_to_nat(1);
                    v___x_6932_ = lean_nat_sub(v_x_6870_, v___x_6931_);
                    lean_dec(v_x_6870_);
                    v_x_6868_ = v_fn_6928_;
                    v_x_6869_ = v___x_6930_;
                    v_x_6870_ = v___x_6932_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_6870_);
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
                    lean_inc_ref(v_post_6865_);
                    lean_inc_ref(v_pre_6864_);
                    v___x_6888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v_sz_6886_, v___x_6887_, v_x_6869_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                    if lean_obj_tag(v___x_6888_) == 0 {
                        v_a_6889_ = lean_ctor_get(v___x_6888_, 0);
                        lean_inc(v_a_6889_);
                        lean_dec_ref_known(v___x_6888_, 1);
                        v___x_6890_ = l_Lean_mkAppN(v_f_6879_, v_a_6889_);
                        lean_dec(v_a_6889_);
                        v___x_6891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6890_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                        return v___x_6891_;
                    } else {
                        lean_dec_ref(v_f_6879_);
                        lean_dec_ref(v_post_6865_);
                        lean_dec_ref(v_pre_6864_);
                        v_a_6892_ = lean_ctor_get(v___x_6888_, 0);
                        v_isSharedCheck_6899_ = (!lean_is_exclusive(v___x_6888_)) as u8;
                        if v_isSharedCheck_6899_ == 0 {
                            v___x_6894_ = v___x_6888_;
                            v_isShared_6895_ = v_isSharedCheck_6899_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6892_);
                            lean_dec(v___x_6888_);
                            v___x_6894_ = lean_box(0);
                            v_isShared_6895_ = v_isSharedCheck_6899_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_6900_ = lean_array_get_size(v_x_6869_);
                    lean_inc_ref(v_f_6879_);
                    v___x_6901_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_6879_,
                        v___x_6900_,
                        v___y_6882_,
                        v___y_6883_,
                        v___y_6884_,
                        v___y_6885_,
                    );
                    if lean_obj_tag(v___x_6901_) == 0 {
                        v_a_6902_ = lean_ctor_get(v___x_6901_, 0);
                        lean_inc(v_a_6902_);
                        lean_dec_ref_known(v___x_6901_, 1);
                        v_paramInfo_6903_ = lean_ctor_get(v_a_6902_, 0);
                        lean_inc_ref(v_paramInfo_6903_);
                        lean_dec(v_a_6902_);
                        v___x_6904_ = lean_unsigned_to_nat(0);
                        lean_inc_ref(v_post_6865_);
                        lean_inc_ref(v_pre_6864_);
                        v___x_6905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_6900_, v_paramInfo_6903_, v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6904_, v_x_6869_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                        lean_dec_ref(v_paramInfo_6903_);
                        if lean_obj_tag(v___x_6905_) == 0 {
                            v_a_6906_ = lean_ctor_get(v___x_6905_, 0);
                            lean_inc(v_a_6906_);
                            lean_dec_ref_known(v___x_6905_, 1);
                            v___x_6907_ = l_Lean_mkAppN(v_f_6879_, v_a_6906_);
                            lean_dec(v_a_6906_);
                            v___x_6908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v___x_6907_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
                            return v___x_6908_;
                        } else {
                            lean_dec_ref(v_f_6879_);
                            lean_dec_ref(v_post_6865_);
                            lean_dec_ref(v_pre_6864_);
                            v_a_6909_ = lean_ctor_get(v___x_6905_, 0);
                            v_isSharedCheck_6916_ = (!lean_is_exclusive(v___x_6905_)) as u8;
                            if v_isSharedCheck_6916_ == 0 {
                                v___x_6911_ = v___x_6905_;
                                v_isShared_6912_ = v_isSharedCheck_6916_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_6909_);
                                lean_dec(v___x_6905_);
                                v___x_6911_ = lean_box(0);
                                v_isShared_6912_ = v_isSharedCheck_6916_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_f_6879_);
                        lean_dec_ref(v_x_6869_);
                        lean_dec_ref(v_post_6865_);
                        lean_dec_ref(v_pre_6864_);
                        v_a_6917_ = lean_ctor_get(v___x_6901_, 0);
                        v_isSharedCheck_6924_ = (!lean_is_exclusive(v___x_6901_)) as u8;
                        if v_isSharedCheck_6924_ == 0 {
                            v___x_6919_ = v___x_6901_;
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6917_);
                            lean_dec(v___x_6901_);
                            v___x_6919_ = lean_box(0);
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
                    v_reuseFailAlloc_6898_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 0, v_a_6892_);
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
                    v_reuseFailAlloc_6915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6915_, 0, v_a_6909_);
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
                    v_reuseFailAlloc_6923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6917_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6922_;
            }
            8 => {
                lean_inc_ref(v_post_6865_);
                lean_inc_ref(v_pre_6864_);
                v___x_6926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6864_, v_post_6865_, v_usedLetOnly_6866_, v_skipConstInApp_6867_, v_skipInstances_6863_, v_x_6868_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                if lean_obj_tag(v___x_6926_) == 0 {
                    v_a_6927_ = lean_ctor_get(v___x_6926_, 0);
                    lean_inc(v_a_6927_);
                    lean_dec_ref_known(v___x_6926_, 1);
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
                    lean_dec_ref(v_x_6869_);
                    lean_dec_ref(v_post_6865_);
                    lean_dec_ref(v_pre_6864_);
                    return v___x_6926_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(
    mut v___x_6935_: *mut LeanObject,
    mut v_pre_6936_: *mut LeanObject,
    mut v_e_6937_: *mut LeanObject,
    mut v_post_6938_: *mut LeanObject,
    mut v_usedLetOnly_6939_: u8,
    mut v_skipConstInApp_6940_: u8,
    mut v_skipInstances_6941_: u8,
    mut v___y_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6954_: u8 = 0;
    let mut v___y_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: usize = 0;
    let mut v___x_6974_: usize = 0;
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: usize = 0;
    let mut v___x_6985_: usize = 0;
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_a_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v_a_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7011_: u8 = 0;
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6949_ = l_Lean_Core_checkSystem(v___x_6935_, v___y_6946_, v___y_6947_);
                if lean_obj_tag(v___x_6949_) == 0 {
                    lean_dec_ref_known(v___x_6949_, 1);
                    lean_inc_ref(v_pre_6936_);
                    lean_inc(v___y_6947_);
                    lean_inc_ref(v___y_6946_);
                    lean_inc(v___y_6945_);
                    lean_inc_ref(v___y_6944_);
                    lean_inc(v___y_6943_);
                    lean_inc_ref(v_e_6937_);
                    v___x_6950_ = lean_apply_7(
                        v_pre_6936_,
                        v_e_6937_,
                        v___y_6943_,
                        v___y_6944_,
                        v___y_6945_,
                        v___y_6946_,
                        v___y_6947_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6950_) == 0 {
                        v_a_6951_ = lean_ctor_get(v___x_6950_, 0);
                        v_isSharedCheck_6999_ = (!lean_is_exclusive(v___x_6950_)) as u8;
                        if v_isSharedCheck_6999_ == 0 {
                            v___x_6953_ = v___x_6950_;
                            v_isShared_6954_ = v_isSharedCheck_6999_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6951_);
                            lean_dec(v___x_6950_);
                            v___x_6953_ = lean_box(0);
                            v_isShared_6954_ = v_isSharedCheck_6999_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_post_6938_);
                        lean_dec_ref(v_e_6937_);
                        lean_dec_ref(v_pre_6936_);
                        v_a_7000_ = lean_ctor_get(v___x_6950_, 0);
                        v_isSharedCheck_7007_ = (!lean_is_exclusive(v___x_6950_)) as u8;
                        if v_isSharedCheck_7007_ == 0 {
                            v___x_7002_ = v___x_6950_;
                            v_isShared_7003_ = v_isSharedCheck_7007_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7000_);
                            lean_dec(v___x_6950_);
                            v___x_7002_ = lean_box(0);
                            v_isShared_7003_ = v_isSharedCheck_7007_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_post_6938_);
                    lean_dec_ref(v_e_6937_);
                    lean_dec_ref(v_pre_6936_);
                    v_a_7008_ = lean_ctor_get(v___x_6949_, 0);
                    v_isSharedCheck_7015_ = (!lean_is_exclusive(v___x_6949_)) as u8;
                    if v_isSharedCheck_7015_ == 0 {
                        v___x_7010_ = v___x_6949_;
                        v_isShared_7011_ = v_isSharedCheck_7015_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7008_);
                        lean_dec(v___x_6949_);
                        v___x_7010_ = lean_box(0);
                        v_isShared_7011_ = v_isSharedCheck_7015_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_6951_) {
                0 => {
                    lean_dec_ref(v_post_6938_);
                    lean_dec_ref(v_e_6937_);
                    lean_dec_ref(v_pre_6936_);
                    v_e_6991_ = lean_ctor_get(v_a_6951_, 0);
                    lean_inc_ref(v_e_6991_);
                    lean_dec_ref_known(v_a_6951_, 1);
                    if v_isShared_6954_ == 0 {
                        lean_ctor_set(v___x_6953_, 0, v_e_6991_);
                        v___x_6993_ = v___x_6953_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6994_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6994_, 0, v_e_6991_);
                        v___x_6993_ = v_reuseFailAlloc_6994_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_6953_);
                    lean_dec_ref(v_e_6937_);
                    v_e_6995_ = lean_ctor_get(v_a_6951_, 0);
                    lean_inc_ref(v_e_6995_);
                    lean_dec_ref_known(v_a_6951_, 1);
                    v___x_6996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_e_6995_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6996_;
                }
                _ => {
                    lean_del_object(v___x_6953_);
                    v_e_x3f_6997_ = lean_ctor_get(v_a_6951_, 0);
                    lean_inc(v_e_x3f_6997_);
                    lean_dec_ref_known(v_a_6951_, 1);
                    if lean_obj_tag(v_e_x3f_6997_) == 0 {
                        v___y_6956_ = v_e_6937_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_e_6937_);
                        v_val_6998_ = lean_ctor_get(v_e_x3f_6997_, 0);
                        lean_inc(v_val_6998_);
                        lean_dec_ref_known(v_e_x3f_6997_, 1);
                        v___y_6956_ = v_val_6998_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match lean_obj_tag(v___y_6956_) {
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
                    v_dummy_6963_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once), _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
                    v_nargs_6964_ = l_Lean_Expr_getAppNumArgs(v___y_6956_);
                    lean_inc(v_nargs_6964_);
                    v___x_6965_ = lean_mk_array(v_nargs_6964_, v_dummy_6963_);
                    v___x_6966_ = lean_unsigned_to_nat(1);
                    v___x_6967_ = lean_nat_sub(v_nargs_6964_, v___x_6966_);
                    lean_dec(v_nargs_6964_);
                    v___x_6968_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_6941_, v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v___y_6956_, v___x_6965_, v___x_6967_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    return v___x_6968_;
                }
                10 => {
                    v_data_6969_ = lean_ctor_get(v___y_6956_, 0);
                    v_expr_6970_ = lean_ctor_get(v___y_6956_, 1);
                    lean_inc_ref(v_expr_6970_);
                    lean_inc_ref(v_post_6938_);
                    lean_inc_ref(v_pre_6936_);
                    v___x_6971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_expr_6970_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    if lean_obj_tag(v___x_6971_) == 0 {
                        v_a_6972_ = lean_ctor_get(v___x_6971_, 0);
                        lean_inc(v_a_6972_);
                        lean_dec_ref_known(v___x_6971_, 1);
                        v___x_6973_ = lean_ptr_addr(v_expr_6970_);
                        v___x_6974_ = lean_ptr_addr(v_a_6972_);
                        v___x_6975_ = lean_usize_dec_eq(v___x_6973_, v___x_6974_);
                        if v___x_6975_ == 0 {
                            lean_inc(v_data_6969_);
                            lean_dec_ref_known(v___y_6956_, 2);
                            v___x_6976_ = l_Lean_Expr_mdata___override(v_data_6969_, v_a_6972_);
                            v___x_6977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6976_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6977_;
                        } else {
                            lean_dec(v_a_6972_);
                            v___x_6978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6978_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_6956_, 2);
                        lean_dec_ref(v_post_6938_);
                        lean_dec_ref(v_pre_6936_);
                        return v___x_6971_;
                    }
                }
                11 => {
                    v_typeName_6979_ = lean_ctor_get(v___y_6956_, 0);
                    v_idx_6980_ = lean_ctor_get(v___y_6956_, 1);
                    v_struct_6981_ = lean_ctor_get(v___y_6956_, 2);
                    lean_inc_ref(v_struct_6981_);
                    lean_inc_ref(v_post_6938_);
                    lean_inc_ref(v_pre_6936_);
                    v___x_6982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v_struct_6981_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                    if lean_obj_tag(v___x_6982_) == 0 {
                        v_a_6983_ = lean_ctor_get(v___x_6982_, 0);
                        lean_inc(v_a_6983_);
                        lean_dec_ref_known(v___x_6982_, 1);
                        v___x_6984_ = lean_ptr_addr(v_struct_6981_);
                        v___x_6985_ = lean_ptr_addr(v_a_6983_);
                        v___x_6986_ = lean_usize_dec_eq(v___x_6984_, v___x_6985_);
                        if v___x_6986_ == 0 {
                            lean_inc(v_idx_6980_);
                            lean_inc(v_typeName_6979_);
                            lean_dec_ref_known(v___y_6956_, 3);
                            v___x_6987_ = l_Lean_Expr_proj___override(
                                v_typeName_6979_,
                                v_idx_6980_,
                                v_a_6983_,
                            );
                            v___x_6988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___x_6987_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6988_;
                        } else {
                            lean_dec(v_a_6983_);
                            v___x_6989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_6936_, v_post_6938_, v_usedLetOnly_6939_, v_skipConstInApp_6940_, v_skipInstances_6941_, v___y_6956_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
                            return v___x_6989_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_6956_, 3);
                        lean_dec_ref(v_post_6938_);
                        lean_dec_ref(v_pre_6936_);
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
                    v_reuseFailAlloc_7006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_a_7000_);
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
                    v_reuseFailAlloc_7014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_a_7008_);
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
    mut v___x_7016_: *mut LeanObject,
    mut v_pre_7017_: *mut LeanObject,
    mut v_e_7018_: *mut LeanObject,
    mut v_post_7019_: *mut LeanObject,
    mut v_usedLetOnly_7020_: *mut LeanObject,
    mut v_skipConstInApp_7021_: *mut LeanObject,
    mut v_skipInstances_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
    mut v___y_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7030_: u8 = 0;
    let mut v_skipConstInApp_boxed_7031_: u8 = 0;
    let mut v_skipInstances_boxed_7032_: u8 = 0;
    let mut v_res_7033_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7030_ = (lean_unbox(v_usedLetOnly_7020_) as u8);
    v_skipConstInApp_boxed_7031_ = (lean_unbox(v_skipConstInApp_7021_) as u8);
    v_skipInstances_boxed_7032_ = (lean_unbox(v_skipInstances_7022_) as u8);
    v_res_7033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_7016_, v_pre_7017_, v_e_7018_, v_post_7019_, v_usedLetOnly_boxed_7030_, v_skipConstInApp_boxed_7031_, v_skipInstances_boxed_7032_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_);
    lean_dec(v___y_7028_);
    lean_dec_ref(v___y_7027_);
    lean_dec(v___y_7026_);
    lean_dec_ref(v___y_7025_);
    lean_dec(v___y_7024_);
    lean_dec(v___y_7023_);
    return v_res_7033_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(
    mut v_pre_7034_: *mut LeanObject,
    mut v_post_7035_: *mut LeanObject,
    mut v_usedLetOnly_7036_: u8,
    mut v_skipConstInApp_7037_: u8,
    mut v_skipInstances_7038_: u8,
    mut v_e_7039_: *mut LeanObject,
    mut v_a_7040_: *mut LeanObject,
    mut v___y_7041_: *mut LeanObject,
    mut v___y_7042_: *mut LeanObject,
    mut v___y_7043_: *mut LeanObject,
    mut v___y_7044_: *mut LeanObject,
    mut v___y_7045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7052_: u8 = 0;
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7065_: u8 = 0;
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7069_: u8 = 0;
    let mut v_unused_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7074_: u8 = 0;
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut v_val_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut v_a_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7087_: u8 = 0;
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_7040_);
                v___x_7047_ =
                    lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_7047_, 0, lean_box(0));
                lean_closure_set(v___x_7047_, 1, lean_box(0));
                lean_closure_set(v___x_7047_, 2, v_a_7040_);
                v___x_7048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_7047_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                if lean_obj_tag(v___x_7048_) == 0 {
                    v_a_7049_ = lean_ctor_get(v___x_7048_, 0);
                    v_isSharedCheck_7083_ = (!lean_is_exclusive(v___x_7048_)) as u8;
                    if v_isSharedCheck_7083_ == 0 {
                        v___x_7051_ = v___x_7048_;
                        v_isShared_7052_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7049_);
                        lean_dec(v___x_7048_);
                        v___x_7051_ = lean_box(0);
                        v_isShared_7052_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_7039_);
                    lean_dec_ref(v_post_7035_);
                    lean_dec_ref(v_pre_7034_);
                    v_a_7084_ = lean_ctor_get(v___x_7048_, 0);
                    v_isSharedCheck_7091_ = (!lean_is_exclusive(v___x_7048_)) as u8;
                    if v_isSharedCheck_7091_ == 0 {
                        v___x_7086_ = v___x_7048_;
                        v_isShared_7087_ = v_isSharedCheck_7091_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7084_);
                        lean_dec(v___x_7048_);
                        v___x_7086_ = lean_box(0);
                        v_isShared_7087_ = v_isSharedCheck_7091_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_7049_, v_e_7039_);
                lean_dec(v_a_7049_);
                if lean_obj_tag(v___x_7053_) == 0 {
                    lean_del_object(v___x_7051_);
                    v___x_7054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0;
                    v___x_7055_ = lean_box((v_usedLetOnly_7036_) as usize);
                    v___x_7056_ = lean_box((v_skipConstInApp_7037_) as usize);
                    v___x_7057_ = lean_box((v_skipInstances_7038_) as usize);
                    lean_inc_ref(v_e_7039_);
                    v___f_7058_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
                    lean_closure_set(v___f_7058_, 0, v___x_7054_);
                    lean_closure_set(v___f_7058_, 1, v_pre_7034_);
                    lean_closure_set(v___f_7058_, 2, v_e_7039_);
                    lean_closure_set(v___f_7058_, 3, v_post_7035_);
                    lean_closure_set(v___f_7058_, 4, v___x_7055_);
                    lean_closure_set(v___f_7058_, 5, v___x_7056_);
                    lean_closure_set(v___f_7058_, 6, v___x_7057_);
                    v___x_7059_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_7058_, v_a_7040_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                    if lean_obj_tag(v___x_7059_) == 0 {
                        v_a_7060_ = lean_ctor_get(v___x_7059_, 0);
                        lean_inc_n(v_a_7060_, 2);
                        lean_dec_ref_known(v___x_7059_, 1);
                        lean_inc(v_a_7040_);
                        v___f_7061_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_7061_, 0, v_a_7040_);
                        lean_closure_set(v___f_7061_, 1, v_e_7039_);
                        lean_closure_set(v___f_7061_, 2, v_a_7060_);
                        v___x_7062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_7061_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
                        if lean_obj_tag(v___x_7062_) == 0 {
                            v_isSharedCheck_7069_ = (!lean_is_exclusive(v___x_7062_)) as u8;
                            if v_isSharedCheck_7069_ == 0 {
                                v_unused_7070_ = lean_ctor_get(v___x_7062_, 0);
                                lean_dec(v_unused_7070_);
                                v___x_7064_ = v___x_7062_;
                                v_isShared_7065_ = v_isSharedCheck_7069_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_7062_);
                                v___x_7064_ = lean_box(0);
                                v_isShared_7065_ = v_isSharedCheck_7069_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_7060_);
                            v_a_7071_ = lean_ctor_get(v___x_7062_, 0);
                            v_isSharedCheck_7078_ = (!lean_is_exclusive(v___x_7062_)) as u8;
                            if v_isSharedCheck_7078_ == 0 {
                                v___x_7073_ = v___x_7062_;
                                v_isShared_7074_ = v_isSharedCheck_7078_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7071_);
                                lean_dec(v___x_7062_);
                                v___x_7073_ = lean_box(0);
                                v_isShared_7074_ = v_isSharedCheck_7078_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_7039_);
                        return v___x_7059_;
                    }
                } else {
                    lean_dec_ref(v_e_7039_);
                    lean_dec_ref(v_post_7035_);
                    lean_dec_ref(v_pre_7034_);
                    v_val_7079_ = lean_ctor_get(v___x_7053_, 0);
                    lean_inc(v_val_7079_);
                    lean_dec_ref_known(v___x_7053_, 1);
                    if v_isShared_7052_ == 0 {
                        lean_ctor_set(v___x_7051_, 0, v_val_7079_);
                        v___x_7081_ = v___x_7051_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7082_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_val_7079_);
                        v___x_7081_ = v_reuseFailAlloc_7082_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7065_ == 0 {
                    lean_ctor_set(v___x_7064_, 0, v_a_7060_);
                    v___x_7067_ = v___x_7064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7068_, 0, v_a_7060_);
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
                    v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_a_7071_);
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
                    v_reuseFailAlloc_7090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7090_, 0, v_a_7084_);
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
    mut v_fvars_7092_: *mut LeanObject,
    mut v_pre_7093_: *mut LeanObject,
    mut v_post_7094_: *mut LeanObject,
    mut v_usedLetOnly_7095_: *mut LeanObject,
    mut v_skipConstInApp_7096_: *mut LeanObject,
    mut v_skipInstances_7097_: *mut LeanObject,
    mut v_body_7098_: *mut LeanObject,
    mut v_x_7099_: *mut LeanObject,
    mut v___y_7100_: *mut LeanObject,
    mut v___y_7101_: *mut LeanObject,
    mut v___y_7102_: *mut LeanObject,
    mut v___y_7103_: *mut LeanObject,
    mut v___y_7104_: *mut LeanObject,
    mut v___y_7105_: *mut LeanObject,
    mut v___y_7106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7107_: u8 = 0;
    let mut v_skipConstInApp_boxed_7108_: u8 = 0;
    let mut v_skipInstances_boxed_7109_: u8 = 0;
    let mut v_res_7110_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7107_ = (lean_unbox(v_usedLetOnly_7095_) as u8);
    v_skipConstInApp_boxed_7108_ = (lean_unbox(v_skipConstInApp_7096_) as u8);
    v_skipInstances_boxed_7109_ = (lean_unbox(v_skipInstances_7097_) as u8);
    v_res_7110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_7092_, v_pre_7093_, v_post_7094_, v_usedLetOnly_boxed_7107_, v_skipConstInApp_boxed_7108_, v_skipInstances_boxed_7109_, v_body_7098_, v_x_7099_, v___y_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_, v___y_7105_);
    lean_dec(v___y_7105_);
    lean_dec_ref(v___y_7104_);
    lean_dec(v___y_7103_);
    lean_dec_ref(v___y_7102_);
    lean_dec(v___y_7101_);
    lean_dec(v___y_7100_);
    return v_res_7110_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(
    mut v_pre_7111_: *mut LeanObject,
    mut v_post_7112_: *mut LeanObject,
    mut v_usedLetOnly_7113_: u8,
    mut v_skipConstInApp_7114_: u8,
    mut v_skipInstances_7115_: u8,
    mut v_fvars_7116_: *mut LeanObject,
    mut v_e_7117_: *mut LeanObject,
    mut v_a_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_7117_) == 7 {
        let mut v_binderName_7125_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_7126_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_7127_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7128_: u8 = 0;
        let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_7125_ = lean_ctor_get(v_e_7117_, 0);
        lean_inc(v_binderName_7125_);
        v_binderType_7126_ = lean_ctor_get(v_e_7117_, 1);
        lean_inc_ref(v_binderType_7126_);
        v_body_7127_ = lean_ctor_get(v_e_7117_, 2);
        lean_inc_ref(v_body_7127_);
        v_binderInfo_7128_ = lean_ctor_get_uint8(
            v_e_7117_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_7117_, 3);
        v___x_7129_ = lean_expr_instantiate_rev(v_binderType_7126_, v_fvars_7116_);
        lean_dec_ref(v_binderType_7126_);
        lean_inc_ref(v_post_7112_);
        lean_inc_ref(v_pre_7111_);
        v___x_7130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v___x_7129_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
        if lean_obj_tag(v___x_7130_) == 0 {
            let mut v_a_7131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_7135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7136_: u8 = 0;
            let mut v___x_7137_: *mut LeanObject = core::ptr::null_mut();
            v_a_7131_ = lean_ctor_get(v___x_7130_, 0);
            lean_inc(v_a_7131_);
            lean_dec_ref_known(v___x_7130_, 1);
            v___x_7132_ = lean_box((v_usedLetOnly_7113_) as usize);
            v___x_7133_ = lean_box((v_skipConstInApp_7114_) as usize);
            v___x_7134_ = lean_box((v_skipInstances_7115_) as usize);
            v___f_7135_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
            lean_closure_set(v___f_7135_, 0, v_fvars_7116_);
            lean_closure_set(v___f_7135_, 1, v_pre_7111_);
            lean_closure_set(v___f_7135_, 2, v_post_7112_);
            lean_closure_set(v___f_7135_, 3, v___x_7132_);
            lean_closure_set(v___f_7135_, 4, v___x_7133_);
            lean_closure_set(v___f_7135_, 5, v___x_7134_);
            lean_closure_set(v___f_7135_, 6, v_body_7127_);
            v___x_7136_ = 0;
            v___x_7137_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_7125_, v_binderInfo_7128_, v_a_7131_, v___f_7135_, v___x_7136_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
            return v___x_7137_;
        } else {
            lean_dec_ref(v_body_7127_);
            lean_dec(v_binderName_7125_);
            lean_dec_ref(v_fvars_7116_);
            lean_dec_ref(v_post_7112_);
            lean_dec_ref(v_pre_7111_);
            return v___x_7130_;
        }
    } else {
        let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
        v___x_7138_ = lean_expr_instantiate_rev(v_e_7117_, v_fvars_7116_);
        lean_dec_ref(v_e_7117_);
        lean_inc_ref(v_post_7112_);
        lean_inc_ref(v_pre_7111_);
        v___x_7139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v___x_7138_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
        if lean_obj_tag(v___x_7139_) == 0 {
            let mut v_a_7140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7141_: u8 = 0;
            let mut v___x_7142_: u8 = 0;
            let mut v___x_7143_: u8 = 0;
            let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
            v_a_7140_ = lean_ctor_get(v___x_7139_, 0);
            lean_inc(v_a_7140_);
            lean_dec_ref_known(v___x_7139_, 1);
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
            lean_dec_ref(v_fvars_7116_);
            if lean_obj_tag(v___x_7144_) == 0 {
                let mut v_a_7145_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
                v_a_7145_ = lean_ctor_get(v___x_7144_, 0);
                lean_inc(v_a_7145_);
                lean_dec_ref_known(v___x_7144_, 1);
                v___x_7146_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_7111_, v_post_7112_, v_usedLetOnly_7113_, v_skipConstInApp_7114_, v_skipInstances_7115_, v_a_7145_, v_a_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
                return v___x_7146_;
            } else {
                lean_dec_ref(v_post_7112_);
                lean_dec_ref(v_pre_7111_);
                return v___x_7144_;
            }
        } else {
            lean_dec_ref(v_fvars_7116_);
            lean_dec_ref(v_post_7112_);
            lean_dec_ref(v_pre_7111_);
            return v___x_7139_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(
    mut v_fvars_7147_: *mut LeanObject,
    mut v_pre_7148_: *mut LeanObject,
    mut v_post_7149_: *mut LeanObject,
    mut v_usedLetOnly_7150_: u8,
    mut v_skipConstInApp_7151_: u8,
    mut v_skipInstances_7152_: u8,
    mut v_body_7153_: *mut LeanObject,
    mut v_x_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
    mut v___y_7157_: *mut LeanObject,
    mut v___y_7158_: *mut LeanObject,
    mut v___y_7159_: *mut LeanObject,
    mut v___y_7160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    v___x_7162_ = lean_array_push(v_fvars_7147_, v_x_7154_);
    v___x_7163_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_7148_, v_post_7149_, v_usedLetOnly_7150_, v_skipConstInApp_7151_, v_skipInstances_7152_, v___x_7162_, v_body_7153_, v___y_7155_, v___y_7156_, v___y_7157_, v___y_7158_, v___y_7159_, v___y_7160_);
    return v___x_7163_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(
    mut v_pre_7164_: *mut LeanObject,
    mut v_post_7165_: *mut LeanObject,
    mut v_usedLetOnly_7166_: *mut LeanObject,
    mut v_skipConstInApp_7167_: *mut LeanObject,
    mut v_skipInstances_7168_: *mut LeanObject,
    mut v_e_7169_: *mut LeanObject,
    mut v_a_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
    mut v___y_7172_: *mut LeanObject,
    mut v___y_7173_: *mut LeanObject,
    mut v___y_7174_: *mut LeanObject,
    mut v___y_7175_: *mut LeanObject,
    mut v___y_7176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7177_: u8 = 0;
    let mut v_skipConstInApp_boxed_7178_: u8 = 0;
    let mut v_skipInstances_boxed_7179_: u8 = 0;
    let mut v_res_7180_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7177_ = (lean_unbox(v_usedLetOnly_7166_) as u8);
    v_skipConstInApp_boxed_7178_ = (lean_unbox(v_skipConstInApp_7167_) as u8);
    v_skipInstances_boxed_7179_ = (lean_unbox(v_skipInstances_7168_) as u8);
    v_res_7180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_7164_, v_post_7165_, v_usedLetOnly_boxed_7177_, v_skipConstInApp_boxed_7178_, v_skipInstances_boxed_7179_, v_e_7169_, v_a_7170_, v___y_7171_, v___y_7172_, v___y_7173_, v___y_7174_, v___y_7175_);
    lean_dec(v___y_7175_);
    lean_dec_ref(v___y_7174_);
    lean_dec(v___y_7173_);
    lean_dec_ref(v___y_7172_);
    lean_dec(v___y_7171_);
    lean_dec(v_a_7170_);
    return v_res_7180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(
    mut v_pre_7181_: *mut LeanObject,
    mut v_post_7182_: *mut LeanObject,
    mut v_usedLetOnly_7183_: *mut LeanObject,
    mut v_skipConstInApp_7184_: *mut LeanObject,
    mut v_skipInstances_7185_: *mut LeanObject,
    mut v_sz_7186_: *mut LeanObject,
    mut v_i_7187_: *mut LeanObject,
    mut v_bs_7188_: *mut LeanObject,
    mut v___y_7189_: *mut LeanObject,
    mut v___y_7190_: *mut LeanObject,
    mut v___y_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7196_: u8 = 0;
    let mut v_skipConstInApp_boxed_7197_: u8 = 0;
    let mut v_skipInstances_boxed_7198_: u8 = 0;
    let mut v_sz_boxed_7199_: usize = 0;
    let mut v_i_boxed_7200_: usize = 0;
    let mut v_res_7201_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7196_ = (lean_unbox(v_usedLetOnly_7183_) as u8);
    v_skipConstInApp_boxed_7197_ = (lean_unbox(v_skipConstInApp_7184_) as u8);
    v_skipInstances_boxed_7198_ = (lean_unbox(v_skipInstances_7185_) as u8);
    v_sz_boxed_7199_ = lean_unbox_usize(v_sz_7186_);
    lean_dec(v_sz_7186_);
    v_i_boxed_7200_ = lean_unbox_usize(v_i_7187_);
    lean_dec(v_i_7187_);
    v_res_7201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_7181_, v_post_7182_, v_usedLetOnly_boxed_7196_, v_skipConstInApp_boxed_7197_, v_skipInstances_boxed_7198_, v_sz_boxed_7199_, v_i_boxed_7200_, v_bs_7188_, v___y_7189_, v___y_7190_, v___y_7191_, v___y_7192_, v___y_7193_, v___y_7194_);
    lean_dec(v___y_7194_);
    lean_dec_ref(v___y_7193_);
    lean_dec(v___y_7192_);
    lean_dec_ref(v___y_7191_);
    lean_dec(v___y_7190_);
    lean_dec(v___y_7189_);
    return v_res_7201_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(
    mut v_pre_7202_: *mut LeanObject,
    mut v_post_7203_: *mut LeanObject,
    mut v_usedLetOnly_7204_: *mut LeanObject,
    mut v_skipConstInApp_7205_: *mut LeanObject,
    mut v_skipInstances_7206_: *mut LeanObject,
    mut v_e_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
    mut v___y_7209_: *mut LeanObject,
    mut v___y_7210_: *mut LeanObject,
    mut v___y_7211_: *mut LeanObject,
    mut v___y_7212_: *mut LeanObject,
    mut v___y_7213_: *mut LeanObject,
    mut v___y_7214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7215_: u8 = 0;
    let mut v_skipConstInApp_boxed_7216_: u8 = 0;
    let mut v_skipInstances_boxed_7217_: u8 = 0;
    let mut v_res_7218_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7215_ = (lean_unbox(v_usedLetOnly_7204_) as u8);
    v_skipConstInApp_boxed_7216_ = (lean_unbox(v_skipConstInApp_7205_) as u8);
    v_skipInstances_boxed_7217_ = (lean_unbox(v_skipInstances_7206_) as u8);
    v_res_7218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7202_, v_post_7203_, v_usedLetOnly_boxed_7215_, v_skipConstInApp_boxed_7216_, v_skipInstances_boxed_7217_, v_e_7207_, v_a_7208_, v___y_7209_, v___y_7210_, v___y_7211_, v___y_7212_, v___y_7213_);
    lean_dec(v___y_7213_);
    lean_dec_ref(v___y_7212_);
    lean_dec(v___y_7211_);
    lean_dec_ref(v___y_7210_);
    lean_dec(v___y_7209_);
    lean_dec(v_a_7208_);
    return v_res_7218_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(
    mut v_pre_7219_: *mut LeanObject,
    mut v_post_7220_: *mut LeanObject,
    mut v_usedLetOnly_7221_: *mut LeanObject,
    mut v_skipConstInApp_7222_: *mut LeanObject,
    mut v_skipInstances_7223_: *mut LeanObject,
    mut v_fvars_7224_: *mut LeanObject,
    mut v_e_7225_: *mut LeanObject,
    mut v_a_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
    mut v___y_7228_: *mut LeanObject,
    mut v___y_7229_: *mut LeanObject,
    mut v___y_7230_: *mut LeanObject,
    mut v___y_7231_: *mut LeanObject,
    mut v___y_7232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7233_: u8 = 0;
    let mut v_skipConstInApp_boxed_7234_: u8 = 0;
    let mut v_skipInstances_boxed_7235_: u8 = 0;
    let mut v_res_7236_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7233_ = (lean_unbox(v_usedLetOnly_7221_) as u8);
    v_skipConstInApp_boxed_7234_ = (lean_unbox(v_skipConstInApp_7222_) as u8);
    v_skipInstances_boxed_7235_ = (lean_unbox(v_skipInstances_7223_) as u8);
    v_res_7236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_7219_, v_post_7220_, v_usedLetOnly_boxed_7233_, v_skipConstInApp_boxed_7234_, v_skipInstances_boxed_7235_, v_fvars_7224_, v_e_7225_, v_a_7226_, v___y_7227_, v___y_7228_, v___y_7229_, v___y_7230_, v___y_7231_);
    lean_dec(v___y_7231_);
    lean_dec_ref(v___y_7230_);
    lean_dec(v___y_7229_);
    lean_dec_ref(v___y_7228_);
    lean_dec(v___y_7227_);
    lean_dec(v_a_7226_);
    return v_res_7236_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(
    mut v_pre_7237_: *mut LeanObject,
    mut v_post_7238_: *mut LeanObject,
    mut v_usedLetOnly_7239_: *mut LeanObject,
    mut v_skipConstInApp_7240_: *mut LeanObject,
    mut v_skipInstances_7241_: *mut LeanObject,
    mut v_fvars_7242_: *mut LeanObject,
    mut v_e_7243_: *mut LeanObject,
    mut v_a_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
    mut v___y_7246_: *mut LeanObject,
    mut v___y_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
    mut v___y_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7251_: u8 = 0;
    let mut v_skipConstInApp_boxed_7252_: u8 = 0;
    let mut v_skipInstances_boxed_7253_: u8 = 0;
    let mut v_res_7254_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7251_ = (lean_unbox(v_usedLetOnly_7239_) as u8);
    v_skipConstInApp_boxed_7252_ = (lean_unbox(v_skipConstInApp_7240_) as u8);
    v_skipInstances_boxed_7253_ = (lean_unbox(v_skipInstances_7241_) as u8);
    v_res_7254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_7237_, v_post_7238_, v_usedLetOnly_boxed_7251_, v_skipConstInApp_boxed_7252_, v_skipInstances_boxed_7253_, v_fvars_7242_, v_e_7243_, v_a_7244_, v___y_7245_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_);
    lean_dec(v___y_7249_);
    lean_dec_ref(v___y_7248_);
    lean_dec(v___y_7247_);
    lean_dec_ref(v___y_7246_);
    lean_dec(v___y_7245_);
    lean_dec(v_a_7244_);
    return v_res_7254_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(
    mut v_pre_7255_: *mut LeanObject,
    mut v_post_7256_: *mut LeanObject,
    mut v_usedLetOnly_7257_: *mut LeanObject,
    mut v_skipConstInApp_7258_: *mut LeanObject,
    mut v_skipInstances_7259_: *mut LeanObject,
    mut v_fvars_7260_: *mut LeanObject,
    mut v_e_7261_: *mut LeanObject,
    mut v_a_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
    mut v___y_7266_: *mut LeanObject,
    mut v___y_7267_: *mut LeanObject,
    mut v___y_7268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7269_: u8 = 0;
    let mut v_skipConstInApp_boxed_7270_: u8 = 0;
    let mut v_skipInstances_boxed_7271_: u8 = 0;
    let mut v_res_7272_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7269_ = (lean_unbox(v_usedLetOnly_7257_) as u8);
    v_skipConstInApp_boxed_7270_ = (lean_unbox(v_skipConstInApp_7258_) as u8);
    v_skipInstances_boxed_7271_ = (lean_unbox(v_skipInstances_7259_) as u8);
    v_res_7272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_7255_, v_post_7256_, v_usedLetOnly_boxed_7269_, v_skipConstInApp_boxed_7270_, v_skipInstances_boxed_7271_, v_fvars_7260_, v_e_7261_, v_a_7262_, v___y_7263_, v___y_7264_, v___y_7265_, v___y_7266_, v___y_7267_);
    lean_dec(v___y_7267_);
    lean_dec_ref(v___y_7266_);
    lean_dec(v___y_7265_);
    lean_dec_ref(v___y_7264_);
    lean_dec(v___y_7263_);
    lean_dec(v_a_7262_);
    return v_res_7272_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_upperBound_7273_: *mut LeanObject,
    mut v___x_7274_: *mut LeanObject,
    mut v_pre_7275_: *mut LeanObject,
    mut v_post_7276_: *mut LeanObject,
    mut v_usedLetOnly_7277_: *mut LeanObject,
    mut v_skipConstInApp_7278_: *mut LeanObject,
    mut v_skipInstances_7279_: *mut LeanObject,
    mut v_a_7280_: *mut LeanObject,
    mut v_b_7281_: *mut LeanObject,
    mut v___y_7282_: *mut LeanObject,
    mut v___y_7283_: *mut LeanObject,
    mut v___y_7284_: *mut LeanObject,
    mut v___y_7285_: *mut LeanObject,
    mut v___y_7286_: *mut LeanObject,
    mut v___y_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7289_: u8 = 0;
    let mut v_skipConstInApp_boxed_7290_: u8 = 0;
    let mut v_skipInstances_boxed_7291_: u8 = 0;
    let mut v_res_7292_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7289_ = (lean_unbox(v_usedLetOnly_7277_) as u8);
    v_skipConstInApp_boxed_7290_ = (lean_unbox(v_skipConstInApp_7278_) as u8);
    v_skipInstances_boxed_7291_ = (lean_unbox(v_skipInstances_7279_) as u8);
    v_res_7292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_7273_, v___x_7274_, v_pre_7275_, v_post_7276_, v_usedLetOnly_boxed_7289_, v_skipConstInApp_boxed_7290_, v_skipInstances_boxed_7291_, v_a_7280_, v_b_7281_, v___y_7282_, v___y_7283_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_);
    lean_dec(v___y_7287_);
    lean_dec_ref(v___y_7286_);
    lean_dec(v___y_7285_);
    lean_dec_ref(v___y_7284_);
    lean_dec(v___y_7283_);
    lean_dec(v___y_7282_);
    lean_dec_ref(v___x_7274_);
    lean_dec(v_upperBound_7273_);
    return v_res_7292_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(
    mut v_skipInstances_7293_: *mut LeanObject,
    mut v_pre_7294_: *mut LeanObject,
    mut v_post_7295_: *mut LeanObject,
    mut v_usedLetOnly_7296_: *mut LeanObject,
    mut v_skipConstInApp_7297_: *mut LeanObject,
    mut v_x_7298_: *mut LeanObject,
    mut v_x_7299_: *mut LeanObject,
    mut v_x_7300_: *mut LeanObject,
    mut v___y_7301_: *mut LeanObject,
    mut v___y_7302_: *mut LeanObject,
    mut v___y_7303_: *mut LeanObject,
    mut v___y_7304_: *mut LeanObject,
    mut v___y_7305_: *mut LeanObject,
    mut v___y_7306_: *mut LeanObject,
    mut v___y_7307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipInstances_boxed_7308_: u8 = 0;
    let mut v_usedLetOnly_boxed_7309_: u8 = 0;
    let mut v_skipConstInApp_boxed_7310_: u8 = 0;
    let mut v_res_7311_: *mut LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7308_ = (lean_unbox(v_skipInstances_7293_) as u8);
    v_usedLetOnly_boxed_7309_ = (lean_unbox(v_usedLetOnly_7296_) as u8);
    v_skipConstInApp_boxed_7310_ = (lean_unbox(v_skipConstInApp_7297_) as u8);
    v_res_7311_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_7308_, v_pre_7294_, v_post_7295_, v_usedLetOnly_boxed_7309_, v_skipConstInApp_boxed_7310_, v_x_7298_, v_x_7299_, v_x_7300_, v___y_7301_, v___y_7302_, v___y_7303_, v___y_7304_, v___y_7305_, v___y_7306_);
    lean_dec(v___y_7306_);
    lean_dec_ref(v___y_7305_);
    lean_dec(v___y_7304_);
    lean_dec_ref(v___y_7303_);
    lean_dec(v___y_7302_);
    lean_dec(v___y_7301_);
    return v_res_7311_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(
    mut v_00_u03b1_7312_: *mut LeanObject,
    mut v_x_7313_: *mut LeanObject,
    mut v___y_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
    mut v___y_7316_: *mut LeanObject,
    mut v___y_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    v___x_7320_ = lean_apply_1(v_x_7313_, lean_box(0));
    v___x_7321_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7321_, 0, v___x_7320_);
    return v___x_7321_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(
    mut v_00_u03b1_7322_: *mut LeanObject,
    mut v_x_7323_: *mut LeanObject,
    mut v___y_7324_: *mut LeanObject,
    mut v___y_7325_: *mut LeanObject,
    mut v___y_7326_: *mut LeanObject,
    mut v___y_7327_: *mut LeanObject,
    mut v___y_7328_: *mut LeanObject,
    mut v___y_7329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7330_: *mut LeanObject = core::ptr::null_mut();
    v_res_7330_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(
        v_00_u03b1_7322_,
        v_x_7323_,
        v___y_7324_,
        v___y_7325_,
        v___y_7326_,
        v___y_7327_,
        v___y_7328_,
    );
    lean_dec(v___y_7328_);
    lean_dec_ref(v___y_7327_);
    lean_dec(v___y_7326_);
    lean_dec_ref(v___y_7325_);
    lean_dec(v___y_7324_);
    return v_res_7330_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
    v___x_7331_ = lean_box(0);
    v___x_7332_ = lean_unsigned_to_nat(16);
    v___x_7333_ = lean_mk_array(v___x_7332_, v___x_7331_);
    return v___x_7333_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    v___x_7334_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
    v___x_7335_ = lean_unsigned_to_nat(0);
    v___x_7336_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7336_, 0, v___x_7335_);
    lean_ctor_set(v___x_7336_, 1, v___x_7334_);
    return v___x_7336_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    v___x_7337_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
    v___x_7338_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7338_, 0, lean_box(0));
    lean_closure_set(v___x_7338_, 1, lean_box(0));
    lean_closure_set(v___x_7338_, 2, v___x_7337_);
    return v___x_7338_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(
    mut v_input_7339_: *mut LeanObject,
    mut v_pre_7340_: *mut LeanObject,
    mut v_post_7341_: *mut LeanObject,
    mut v_usedLetOnly_7342_: u8,
    mut v_skipConstInApp_7343_: u8,
    mut v___y_7344_: *mut LeanObject,
    mut v___y_7345_: *mut LeanObject,
    mut v___y_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
    mut v___y_7348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: u8 = 0;
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7360_: u8 = 0;
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7364_: u8 = 0;
    let mut v_unused_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7350_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
                v___x_7351_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_7350_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                v_a_7352_ = lean_ctor_get(v___x_7351_, 0);
                lean_inc(v_a_7352_);
                lean_dec_ref(v___x_7351_);
                v___x_7353_ = 0;
                v___x_7354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_7340_, v_post_7341_, v_usedLetOnly_7342_, v_skipConstInApp_7343_, v___x_7353_, v_input_7339_, v_a_7352_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                if lean_obj_tag(v___x_7354_) == 0 {
                    v_a_7355_ = lean_ctor_get(v___x_7354_, 0);
                    lean_inc(v_a_7355_);
                    lean_dec_ref_known(v___x_7354_, 1);
                    v___x_7356_ = lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_7356_, 0, lean_box(0));
                    lean_closure_set(v___x_7356_, 1, lean_box(0));
                    lean_closure_set(v___x_7356_, 2, v_a_7352_);
                    v___x_7357_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_7356_, v___y_7344_, v___y_7345_, v___y_7346_, v___y_7347_, v___y_7348_);
                    v_isSharedCheck_7364_ = (!lean_is_exclusive(v___x_7357_)) as u8;
                    if v_isSharedCheck_7364_ == 0 {
                        v_unused_7365_ = lean_ctor_get(v___x_7357_, 0);
                        lean_dec(v_unused_7365_);
                        v___x_7359_ = v___x_7357_;
                        v_isShared_7360_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7357_);
                        v___x_7359_ = lean_box(0);
                        v_isShared_7360_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7352_);
                    return v___x_7354_;
                }
            }
            1 => {
                if v_isShared_7360_ == 0 {
                    lean_ctor_set(v___x_7359_, 0, v_a_7355_);
                    v___x_7362_ = v___x_7359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7363_, 0, v_a_7355_);
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
    mut v_input_7366_: *mut LeanObject,
    mut v_pre_7367_: *mut LeanObject,
    mut v_post_7368_: *mut LeanObject,
    mut v_usedLetOnly_7369_: *mut LeanObject,
    mut v_skipConstInApp_7370_: *mut LeanObject,
    mut v___y_7371_: *mut LeanObject,
    mut v___y_7372_: *mut LeanObject,
    mut v___y_7373_: *mut LeanObject,
    mut v___y_7374_: *mut LeanObject,
    mut v___y_7375_: *mut LeanObject,
    mut v___y_7376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_7377_: u8 = 0;
    let mut v_skipConstInApp_boxed_7378_: u8 = 0;
    let mut v_res_7379_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7377_ = (lean_unbox(v_usedLetOnly_7369_) as u8);
    v_skipConstInApp_boxed_7378_ = (lean_unbox(v_skipConstInApp_7370_) as u8);
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
    lean_dec(v___y_7375_);
    lean_dec_ref(v___y_7374_);
    lean_dec(v___y_7373_);
    lean_dec_ref(v___y_7372_);
    lean_dec(v___y_7371_);
    return v_res_7379_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLetsCore(
    mut v_e_7381_: *mut LeanObject,
    mut v_elimTrivial_7382_: u8,
    mut v_a_7383_: *mut LeanObject,
    mut v_a_7384_: *mut LeanObject,
    mut v_a_7385_: *mut LeanObject,
    mut v_a_7386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: u8 = 0;
    let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7398_: u8 = 0;
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7388_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once),
                    _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3,
                );
                v___x_7389_ = lean_st_mk_ref(v___x_7388_);
                v___x_7390_ = lean_box((v_elimTrivial_7382_) as usize);
                v_pre_7391_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed as *mut core::ffi::c_void,
                    8,
                    1,
                );
                lean_closure_set(v_pre_7391_, 0, v___x_7390_);
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
                if lean_obj_tag(v___x_7394_) == 0 {
                    v_a_7395_ = lean_ctor_get(v___x_7394_, 0);
                    v_isSharedCheck_7403_ = (!lean_is_exclusive(v___x_7394_)) as u8;
                    if v_isSharedCheck_7403_ == 0 {
                        v___x_7397_ = v___x_7394_;
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7395_);
                        lean_dec(v___x_7394_);
                        v___x_7397_ = lean_box(0);
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7389_);
                    return v___x_7394_;
                }
            }
            1 => {
                v___x_7399_ = lean_st_ref_get(v___x_7389_);
                lean_dec(v___x_7389_);
                lean_dec(v___x_7399_);
                if v_isShared_7398_ == 0 {
                    v___x_7401_ = v___x_7397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7402_, 0, v_a_7395_);
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
    mut v_e_7404_: *mut LeanObject,
    mut v_elimTrivial_7405_: *mut LeanObject,
    mut v_a_7406_: *mut LeanObject,
    mut v_a_7407_: *mut LeanObject,
    mut v_a_7408_: *mut LeanObject,
    mut v_a_7409_: *mut LeanObject,
    mut v_a_7410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_7411_: u8 = 0;
    let mut v_res_7412_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7411_ = (lean_unbox(v_elimTrivial_7405_) as u8);
    v_res_7412_ = l_Lean_Elab_Tactic_Do_elimLetsCore(
        v_e_7404_,
        v_elimTrivial_boxed_7411_,
        v_a_7406_,
        v_a_7407_,
        v_a_7408_,
        v_a_7409_,
    );
    lean_dec(v_a_7409_);
    lean_dec_ref(v_a_7408_);
    lean_dec(v_a_7407_);
    lean_dec_ref(v_a_7406_);
    return v_res_7412_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(
    mut v_upperBound_7413_: *mut LeanObject,
    mut v___x_7414_: *mut LeanObject,
    mut v_pre_7415_: *mut LeanObject,
    mut v_post_7416_: *mut LeanObject,
    mut v_usedLetOnly_7417_: u8,
    mut v_skipConstInApp_7418_: u8,
    mut v_skipInstances_7419_: u8,
    mut v___x_7420_: *mut LeanObject,
    mut v_inst_7421_: *mut LeanObject,
    mut v_R_7422_: *mut LeanObject,
    mut v_a_7423_: *mut LeanObject,
    mut v_b_7424_: *mut LeanObject,
    mut v_c_7425_: *mut LeanObject,
    mut v___y_7426_: *mut LeanObject,
    mut v___y_7427_: *mut LeanObject,
    mut v___y_7428_: *mut LeanObject,
    mut v___y_7429_: *mut LeanObject,
    mut v___y_7430_: *mut LeanObject,
    mut v___y_7431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    v___x_7433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_7413_, v___x_7414_, v_pre_7415_, v_post_7416_, v_usedLetOnly_7417_, v_skipConstInApp_7418_, v_skipInstances_7419_, v_a_7423_, v_b_7424_, v___y_7426_, v___y_7427_, v___y_7428_, v___y_7429_, v___y_7430_, v___y_7431_);
    return v___x_7433_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_7434_: *mut LeanObject = *_args.add(0);
    let mut v___x_7435_: *mut LeanObject = *_args.add(1);
    let mut v_pre_7436_: *mut LeanObject = *_args.add(2);
    let mut v_post_7437_: *mut LeanObject = *_args.add(3);
    let mut v_usedLetOnly_7438_: *mut LeanObject = *_args.add(4);
    let mut v_skipConstInApp_7439_: *mut LeanObject = *_args.add(5);
    let mut v_skipInstances_7440_: *mut LeanObject = *_args.add(6);
    let mut v___x_7441_: *mut LeanObject = *_args.add(7);
    let mut v_inst_7442_: *mut LeanObject = *_args.add(8);
    let mut v_R_7443_: *mut LeanObject = *_args.add(9);
    let mut v_a_7444_: *mut LeanObject = *_args.add(10);
    let mut v_b_7445_: *mut LeanObject = *_args.add(11);
    let mut v_c_7446_: *mut LeanObject = *_args.add(12);
    let mut v___y_7447_: *mut LeanObject = *_args.add(13);
    let mut v___y_7448_: *mut LeanObject = *_args.add(14);
    let mut v___y_7449_: *mut LeanObject = *_args.add(15);
    let mut v___y_7450_: *mut LeanObject = *_args.add(16);
    let mut v___y_7451_: *mut LeanObject = *_args.add(17);
    let mut v___y_7452_: *mut LeanObject = *_args.add(18);
    let mut v___y_7453_: *mut LeanObject = *_args.add(19);
    let mut v_usedLetOnly_boxed_7454_: u8 = 0;
    let mut v_skipConstInApp_boxed_7455_: u8 = 0;
    let mut v_skipInstances_boxed_7456_: u8 = 0;
    let mut v_res_7457_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7454_ = (lean_unbox(v_usedLetOnly_7438_) as u8);
    v_skipConstInApp_boxed_7455_ = (lean_unbox(v_skipConstInApp_7439_) as u8);
    v_skipInstances_boxed_7456_ = (lean_unbox(v_skipInstances_7440_) as u8);
    v_res_7457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_7434_, v___x_7435_, v_pre_7436_, v_post_7437_, v_usedLetOnly_boxed_7454_, v_skipConstInApp_boxed_7455_, v_skipInstances_boxed_7456_, v___x_7441_, v_inst_7442_, v_R_7443_, v_a_7444_, v_b_7445_, v_c_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_, v___y_7452_);
    lean_dec(v___y_7452_);
    lean_dec_ref(v___y_7451_);
    lean_dec(v___y_7450_);
    lean_dec_ref(v___y_7449_);
    lean_dec(v___y_7448_);
    lean_dec(v___y_7447_);
    lean_dec(v___x_7441_);
    lean_dec_ref(v___x_7435_);
    lean_dec(v_upperBound_7434_);
    return v_res_7457_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(
    mut v_00_u03b2_7458_: *mut LeanObject,
    mut v_m_7459_: *mut LeanObject,
    mut v_a_7460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    v___x_7461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_7459_, v_a_7460_);
    return v___x_7461_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_7462_: *mut LeanObject,
    mut v_m_7463_: *mut LeanObject,
    mut v_a_7464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7465_: *mut LeanObject = core::ptr::null_mut();
    v_res_7465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_7462_, v_m_7463_, v_a_7464_);
    lean_dec_ref(v_a_7464_);
    lean_dec_ref(v_m_7463_);
    return v_res_7465_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_7466_: *mut LeanObject,
    mut v_name_7467_: *mut LeanObject,
    mut v_bi_7468_: u8,
    mut v_type_7469_: *mut LeanObject,
    mut v_k_7470_: *mut LeanObject,
    mut v_kind_7471_: u8,
    mut v___y_7472_: *mut LeanObject,
    mut v___y_7473_: *mut LeanObject,
    mut v___y_7474_: *mut LeanObject,
    mut v___y_7475_: *mut LeanObject,
    mut v___y_7476_: *mut LeanObject,
    mut v___y_7477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_7467_, v_bi_7468_, v_type_7469_, v_k_7470_, v_kind_7471_, v___y_7472_, v___y_7473_, v___y_7474_, v___y_7475_, v___y_7476_, v___y_7477_);
    return v___x_7479_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_7480_: *mut LeanObject,
    mut v_name_7481_: *mut LeanObject,
    mut v_bi_7482_: *mut LeanObject,
    mut v_type_7483_: *mut LeanObject,
    mut v_k_7484_: *mut LeanObject,
    mut v_kind_7485_: *mut LeanObject,
    mut v___y_7486_: *mut LeanObject,
    mut v___y_7487_: *mut LeanObject,
    mut v___y_7488_: *mut LeanObject,
    mut v___y_7489_: *mut LeanObject,
    mut v___y_7490_: *mut LeanObject,
    mut v___y_7491_: *mut LeanObject,
    mut v___y_7492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_7493_: u8 = 0;
    let mut v_kind_boxed_7494_: u8 = 0;
    let mut v_res_7495_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_7493_ = (lean_unbox(v_bi_7482_) as u8);
    v_kind_boxed_7494_ = (lean_unbox(v_kind_7485_) as u8);
    v_res_7495_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_7480_, v_name_7481_, v_bi_boxed_7493_, v_type_7483_, v_k_7484_, v_kind_boxed_7494_, v___y_7486_, v___y_7487_, v___y_7488_, v___y_7489_, v___y_7490_, v___y_7491_);
    lean_dec(v___y_7491_);
    lean_dec_ref(v___y_7490_);
    lean_dec(v___y_7489_);
    lean_dec_ref(v___y_7488_);
    lean_dec(v___y_7487_);
    lean_dec(v___y_7486_);
    return v_res_7495_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(
    mut v_00_u03b1_7496_: *mut LeanObject,
    mut v_name_7497_: *mut LeanObject,
    mut v_type_7498_: *mut LeanObject,
    mut v_val_7499_: *mut LeanObject,
    mut v_k_7500_: *mut LeanObject,
    mut v_nondep_7501_: u8,
    mut v_kind_7502_: u8,
    mut v___y_7503_: *mut LeanObject,
    mut v___y_7504_: *mut LeanObject,
    mut v___y_7505_: *mut LeanObject,
    mut v___y_7506_: *mut LeanObject,
    mut v___y_7507_: *mut LeanObject,
    mut v___y_7508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    v___x_7510_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_7497_, v_type_7498_, v_val_7499_, v_k_7500_, v_nondep_7501_, v_kind_7502_, v___y_7503_, v___y_7504_, v___y_7505_, v___y_7506_, v___y_7507_, v___y_7508_);
    return v___x_7510_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(
    mut v_00_u03b1_7511_: *mut LeanObject,
    mut v_name_7512_: *mut LeanObject,
    mut v_type_7513_: *mut LeanObject,
    mut v_val_7514_: *mut LeanObject,
    mut v_k_7515_: *mut LeanObject,
    mut v_nondep_7516_: *mut LeanObject,
    mut v_kind_7517_: *mut LeanObject,
    mut v___y_7518_: *mut LeanObject,
    mut v___y_7519_: *mut LeanObject,
    mut v___y_7520_: *mut LeanObject,
    mut v___y_7521_: *mut LeanObject,
    mut v___y_7522_: *mut LeanObject,
    mut v___y_7523_: *mut LeanObject,
    mut v___y_7524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_7525_: u8 = 0;
    let mut v_kind_boxed_7526_: u8 = 0;
    let mut v_res_7527_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7525_ = (lean_unbox(v_nondep_7516_) as u8);
    v_kind_boxed_7526_ = (lean_unbox(v_kind_7517_) as u8);
    v_res_7527_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_7511_, v_name_7512_, v_type_7513_, v_val_7514_, v_k_7515_, v_nondep_boxed_7525_, v_kind_boxed_7526_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_, v___y_7523_);
    lean_dec(v___y_7523_);
    lean_dec_ref(v___y_7522_);
    lean_dec(v___y_7521_);
    lean_dec_ref(v___y_7520_);
    lean_dec(v___y_7519_);
    lean_dec(v___y_7518_);
    return v_res_7527_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(
    mut v_00_u03b1_7528_: *mut LeanObject,
    mut v_ref_7529_: *mut LeanObject,
    mut v___y_7530_: *mut LeanObject,
    mut v___y_7531_: *mut LeanObject,
    mut v___y_7532_: *mut LeanObject,
    mut v___y_7533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    v___x_7535_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_7529_);
    return v___x_7535_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(
    mut v_00_u03b1_7536_: *mut LeanObject,
    mut v_ref_7537_: *mut LeanObject,
    mut v___y_7538_: *mut LeanObject,
    mut v___y_7539_: *mut LeanObject,
    mut v___y_7540_: *mut LeanObject,
    mut v___y_7541_: *mut LeanObject,
    mut v___y_7542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7543_: *mut LeanObject = core::ptr::null_mut();
    v_res_7543_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_7536_, v_ref_7537_, v___y_7538_, v___y_7539_, v___y_7540_, v___y_7541_);
    lean_dec(v___y_7541_);
    lean_dec_ref(v___y_7540_);
    lean_dec(v___y_7539_);
    lean_dec_ref(v___y_7538_);
    return v_res_7543_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(
    mut v_00_u03b1_7544_: *mut LeanObject,
    mut v_x_7545_: *mut LeanObject,
    mut v___y_7546_: *mut LeanObject,
    mut v___y_7547_: *mut LeanObject,
    mut v___y_7548_: *mut LeanObject,
    mut v___y_7549_: *mut LeanObject,
    mut v___y_7550_: *mut LeanObject,
    mut v___y_7551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7553_: *mut LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
    return v___x_7553_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(
    mut v_00_u03b1_7554_: *mut LeanObject,
    mut v_x_7555_: *mut LeanObject,
    mut v___y_7556_: *mut LeanObject,
    mut v___y_7557_: *mut LeanObject,
    mut v___y_7558_: *mut LeanObject,
    mut v___y_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___y_7561_: *mut LeanObject,
    mut v___y_7562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7563_: *mut LeanObject = core::ptr::null_mut();
    v_res_7563_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_7554_, v_x_7555_, v___y_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_, v___y_7561_);
    lean_dec(v___y_7561_);
    lean_dec_ref(v___y_7560_);
    lean_dec(v___y_7559_);
    lean_dec_ref(v___y_7558_);
    lean_dec(v___y_7557_);
    lean_dec(v___y_7556_);
    return v_res_7563_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(
    mut v_00_u03b2_7564_: *mut LeanObject,
    mut v_m_7565_: *mut LeanObject,
    mut v_a_7566_: *mut LeanObject,
    mut v_b_7567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    v___x_7568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_7565_, v_a_7566_, v_b_7567_);
    return v___x_7568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(
    mut v_00_u03b2_7569_: *mut LeanObject,
    mut v_a_7570_: *mut LeanObject,
    mut v_x_7571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    v___x_7572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_7570_, v_x_7571_);
    return v___x_7572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(
    mut v_00_u03b2_7573_: *mut LeanObject,
    mut v_a_7574_: *mut LeanObject,
    mut v_x_7575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7576_: *mut LeanObject = core::ptr::null_mut();
    v_res_7576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_7573_, v_a_7574_, v_x_7575_);
    lean_dec(v_x_7575_);
    lean_dec_ref(v_a_7574_);
    return v_res_7576_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(
    mut v_00_u03b2_7577_: *mut LeanObject,
    mut v_a_7578_: *mut LeanObject,
    mut v_x_7579_: *mut LeanObject,
) -> u8 {
    let mut v___x_7580_: u8 = 0;
    v___x_7580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_7578_, v_x_7579_);
    return v___x_7580_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(
    mut v_00_u03b2_7581_: *mut LeanObject,
    mut v_a_7582_: *mut LeanObject,
    mut v_x_7583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7584_: u8 = 0;
    let mut v_r_7585_: *mut LeanObject = core::ptr::null_mut();
    v_res_7584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_7581_, v_a_7582_, v_x_7583_);
    lean_dec(v_x_7583_);
    lean_dec_ref(v_a_7582_);
    v_r_7585_ = lean_box((v_res_7584_) as usize);
    return v_r_7585_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(
    mut v_00_u03b2_7586_: *mut LeanObject,
    mut v_data_7587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    v___x_7588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_7587_);
    return v___x_7588_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(
    mut v_00_u03b2_7589_: *mut LeanObject,
    mut v_a_7590_: *mut LeanObject,
    mut v_b_7591_: *mut LeanObject,
    mut v_x_7592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
    v___x_7593_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_7590_, v_b_7591_, v_x_7592_);
    return v___x_7593_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(
    mut v_00_u03b2_7594_: *mut LeanObject,
    mut v_i_7595_: *mut LeanObject,
    mut v_source_7596_: *mut LeanObject,
    mut v_target_7597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    v___x_7598_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_7595_, v_source_7596_, v_target_7597_);
    return v___x_7598_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(
    mut v_00_u03b2_7599_: *mut LeanObject,
    mut v_x_7600_: *mut LeanObject,
    mut v_x_7601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    v___x_7602_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_7600_, v_x_7601_);
    return v___x_7602_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
    mut v_mvarId_7603_: *mut LeanObject,
    mut v_x_7604_: *mut LeanObject,
    mut v___y_7605_: *mut LeanObject,
    mut v___y_7606_: *mut LeanObject,
    mut v___y_7607_: *mut LeanObject,
    mut v___y_7608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7614_: u8 = 0;
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7618_: u8 = 0;
    let mut v_a_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7622_: u8 = 0;
    let mut v___x_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_7603_,
                    v_x_7604_,
                    v___y_7605_,
                    v___y_7606_,
                    v___y_7607_,
                    v___y_7608_,
                );
                if lean_obj_tag(v___x_7610_) == 0 {
                    v_a_7611_ = lean_ctor_get(v___x_7610_, 0);
                    v_isSharedCheck_7618_ = (!lean_is_exclusive(v___x_7610_)) as u8;
                    if v_isSharedCheck_7618_ == 0 {
                        v___x_7613_ = v___x_7610_;
                        v_isShared_7614_ = v_isSharedCheck_7618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7611_);
                        lean_dec(v___x_7610_);
                        v___x_7613_ = lean_box(0);
                        v_isShared_7614_ = v_isSharedCheck_7618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7619_ = lean_ctor_get(v___x_7610_, 0);
                    v_isSharedCheck_7626_ = (!lean_is_exclusive(v___x_7610_)) as u8;
                    if v_isSharedCheck_7626_ == 0 {
                        v___x_7621_ = v___x_7610_;
                        v_isShared_7622_ = v_isSharedCheck_7626_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7619_);
                        lean_dec(v___x_7610_);
                        v___x_7621_ = lean_box(0);
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
                    v_reuseFailAlloc_7617_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7617_, 0, v_a_7611_);
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
                    v_reuseFailAlloc_7625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7625_, 0, v_a_7619_);
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
    mut v_mvarId_7627_: *mut LeanObject,
    mut v_x_7628_: *mut LeanObject,
    mut v___y_7629_: *mut LeanObject,
    mut v___y_7630_: *mut LeanObject,
    mut v___y_7631_: *mut LeanObject,
    mut v___y_7632_: *mut LeanObject,
    mut v___y_7633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7634_: *mut LeanObject = core::ptr::null_mut();
    v_res_7634_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(
        v_mvarId_7627_,
        v_x_7628_,
        v___y_7629_,
        v___y_7630_,
        v___y_7631_,
        v___y_7632_,
    );
    lean_dec(v___y_7632_);
    lean_dec_ref(v___y_7631_);
    lean_dec(v___y_7630_);
    lean_dec_ref(v___y_7629_);
    return v_res_7634_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(
    mut v_00_u03b1_7635_: *mut LeanObject,
    mut v_mvarId_7636_: *mut LeanObject,
    mut v_x_7637_: *mut LeanObject,
    mut v___y_7638_: *mut LeanObject,
    mut v___y_7639_: *mut LeanObject,
    mut v___y_7640_: *mut LeanObject,
    mut v___y_7641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7643_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7644_: *mut LeanObject,
    mut v_mvarId_7645_: *mut LeanObject,
    mut v_x_7646_: *mut LeanObject,
    mut v___y_7647_: *mut LeanObject,
    mut v___y_7648_: *mut LeanObject,
    mut v___y_7649_: *mut LeanObject,
    mut v___y_7650_: *mut LeanObject,
    mut v___y_7651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7652_: *mut LeanObject = core::ptr::null_mut();
    v_res_7652_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(
        v_00_u03b1_7644_,
        v_mvarId_7645_,
        v_x_7646_,
        v___y_7647_,
        v___y_7648_,
        v___y_7649_,
        v___y_7650_,
    );
    lean_dec(v___y_7650_);
    lean_dec_ref(v___y_7649_);
    lean_dec(v___y_7648_);
    lean_dec_ref(v___y_7647_);
    return v_res_7652_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(
    mut v_elimTrivial_7653_: u8,
    mut v_as_7654_: *mut LeanObject,
    mut v_sz_7655_: usize,
    mut v_i_7656_: usize,
    mut v_b_7657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7659_: u8 = 0;
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7664_: u8 = 0;
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: usize = 0;
    let mut v___x_7671_: usize = 0;
    let mut v_reuseFailAlloc_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7680_: u8 = 0;
    let mut v___x_7681_: u8 = 0;
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: u8 = 0;
    let mut v___x_7690_: u8 = 0;
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7707_: u8 = 0;
    let mut v_isSharedCheck_7708_: u8 = 0;
    let mut v_unused_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7659_ = lean_usize_dec_lt(v_i_7656_, v_sz_7655_);
                if v___x_7659_ == 0 {
                    v___x_7660_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7660_, 0, v_b_7657_);
                    return v___x_7660_;
                } else {
                    v_snd_7661_ = lean_ctor_get(v_b_7657_, 1);
                    v_isSharedCheck_7708_ = (!lean_is_exclusive(v_b_7657_)) as u8;
                    if v_isSharedCheck_7708_ == 0 {
                        v_unused_7709_ = lean_ctor_get(v_b_7657_, 0);
                        lean_dec(v_unused_7709_);
                        v___x_7663_ = v_b_7657_;
                        v_isShared_7664_ = v_isSharedCheck_7708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7661_);
                        lean_dec(v_b_7657_);
                        v___x_7663_ = lean_box(0);
                        v_isShared_7664_ = v_isSharedCheck_7708_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7665_ = lean_box(0);
                v_a_7674_ = lean_array_uget_borrowed(v_as_7654_, v_i_7656_);
                if lean_obj_tag(v_a_7674_) == 0 {
                    v_a_7667_ = v_snd_7661_;
                    state = 2;
                    continue;
                } else {
                    v_val_7675_ = lean_ctor_get(v_a_7674_, 0);
                    v_fst_7676_ = lean_ctor_get(v_snd_7661_, 0);
                    v_snd_7677_ = lean_ctor_get(v_snd_7661_, 1);
                    v_isSharedCheck_7707_ = (!lean_is_exclusive(v_snd_7661_)) as u8;
                    if v_isSharedCheck_7707_ == 0 {
                        v___x_7679_ = v_snd_7661_;
                        v_isShared_7680_ = v_isSharedCheck_7707_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_7677_);
                        lean_inc(v_fst_7676_);
                        lean_dec(v_snd_7661_);
                        v___x_7679_ = lean_box(0);
                        v_isShared_7680_ = v_isSharedCheck_7707_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7664_ == 0 {
                    lean_ctor_set(v___x_7663_, 1, v_a_7667_);
                    lean_ctor_set(v___x_7663_, 0, v___x_7665_);
                    v___x_7669_ = v___x_7663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7673_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7673_, 0, v___x_7665_);
                    lean_ctor_set(v_reuseFailAlloc_7673_, 1, v_a_7667_);
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
                if lean_obj_tag(v___x_7682_) == 1 {
                    v_val_7683_ = lean_ctor_get(v___x_7682_, 0);
                    lean_inc(v_val_7683_);
                    lean_dec_ref_known(v___x_7682_, 1);
                    v___x_7684_ = l_Lean_LocalDecl_type(v_val_7675_);
                    if lean_obj_tag(v___x_7684_) == 10 {
                        v_data_7685_ = lean_ctor_get(v___x_7684_, 0);
                        lean_inc(v_data_7685_);
                        lean_dec_ref_known(v___x_7684_, 2);
                        v___x_7686_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7687_ = lean_unsigned_to_nat(2);
                        v___x_7688_ = l_Lean_KVMap_getNat(v_data_7685_, v___x_7686_, v___x_7687_);
                        lean_dec(v_data_7685_);
                        v___x_7689_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7688_);
                        lean_dec(v___x_7688_);
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
                                lean_ctor_set(v___x_7679_, 1, v___x_7694_);
                                lean_ctor_set(v___x_7679_, 0, v___x_7693_);
                                v___x_7696_ = v___x_7679_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7697_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7697_, 0, v___x_7693_);
                                lean_ctor_set(v_reuseFailAlloc_7697_, 1, v___x_7694_);
                                v___x_7696_ = v_reuseFailAlloc_7697_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_7683_);
                            if v_isShared_7680_ == 0 {
                                v___x_7699_ = v___x_7679_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7700_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7700_, 0, v_fst_7676_);
                                lean_ctor_set(v_reuseFailAlloc_7700_, 1, v_snd_7677_);
                                v___x_7699_ = v_reuseFailAlloc_7700_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7684_);
                        lean_dec(v_val_7683_);
                        if v_isShared_7680_ == 0 {
                            v___x_7702_ = v___x_7679_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7703_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7703_, 0, v_fst_7676_);
                            lean_ctor_set(v_reuseFailAlloc_7703_, 1, v_snd_7677_);
                            v___x_7702_ = v_reuseFailAlloc_7703_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7682_);
                    if v_isShared_7680_ == 0 {
                        v___x_7705_ = v___x_7679_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7706_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7706_, 0, v_fst_7676_);
                        lean_ctor_set(v_reuseFailAlloc_7706_, 1, v_snd_7677_);
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
    mut v_elimTrivial_7710_: *mut LeanObject,
    mut v_as_7711_: *mut LeanObject,
    mut v_sz_7712_: *mut LeanObject,
    mut v_i_7713_: *mut LeanObject,
    mut v_b_7714_: *mut LeanObject,
    mut v___y_7715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_7716_: u8 = 0;
    let mut v_sz_boxed_7717_: usize = 0;
    let mut v_i_boxed_7718_: usize = 0;
    let mut v_res_7719_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7716_ = (lean_unbox(v_elimTrivial_7710_) as u8);
    v_sz_boxed_7717_ = lean_unbox_usize(v_sz_7712_);
    lean_dec(v_sz_7712_);
    v_i_boxed_7718_ = lean_unbox_usize(v_i_7713_);
    lean_dec(v_i_7713_);
    v_res_7719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_7716_, v_as_7711_, v_sz_boxed_7717_, v_i_boxed_7718_, v_b_7714_);
    lean_dec_ref(v_as_7711_);
    return v_res_7719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(
    mut v_elimTrivial_7720_: u8,
    mut v_as_7721_: *mut LeanObject,
    mut v_sz_7722_: usize,
    mut v_i_7723_: usize,
    mut v_b_7724_: *mut LeanObject,
    mut v___y_7725_: *mut LeanObject,
    mut v___y_7726_: *mut LeanObject,
    mut v___y_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7730_: u8 = 0;
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7735_: u8 = 0;
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: usize = 0;
    let mut v___x_7742_: usize = 0;
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7751_: u8 = 0;
    let mut v___x_7752_: u8 = 0;
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: u8 = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7778_: u8 = 0;
    let mut v_isSharedCheck_7779_: u8 = 0;
    let mut v_unused_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7730_ = lean_usize_dec_lt(v_i_7723_, v_sz_7722_);
                if v___x_7730_ == 0 {
                    v___x_7731_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7731_, 0, v_b_7724_);
                    return v___x_7731_;
                } else {
                    v_snd_7732_ = lean_ctor_get(v_b_7724_, 1);
                    v_isSharedCheck_7779_ = (!lean_is_exclusive(v_b_7724_)) as u8;
                    if v_isSharedCheck_7779_ == 0 {
                        v_unused_7780_ = lean_ctor_get(v_b_7724_, 0);
                        lean_dec(v_unused_7780_);
                        v___x_7734_ = v_b_7724_;
                        v_isShared_7735_ = v_isSharedCheck_7779_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7732_);
                        lean_dec(v_b_7724_);
                        v___x_7734_ = lean_box(0);
                        v_isShared_7735_ = v_isSharedCheck_7779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7736_ = lean_box(0);
                v_a_7745_ = lean_array_uget_borrowed(v_as_7721_, v_i_7723_);
                if lean_obj_tag(v_a_7745_) == 0 {
                    v_a_7738_ = v_snd_7732_;
                    state = 2;
                    continue;
                } else {
                    v_val_7746_ = lean_ctor_get(v_a_7745_, 0);
                    v_fst_7747_ = lean_ctor_get(v_snd_7732_, 0);
                    v_snd_7748_ = lean_ctor_get(v_snd_7732_, 1);
                    v_isSharedCheck_7778_ = (!lean_is_exclusive(v_snd_7732_)) as u8;
                    if v_isSharedCheck_7778_ == 0 {
                        v___x_7750_ = v_snd_7732_;
                        v_isShared_7751_ = v_isSharedCheck_7778_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_7748_);
                        lean_inc(v_fst_7747_);
                        lean_dec(v_snd_7732_);
                        v___x_7750_ = lean_box(0);
                        v_isShared_7751_ = v_isSharedCheck_7778_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7735_ == 0 {
                    lean_ctor_set(v___x_7734_, 1, v_a_7738_);
                    lean_ctor_set(v___x_7734_, 0, v___x_7736_);
                    v___x_7740_ = v___x_7734_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7744_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7744_, 0, v___x_7736_);
                    lean_ctor_set(v_reuseFailAlloc_7744_, 1, v_a_7738_);
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
                if lean_obj_tag(v___x_7753_) == 1 {
                    v_val_7754_ = lean_ctor_get(v___x_7753_, 0);
                    lean_inc(v_val_7754_);
                    lean_dec_ref_known(v___x_7753_, 1);
                    v___x_7755_ = l_Lean_LocalDecl_type(v_val_7746_);
                    if lean_obj_tag(v___x_7755_) == 10 {
                        v_data_7756_ = lean_ctor_get(v___x_7755_, 0);
                        lean_inc(v_data_7756_);
                        lean_dec_ref_known(v___x_7755_, 2);
                        v___x_7757_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7758_ = lean_unsigned_to_nat(2);
                        v___x_7759_ = l_Lean_KVMap_getNat(v_data_7756_, v___x_7757_, v___x_7758_);
                        lean_dec(v_data_7756_);
                        v___x_7760_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7759_);
                        lean_dec(v___x_7759_);
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
                                lean_ctor_set(v___x_7750_, 1, v___x_7765_);
                                lean_ctor_set(v___x_7750_, 0, v___x_7764_);
                                v___x_7767_ = v___x_7750_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7768_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7768_, 0, v___x_7764_);
                                lean_ctor_set(v_reuseFailAlloc_7768_, 1, v___x_7765_);
                                v___x_7767_ = v_reuseFailAlloc_7768_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_7754_);
                            if v_isShared_7751_ == 0 {
                                v___x_7770_ = v___x_7750_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7771_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7771_, 0, v_fst_7747_);
                                lean_ctor_set(v_reuseFailAlloc_7771_, 1, v_snd_7748_);
                                v___x_7770_ = v_reuseFailAlloc_7771_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7755_);
                        lean_dec(v_val_7754_);
                        if v_isShared_7751_ == 0 {
                            v___x_7773_ = v___x_7750_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7774_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7774_, 0, v_fst_7747_);
                            lean_ctor_set(v_reuseFailAlloc_7774_, 1, v_snd_7748_);
                            v___x_7773_ = v_reuseFailAlloc_7774_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7753_);
                    if v_isShared_7751_ == 0 {
                        v___x_7776_ = v___x_7750_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7777_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7777_, 0, v_fst_7747_);
                        lean_ctor_set(v_reuseFailAlloc_7777_, 1, v_snd_7748_);
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
    mut v_elimTrivial_7781_: *mut LeanObject,
    mut v_as_7782_: *mut LeanObject,
    mut v_sz_7783_: *mut LeanObject,
    mut v_i_7784_: *mut LeanObject,
    mut v_b_7785_: *mut LeanObject,
    mut v___y_7786_: *mut LeanObject,
    mut v___y_7787_: *mut LeanObject,
    mut v___y_7788_: *mut LeanObject,
    mut v___y_7789_: *mut LeanObject,
    mut v___y_7790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_7791_: u8 = 0;
    let mut v_sz_boxed_7792_: usize = 0;
    let mut v_i_boxed_7793_: usize = 0;
    let mut v_res_7794_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7791_ = (lean_unbox(v_elimTrivial_7781_) as u8);
    v_sz_boxed_7792_ = lean_unbox_usize(v_sz_7783_);
    lean_dec(v_sz_7783_);
    v_i_boxed_7793_ = lean_unbox_usize(v_i_7784_);
    lean_dec(v_i_7784_);
    v_res_7794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_7791_, v_as_7782_, v_sz_boxed_7792_, v_i_boxed_7793_, v_b_7785_, v___y_7786_, v___y_7787_, v___y_7788_, v___y_7789_);
    lean_dec(v___y_7789_);
    lean_dec_ref(v___y_7788_);
    lean_dec(v___y_7787_);
    lean_dec_ref(v___y_7786_);
    lean_dec_ref(v_as_7782_);
    return v_res_7794_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(
    mut v_elimTrivial_7795_: u8,
    mut v_as_7796_: *mut LeanObject,
    mut v_sz_7797_: usize,
    mut v_i_7798_: usize,
    mut v_b_7799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7801_: u8 = 0;
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7806_: u8 = 0;
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: usize = 0;
    let mut v___x_7813_: usize = 0;
    let mut v_reuseFailAlloc_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7822_: u8 = 0;
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: u8 = 0;
    let mut v___x_7832_: u8 = 0;
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7849_: u8 = 0;
    let mut v_isSharedCheck_7850_: u8 = 0;
    let mut v_unused_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7801_ = lean_usize_dec_lt(v_i_7798_, v_sz_7797_);
                if v___x_7801_ == 0 {
                    v___x_7802_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7802_, 0, v_b_7799_);
                    return v___x_7802_;
                } else {
                    v_snd_7803_ = lean_ctor_get(v_b_7799_, 1);
                    v_isSharedCheck_7850_ = (!lean_is_exclusive(v_b_7799_)) as u8;
                    if v_isSharedCheck_7850_ == 0 {
                        v_unused_7851_ = lean_ctor_get(v_b_7799_, 0);
                        lean_dec(v_unused_7851_);
                        v___x_7805_ = v_b_7799_;
                        v_isShared_7806_ = v_isSharedCheck_7850_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7803_);
                        lean_dec(v_b_7799_);
                        v___x_7805_ = lean_box(0);
                        v_isShared_7806_ = v_isSharedCheck_7850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7807_ = lean_box(0);
                v_a_7816_ = lean_array_uget_borrowed(v_as_7796_, v_i_7798_);
                if lean_obj_tag(v_a_7816_) == 0 {
                    v_a_7809_ = v_snd_7803_;
                    state = 2;
                    continue;
                } else {
                    v_val_7817_ = lean_ctor_get(v_a_7816_, 0);
                    v_fst_7818_ = lean_ctor_get(v_snd_7803_, 0);
                    v_snd_7819_ = lean_ctor_get(v_snd_7803_, 1);
                    v_isSharedCheck_7849_ = (!lean_is_exclusive(v_snd_7803_)) as u8;
                    if v_isSharedCheck_7849_ == 0 {
                        v___x_7821_ = v_snd_7803_;
                        v_isShared_7822_ = v_isSharedCheck_7849_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_7819_);
                        lean_inc(v_fst_7818_);
                        lean_dec(v_snd_7803_);
                        v___x_7821_ = lean_box(0);
                        v_isShared_7822_ = v_isSharedCheck_7849_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7806_ == 0 {
                    lean_ctor_set(v___x_7805_, 1, v_a_7809_);
                    lean_ctor_set(v___x_7805_, 0, v___x_7807_);
                    v___x_7811_ = v___x_7805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7815_, 0, v___x_7807_);
                    lean_ctor_set(v_reuseFailAlloc_7815_, 1, v_a_7809_);
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
                if lean_obj_tag(v___x_7824_) == 1 {
                    v_val_7825_ = lean_ctor_get(v___x_7824_, 0);
                    lean_inc(v_val_7825_);
                    lean_dec_ref_known(v___x_7824_, 1);
                    v___x_7826_ = l_Lean_LocalDecl_type(v_val_7817_);
                    if lean_obj_tag(v___x_7826_) == 10 {
                        v_data_7827_ = lean_ctor_get(v___x_7826_, 0);
                        lean_inc(v_data_7827_);
                        lean_dec_ref_known(v___x_7826_, 2);
                        v___x_7828_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7829_ = lean_unsigned_to_nat(2);
                        v___x_7830_ = l_Lean_KVMap_getNat(v_data_7827_, v___x_7828_, v___x_7829_);
                        lean_dec(v_data_7827_);
                        v___x_7831_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7830_);
                        lean_dec(v___x_7830_);
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
                                lean_ctor_set(v___x_7821_, 1, v___x_7836_);
                                lean_ctor_set(v___x_7821_, 0, v___x_7835_);
                                v___x_7838_ = v___x_7821_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7839_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7839_, 0, v___x_7835_);
                                lean_ctor_set(v_reuseFailAlloc_7839_, 1, v___x_7836_);
                                v___x_7838_ = v_reuseFailAlloc_7839_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_7825_);
                            if v_isShared_7822_ == 0 {
                                v___x_7841_ = v___x_7821_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7842_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7842_, 0, v_fst_7818_);
                                lean_ctor_set(v_reuseFailAlloc_7842_, 1, v_snd_7819_);
                                v___x_7841_ = v_reuseFailAlloc_7842_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7826_);
                        lean_dec(v_val_7825_);
                        if v_isShared_7822_ == 0 {
                            v___x_7844_ = v___x_7821_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7845_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7845_, 0, v_fst_7818_);
                            lean_ctor_set(v_reuseFailAlloc_7845_, 1, v_snd_7819_);
                            v___x_7844_ = v_reuseFailAlloc_7845_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7824_);
                    if v_isShared_7822_ == 0 {
                        v___x_7847_ = v___x_7821_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7848_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_fst_7818_);
                        lean_ctor_set(v_reuseFailAlloc_7848_, 1, v_snd_7819_);
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
    mut v_elimTrivial_7852_: *mut LeanObject,
    mut v_as_7853_: *mut LeanObject,
    mut v_sz_7854_: *mut LeanObject,
    mut v_i_7855_: *mut LeanObject,
    mut v_b_7856_: *mut LeanObject,
    mut v___y_7857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_7858_: u8 = 0;
    let mut v_sz_boxed_7859_: usize = 0;
    let mut v_i_boxed_7860_: usize = 0;
    let mut v_res_7861_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7858_ = (lean_unbox(v_elimTrivial_7852_) as u8);
    v_sz_boxed_7859_ = lean_unbox_usize(v_sz_7854_);
    lean_dec(v_sz_7854_);
    v_i_boxed_7860_ = lean_unbox_usize(v_i_7855_);
    lean_dec(v_i_7855_);
    v_res_7861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_7858_, v_as_7853_, v_sz_boxed_7859_, v_i_boxed_7860_, v_b_7856_);
    lean_dec_ref(v_as_7853_);
    return v_res_7861_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(
    mut v_elimTrivial_7862_: u8,
    mut v_as_7863_: *mut LeanObject,
    mut v_sz_7864_: usize,
    mut v_i_7865_: usize,
    mut v_b_7866_: *mut LeanObject,
    mut v___y_7867_: *mut LeanObject,
    mut v___y_7868_: *mut LeanObject,
    mut v___y_7869_: *mut LeanObject,
    mut v___y_7870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7872_: u8 = 0;
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7877_: u8 = 0;
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: usize = 0;
    let mut v___x_7884_: usize = 0;
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7893_: u8 = 0;
    let mut v___x_7894_: u8 = 0;
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: u8 = 0;
    let mut v___x_7903_: u8 = 0;
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7920_: u8 = 0;
    let mut v_isSharedCheck_7921_: u8 = 0;
    let mut v_unused_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7872_ = lean_usize_dec_lt(v_i_7865_, v_sz_7864_);
                if v___x_7872_ == 0 {
                    v___x_7873_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7873_, 0, v_b_7866_);
                    return v___x_7873_;
                } else {
                    v_snd_7874_ = lean_ctor_get(v_b_7866_, 1);
                    v_isSharedCheck_7921_ = (!lean_is_exclusive(v_b_7866_)) as u8;
                    if v_isSharedCheck_7921_ == 0 {
                        v_unused_7922_ = lean_ctor_get(v_b_7866_, 0);
                        lean_dec(v_unused_7922_);
                        v___x_7876_ = v_b_7866_;
                        v_isShared_7877_ = v_isSharedCheck_7921_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7874_);
                        lean_dec(v_b_7866_);
                        v___x_7876_ = lean_box(0);
                        v_isShared_7877_ = v_isSharedCheck_7921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7878_ = lean_box(0);
                v_a_7887_ = lean_array_uget_borrowed(v_as_7863_, v_i_7865_);
                if lean_obj_tag(v_a_7887_) == 0 {
                    v_a_7880_ = v_snd_7874_;
                    state = 2;
                    continue;
                } else {
                    v_val_7888_ = lean_ctor_get(v_a_7887_, 0);
                    v_fst_7889_ = lean_ctor_get(v_snd_7874_, 0);
                    v_snd_7890_ = lean_ctor_get(v_snd_7874_, 1);
                    v_isSharedCheck_7920_ = (!lean_is_exclusive(v_snd_7874_)) as u8;
                    if v_isSharedCheck_7920_ == 0 {
                        v___x_7892_ = v_snd_7874_;
                        v_isShared_7893_ = v_isSharedCheck_7920_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_7890_);
                        lean_inc(v_fst_7889_);
                        lean_dec(v_snd_7874_);
                        v___x_7892_ = lean_box(0);
                        v_isShared_7893_ = v_isSharedCheck_7920_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7877_ == 0 {
                    lean_ctor_set(v___x_7876_, 1, v_a_7880_);
                    lean_ctor_set(v___x_7876_, 0, v___x_7878_);
                    v___x_7882_ = v___x_7876_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7886_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 0, v___x_7878_);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 1, v_a_7880_);
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
                if lean_obj_tag(v___x_7895_) == 1 {
                    v_val_7896_ = lean_ctor_get(v___x_7895_, 0);
                    lean_inc(v_val_7896_);
                    lean_dec_ref_known(v___x_7895_, 1);
                    v___x_7897_ = l_Lean_LocalDecl_type(v_val_7888_);
                    if lean_obj_tag(v___x_7897_) == 10 {
                        v_data_7898_ = lean_ctor_get(v___x_7897_, 0);
                        lean_inc(v_data_7898_);
                        lean_dec_ref_known(v___x_7897_, 2);
                        v___x_7899_ = l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1;
                        v___x_7900_ = lean_unsigned_to_nat(2);
                        v___x_7901_ = l_Lean_KVMap_getNat(v_data_7898_, v___x_7899_, v___x_7900_);
                        lean_dec(v_data_7898_);
                        v___x_7902_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_7901_);
                        lean_dec(v___x_7901_);
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
                                lean_ctor_set(v___x_7892_, 1, v___x_7907_);
                                lean_ctor_set(v___x_7892_, 0, v___x_7906_);
                                v___x_7909_ = v___x_7892_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7910_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7910_, 0, v___x_7906_);
                                lean_ctor_set(v_reuseFailAlloc_7910_, 1, v___x_7907_);
                                v___x_7909_ = v_reuseFailAlloc_7910_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_7896_);
                            if v_isShared_7893_ == 0 {
                                v___x_7912_ = v___x_7892_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7913_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7913_, 0, v_fst_7889_);
                                lean_ctor_set(v_reuseFailAlloc_7913_, 1, v_snd_7890_);
                                v___x_7912_ = v_reuseFailAlloc_7913_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7897_);
                        lean_dec(v_val_7896_);
                        if v_isShared_7893_ == 0 {
                            v___x_7915_ = v___x_7892_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7916_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7916_, 0, v_fst_7889_);
                            lean_ctor_set(v_reuseFailAlloc_7916_, 1, v_snd_7890_);
                            v___x_7915_ = v_reuseFailAlloc_7916_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7895_);
                    if v_isShared_7893_ == 0 {
                        v___x_7918_ = v___x_7892_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7919_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7919_, 0, v_fst_7889_);
                        lean_ctor_set(v_reuseFailAlloc_7919_, 1, v_snd_7890_);
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
    mut v_elimTrivial_7923_: *mut LeanObject,
    mut v_as_7924_: *mut LeanObject,
    mut v_sz_7925_: *mut LeanObject,
    mut v_i_7926_: *mut LeanObject,
    mut v_b_7927_: *mut LeanObject,
    mut v___y_7928_: *mut LeanObject,
    mut v___y_7929_: *mut LeanObject,
    mut v___y_7930_: *mut LeanObject,
    mut v___y_7931_: *mut LeanObject,
    mut v___y_7932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_7933_: u8 = 0;
    let mut v_sz_boxed_7934_: usize = 0;
    let mut v_i_boxed_7935_: usize = 0;
    let mut v_res_7936_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_7933_ = (lean_unbox(v_elimTrivial_7923_) as u8);
    v_sz_boxed_7934_ = lean_unbox_usize(v_sz_7925_);
    lean_dec(v_sz_7925_);
    v_i_boxed_7935_ = lean_unbox_usize(v_i_7926_);
    lean_dec(v_i_7926_);
    v_res_7936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_7933_, v_as_7924_, v_sz_boxed_7934_, v_i_boxed_7935_, v_b_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_);
    lean_dec(v___y_7931_);
    lean_dec_ref(v___y_7930_);
    lean_dec(v___y_7929_);
    lean_dec_ref(v___y_7928_);
    lean_dec_ref(v_as_7924_);
    return v_res_7936_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(
    mut v_init_7937_: *mut LeanObject,
    mut v_elimTrivial_7938_: u8,
    mut v_n_7939_: *mut LeanObject,
    mut v_b_7940_: *mut LeanObject,
    mut v___y_7941_: *mut LeanObject,
    mut v___y_7942_: *mut LeanObject,
    mut v___y_7943_: *mut LeanObject,
    mut v___y_7944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7949_: usize = 0;
    let mut v___x_7950_: usize = 0;
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7955_: u8 = 0;
    let mut v_fst_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7966_: u8 = 0;
    let mut v_a_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7974_: u8 = 0;
    let mut v_vs_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7978_: usize = 0;
    let mut v___x_7979_: usize = 0;
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7984_: u8 = 0;
    let mut v_fst_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7995_: u8 = 0;
    let mut v_a_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_7939_) == 0 {
                    v_cs_7946_ = lean_ctor_get(v_n_7939_, 0);
                    v___x_7947_ = lean_box(0);
                    v___x_7948_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7948_, 0, v___x_7947_);
                    lean_ctor_set(v___x_7948_, 1, v_b_7940_);
                    v_sz_7949_ = lean_array_size(v_cs_7946_);
                    v___x_7950_ = 0usize;
                    v___x_7951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_7937_, v_elimTrivial_7938_, v_cs_7946_, v_sz_7949_, v___x_7950_, v___x_7948_, v___y_7941_, v___y_7942_, v___y_7943_, v___y_7944_);
                    if lean_obj_tag(v___x_7951_) == 0 {
                        v_a_7952_ = lean_ctor_get(v___x_7951_, 0);
                        v_isSharedCheck_7966_ = (!lean_is_exclusive(v___x_7951_)) as u8;
                        if v_isSharedCheck_7966_ == 0 {
                            v___x_7954_ = v___x_7951_;
                            v_isShared_7955_ = v_isSharedCheck_7966_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7952_);
                            lean_dec(v___x_7951_);
                            v___x_7954_ = lean_box(0);
                            v_isShared_7955_ = v_isSharedCheck_7966_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7967_ = lean_ctor_get(v___x_7951_, 0);
                        v_isSharedCheck_7974_ = (!lean_is_exclusive(v___x_7951_)) as u8;
                        if v_isSharedCheck_7974_ == 0 {
                            v___x_7969_ = v___x_7951_;
                            v_isShared_7970_ = v_isSharedCheck_7974_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7967_);
                            lean_dec(v___x_7951_);
                            v___x_7969_ = lean_box(0);
                            v_isShared_7970_ = v_isSharedCheck_7974_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_7975_ = lean_ctor_get(v_n_7939_, 0);
                    v___x_7976_ = lean_box(0);
                    v___x_7977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7977_, 0, v___x_7976_);
                    lean_ctor_set(v___x_7977_, 1, v_b_7940_);
                    v_sz_7978_ = lean_array_size(v_vs_7975_);
                    v___x_7979_ = 0usize;
                    v___x_7980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_7938_, v_vs_7975_, v_sz_7978_, v___x_7979_, v___x_7977_, v___y_7941_, v___y_7942_, v___y_7943_, v___y_7944_);
                    if lean_obj_tag(v___x_7980_) == 0 {
                        v_a_7981_ = lean_ctor_get(v___x_7980_, 0);
                        v_isSharedCheck_7995_ = (!lean_is_exclusive(v___x_7980_)) as u8;
                        if v_isSharedCheck_7995_ == 0 {
                            v___x_7983_ = v___x_7980_;
                            v_isShared_7984_ = v_isSharedCheck_7995_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7981_);
                            lean_dec(v___x_7980_);
                            v___x_7983_ = lean_box(0);
                            v_isShared_7984_ = v_isSharedCheck_7995_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_7996_ = lean_ctor_get(v___x_7980_, 0);
                        v_isSharedCheck_8003_ = (!lean_is_exclusive(v___x_7980_)) as u8;
                        if v_isSharedCheck_8003_ == 0 {
                            v___x_7998_ = v___x_7980_;
                            v_isShared_7999_ = v_isSharedCheck_8003_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7996_);
                            lean_dec(v___x_7980_);
                            v___x_7998_ = lean_box(0);
                            v_isShared_7999_ = v_isSharedCheck_8003_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_7956_ = lean_ctor_get(v_a_7952_, 0);
                if lean_obj_tag(v_fst_7956_) == 0 {
                    v_snd_7957_ = lean_ctor_get(v_a_7952_, 1);
                    lean_inc(v_snd_7957_);
                    lean_dec(v_a_7952_);
                    v___x_7958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7958_, 0, v_snd_7957_);
                    if v_isShared_7955_ == 0 {
                        lean_ctor_set(v___x_7954_, 0, v___x_7958_);
                        v___x_7960_ = v___x_7954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7961_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7961_, 0, v___x_7958_);
                        v___x_7960_ = v_reuseFailAlloc_7961_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7956_);
                    lean_dec(v_a_7952_);
                    v_val_7962_ = lean_ctor_get(v_fst_7956_, 0);
                    lean_inc(v_val_7962_);
                    lean_dec_ref_known(v_fst_7956_, 1);
                    if v_isShared_7955_ == 0 {
                        lean_ctor_set(v___x_7954_, 0, v_val_7962_);
                        v___x_7964_ = v___x_7954_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7965_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7965_, 0, v_val_7962_);
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
                    v_reuseFailAlloc_7973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7973_, 0, v_a_7967_);
                    v___x_7972_ = v_reuseFailAlloc_7973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7972_;
            }
            6 => {
                v_fst_7985_ = lean_ctor_get(v_a_7981_, 0);
                if lean_obj_tag(v_fst_7985_) == 0 {
                    v_snd_7986_ = lean_ctor_get(v_a_7981_, 1);
                    lean_inc(v_snd_7986_);
                    lean_dec(v_a_7981_);
                    v___x_7987_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7987_, 0, v_snd_7986_);
                    if v_isShared_7984_ == 0 {
                        lean_ctor_set(v___x_7983_, 0, v___x_7987_);
                        v___x_7989_ = v___x_7983_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7990_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7990_, 0, v___x_7987_);
                        v___x_7989_ = v_reuseFailAlloc_7990_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7985_);
                    lean_dec(v_a_7981_);
                    v_val_7991_ = lean_ctor_get(v_fst_7985_, 0);
                    lean_inc(v_val_7991_);
                    lean_dec_ref_known(v_fst_7985_, 1);
                    if v_isShared_7984_ == 0 {
                        lean_ctor_set(v___x_7983_, 0, v_val_7991_);
                        v___x_7993_ = v___x_7983_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7994_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7994_, 0, v_val_7991_);
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
                    v_reuseFailAlloc_8002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8002_, 0, v_a_7996_);
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
    mut v_init_8004_: *mut LeanObject,
    mut v_elimTrivial_8005_: u8,
    mut v_as_8006_: *mut LeanObject,
    mut v_sz_8007_: usize,
    mut v_i_8008_: usize,
    mut v_b_8009_: *mut LeanObject,
    mut v___y_8010_: *mut LeanObject,
    mut v___y_8011_: *mut LeanObject,
    mut v___y_8012_: *mut LeanObject,
    mut v___y_8013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8015_: u8 = 0;
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8020_: u8 = 0;
    let mut v_a_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8026_: u8 = 0;
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: usize = 0;
    let mut v___x_8039_: usize = 0;
    let mut v_reuseFailAlloc_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8042_: u8 = 0;
    let mut v_a_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8046_: u8 = 0;
    let mut v___x_8048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8050_: u8 = 0;
    let mut v_isSharedCheck_8051_: u8 = 0;
    let mut v_unused_8052_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8015_ = lean_usize_dec_lt(v_i_8008_, v_sz_8007_);
                if v___x_8015_ == 0 {
                    v___x_8016_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8016_, 0, v_b_8009_);
                    return v___x_8016_;
                } else {
                    v_snd_8017_ = lean_ctor_get(v_b_8009_, 1);
                    v_isSharedCheck_8051_ = (!lean_is_exclusive(v_b_8009_)) as u8;
                    if v_isSharedCheck_8051_ == 0 {
                        v_unused_8052_ = lean_ctor_get(v_b_8009_, 0);
                        lean_dec(v_unused_8052_);
                        v___x_8019_ = v_b_8009_;
                        v_isShared_8020_ = v_isSharedCheck_8051_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8017_);
                        lean_dec(v_b_8009_);
                        v___x_8019_ = lean_box(0);
                        v_isShared_8020_ = v_isSharedCheck_8051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_8021_ = lean_array_uget_borrowed(v_as_8006_, v_i_8008_);
                lean_inc(v_snd_8017_);
                v___x_8022_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8004_, v_elimTrivial_8005_, v_a_8021_, v_snd_8017_, v___y_8010_, v___y_8011_, v___y_8012_, v___y_8013_);
                if lean_obj_tag(v___x_8022_) == 0 {
                    v_a_8023_ = lean_ctor_get(v___x_8022_, 0);
                    v_isSharedCheck_8042_ = (!lean_is_exclusive(v___x_8022_)) as u8;
                    if v_isSharedCheck_8042_ == 0 {
                        v___x_8025_ = v___x_8022_;
                        v_isShared_8026_ = v_isSharedCheck_8042_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8023_);
                        lean_dec(v___x_8022_);
                        v___x_8025_ = lean_box(0);
                        v_isShared_8026_ = v_isSharedCheck_8042_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8019_);
                    lean_dec(v_snd_8017_);
                    v_a_8043_ = lean_ctor_get(v___x_8022_, 0);
                    v_isSharedCheck_8050_ = (!lean_is_exclusive(v___x_8022_)) as u8;
                    if v_isSharedCheck_8050_ == 0 {
                        v___x_8045_ = v___x_8022_;
                        v_isShared_8046_ = v_isSharedCheck_8050_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8043_);
                        lean_dec(v___x_8022_);
                        v___x_8045_ = lean_box(0);
                        v_isShared_8046_ = v_isSharedCheck_8050_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_8023_) == 0 {
                    v___x_8027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8027_, 0, v_a_8023_);
                    if v_isShared_8020_ == 0 {
                        lean_ctor_set(v___x_8019_, 0, v___x_8027_);
                        v___x_8029_ = v___x_8019_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8033_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8033_, 0, v___x_8027_);
                        lean_ctor_set(v_reuseFailAlloc_8033_, 1, v_snd_8017_);
                        v___x_8029_ = v_reuseFailAlloc_8033_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8025_);
                    lean_dec(v_snd_8017_);
                    v_a_8034_ = lean_ctor_get(v_a_8023_, 0);
                    lean_inc(v_a_8034_);
                    lean_dec_ref_known(v_a_8023_, 1);
                    v___x_8035_ = lean_box(0);
                    if v_isShared_8020_ == 0 {
                        lean_ctor_set(v___x_8019_, 1, v_a_8034_);
                        lean_ctor_set(v___x_8019_, 0, v___x_8035_);
                        v___x_8037_ = v___x_8019_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8041_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8041_, 0, v___x_8035_);
                        lean_ctor_set(v_reuseFailAlloc_8041_, 1, v_a_8034_);
                        v___x_8037_ = v_reuseFailAlloc_8041_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8026_ == 0 {
                    lean_ctor_set(v___x_8025_, 0, v___x_8029_);
                    v___x_8031_ = v___x_8025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8032_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8032_, 0, v___x_8029_);
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
                    v_reuseFailAlloc_8049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8049_, 0, v_a_8043_);
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
    mut v_init_8053_: *mut LeanObject,
    mut v_elimTrivial_8054_: *mut LeanObject,
    mut v_as_8055_: *mut LeanObject,
    mut v_sz_8056_: *mut LeanObject,
    mut v_i_8057_: *mut LeanObject,
    mut v_b_8058_: *mut LeanObject,
    mut v___y_8059_: *mut LeanObject,
    mut v___y_8060_: *mut LeanObject,
    mut v___y_8061_: *mut LeanObject,
    mut v___y_8062_: *mut LeanObject,
    mut v___y_8063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8064_: u8 = 0;
    let mut v_sz_boxed_8065_: usize = 0;
    let mut v_i_boxed_8066_: usize = 0;
    let mut v_res_8067_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8064_ = (lean_unbox(v_elimTrivial_8054_) as u8);
    v_sz_boxed_8065_ = lean_unbox_usize(v_sz_8056_);
    lean_dec(v_sz_8056_);
    v_i_boxed_8066_ = lean_unbox_usize(v_i_8057_);
    lean_dec(v_i_8057_);
    v_res_8067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_8053_, v_elimTrivial_boxed_8064_, v_as_8055_, v_sz_boxed_8065_, v_i_boxed_8066_, v_b_8058_, v___y_8059_, v___y_8060_, v___y_8061_, v___y_8062_);
    lean_dec(v___y_8062_);
    lean_dec_ref(v___y_8061_);
    lean_dec(v___y_8060_);
    lean_dec_ref(v___y_8059_);
    lean_dec_ref(v_as_8055_);
    lean_dec_ref(v_init_8053_);
    return v_res_8067_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(
    mut v_init_8068_: *mut LeanObject,
    mut v_elimTrivial_8069_: *mut LeanObject,
    mut v_n_8070_: *mut LeanObject,
    mut v_b_8071_: *mut LeanObject,
    mut v___y_8072_: *mut LeanObject,
    mut v___y_8073_: *mut LeanObject,
    mut v___y_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
    mut v___y_8076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8077_: u8 = 0;
    let mut v_res_8078_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8077_ = (lean_unbox(v_elimTrivial_8069_) as u8);
    v_res_8078_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8068_, v_elimTrivial_boxed_8077_, v_n_8070_, v_b_8071_, v___y_8072_, v___y_8073_, v___y_8074_, v___y_8075_);
    lean_dec(v___y_8075_);
    lean_dec_ref(v___y_8074_);
    lean_dec(v___y_8073_);
    lean_dec_ref(v___y_8072_);
    lean_dec_ref(v_n_8070_);
    lean_dec_ref(v_init_8068_);
    return v_res_8078_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(
    mut v_elimTrivial_8079_: u8,
    mut v_t_8080_: *mut LeanObject,
    mut v_init_8081_: *mut LeanObject,
    mut v___y_8082_: *mut LeanObject,
    mut v___y_8083_: *mut LeanObject,
    mut v___y_8084_: *mut LeanObject,
    mut v___y_8085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8093_: u8 = 0;
    let mut v_a_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8101_: usize = 0;
    let mut v___x_8102_: usize = 0;
    let mut v___x_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8107_: u8 = 0;
    let mut v_fst_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8117_: u8 = 0;
    let mut v_a_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8125_: u8 = 0;
    let mut v_isSharedCheck_8126_: u8 = 0;
    let mut v_a_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8130_: u8 = 0;
    let mut v___x_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_8087_ = lean_ctor_get(v_t_8080_, 0);
                v_tail_8088_ = lean_ctor_get(v_t_8080_, 1);
                lean_inc_ref(v_init_8081_);
                v___x_8089_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_8081_, v_elimTrivial_8079_, v_root_8087_, v_init_8081_, v___y_8082_, v___y_8083_, v___y_8084_, v___y_8085_);
                lean_dec_ref(v_init_8081_);
                if lean_obj_tag(v___x_8089_) == 0 {
                    v_a_8090_ = lean_ctor_get(v___x_8089_, 0);
                    v_isSharedCheck_8126_ = (!lean_is_exclusive(v___x_8089_)) as u8;
                    if v_isSharedCheck_8126_ == 0 {
                        v___x_8092_ = v___x_8089_;
                        v_isShared_8093_ = v_isSharedCheck_8126_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8090_);
                        lean_dec(v___x_8089_);
                        v___x_8092_ = lean_box(0);
                        v_isShared_8093_ = v_isSharedCheck_8126_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8127_ = lean_ctor_get(v___x_8089_, 0);
                    v_isSharedCheck_8134_ = (!lean_is_exclusive(v___x_8089_)) as u8;
                    if v_isSharedCheck_8134_ == 0 {
                        v___x_8129_ = v___x_8089_;
                        v_isShared_8130_ = v_isSharedCheck_8134_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8127_);
                        lean_dec(v___x_8089_);
                        v___x_8129_ = lean_box(0);
                        v_isShared_8130_ = v_isSharedCheck_8134_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_8090_) == 0 {
                    v_a_8094_ = lean_ctor_get(v_a_8090_, 0);
                    lean_inc(v_a_8094_);
                    lean_dec_ref_known(v_a_8090_, 1);
                    if v_isShared_8093_ == 0 {
                        lean_ctor_set(v___x_8092_, 0, v_a_8094_);
                        v___x_8096_ = v___x_8092_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8097_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8097_, 0, v_a_8094_);
                        v___x_8096_ = v_reuseFailAlloc_8097_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8092_);
                    v_a_8098_ = lean_ctor_get(v_a_8090_, 0);
                    lean_inc(v_a_8098_);
                    lean_dec_ref_known(v_a_8090_, 1);
                    v___x_8099_ = lean_box(0);
                    v___x_8100_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8100_, 0, v___x_8099_);
                    lean_ctor_set(v___x_8100_, 1, v_a_8098_);
                    v_sz_8101_ = lean_array_size(v_tail_8088_);
                    v___x_8102_ = 0usize;
                    v___x_8103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_8079_, v_tail_8088_, v_sz_8101_, v___x_8102_, v___x_8100_, v___y_8082_, v___y_8083_, v___y_8084_, v___y_8085_);
                    if lean_obj_tag(v___x_8103_) == 0 {
                        v_a_8104_ = lean_ctor_get(v___x_8103_, 0);
                        v_isSharedCheck_8117_ = (!lean_is_exclusive(v___x_8103_)) as u8;
                        if v_isSharedCheck_8117_ == 0 {
                            v___x_8106_ = v___x_8103_;
                            v_isShared_8107_ = v_isSharedCheck_8117_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8104_);
                            lean_dec(v___x_8103_);
                            v___x_8106_ = lean_box(0);
                            v_isShared_8107_ = v_isSharedCheck_8117_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_8118_ = lean_ctor_get(v___x_8103_, 0);
                        v_isSharedCheck_8125_ = (!lean_is_exclusive(v___x_8103_)) as u8;
                        if v_isSharedCheck_8125_ == 0 {
                            v___x_8120_ = v___x_8103_;
                            v_isShared_8121_ = v_isSharedCheck_8125_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_8118_);
                            lean_dec(v___x_8103_);
                            v___x_8120_ = lean_box(0);
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
                v_fst_8108_ = lean_ctor_get(v_a_8104_, 0);
                if lean_obj_tag(v_fst_8108_) == 0 {
                    v_snd_8109_ = lean_ctor_get(v_a_8104_, 1);
                    lean_inc(v_snd_8109_);
                    lean_dec(v_a_8104_);
                    if v_isShared_8107_ == 0 {
                        lean_ctor_set(v___x_8106_, 0, v_snd_8109_);
                        v___x_8111_ = v___x_8106_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8112_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8112_, 0, v_snd_8109_);
                        v___x_8111_ = v_reuseFailAlloc_8112_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_8108_);
                    lean_dec(v_a_8104_);
                    v_val_8113_ = lean_ctor_get(v_fst_8108_, 0);
                    lean_inc(v_val_8113_);
                    lean_dec_ref_known(v_fst_8108_, 1);
                    if v_isShared_8107_ == 0 {
                        lean_ctor_set(v___x_8106_, 0, v_val_8113_);
                        v___x_8115_ = v___x_8106_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8116_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8116_, 0, v_val_8113_);
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
                    v_reuseFailAlloc_8124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8124_, 0, v_a_8118_);
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
                    v_reuseFailAlloc_8133_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8133_, 0, v_a_8127_);
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
    mut v_elimTrivial_8135_: *mut LeanObject,
    mut v_t_8136_: *mut LeanObject,
    mut v_init_8137_: *mut LeanObject,
    mut v___y_8138_: *mut LeanObject,
    mut v___y_8139_: *mut LeanObject,
    mut v___y_8140_: *mut LeanObject,
    mut v___y_8141_: *mut LeanObject,
    mut v___y_8142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8143_: u8 = 0;
    let mut v_res_8144_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8143_ = (lean_unbox(v_elimTrivial_8135_) as u8);
    v_res_8144_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(
        v_elimTrivial_boxed_8143_,
        v_t_8136_,
        v_init_8137_,
        v___y_8138_,
        v___y_8139_,
        v___y_8140_,
        v___y_8141_,
    );
    lean_dec(v___y_8141_);
    lean_dec_ref(v___y_8140_);
    lean_dec(v___y_8139_);
    lean_dec_ref(v___y_8138_);
    lean_dec_ref(v_t_8136_);
    return v_res_8144_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(
    mut v_as_8145_: *mut LeanObject,
    mut v_sz_8146_: usize,
    mut v_i_8147_: usize,
    mut v_b_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
    mut v___y_8150_: *mut LeanObject,
    mut v___y_8151_: *mut LeanObject,
    mut v___y_8152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8154_: u8 = 0;
    let mut v___x_8155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: usize = 0;
    let mut v___x_8161_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8154_ = lean_usize_dec_lt(v_i_8147_, v_sz_8146_);
                if v___x_8154_ == 0 {
                    v___x_8155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8155_, 0, v_b_8148_);
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
                    if lean_obj_tag(v___x_8158_) == 0 {
                        v_a_8159_ = lean_ctor_get(v___x_8158_, 0);
                        lean_inc(v_a_8159_);
                        lean_dec_ref_known(v___x_8158_, 1);
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
    mut v_as_8163_: *mut LeanObject,
    mut v_sz_8164_: *mut LeanObject,
    mut v_i_8165_: *mut LeanObject,
    mut v_b_8166_: *mut LeanObject,
    mut v___y_8167_: *mut LeanObject,
    mut v___y_8168_: *mut LeanObject,
    mut v___y_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
    mut v___y_8171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8172_: usize = 0;
    let mut v_i_boxed_8173_: usize = 0;
    let mut v_res_8174_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8172_ = lean_unbox_usize(v_sz_8164_);
    lean_dec(v_sz_8164_);
    v_i_boxed_8173_ = lean_unbox_usize(v_i_8165_);
    lean_dec(v_i_8165_);
    v_res_8174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_8163_, v_sz_boxed_8172_, v_i_boxed_8173_, v_b_8166_, v___y_8167_, v___y_8168_, v___y_8169_, v___y_8170_);
    lean_dec(v___y_8170_);
    lean_dec_ref(v___y_8169_);
    lean_dec(v___y_8168_);
    lean_dec_ref(v___y_8167_);
    lean_dec_ref(v_as_8163_);
    return v_res_8174_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(
    mut v_x_8175_: *mut LeanObject,
    mut v_x_8176_: *mut LeanObject,
    mut v_x_8177_: *mut LeanObject,
    mut v_x_8178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_8179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8183_: u8 = 0;
    let mut v___x_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: u8 = 0;
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_8191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: u8 = 0;
    let mut v___x_8194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_8179_ = lean_ctor_get(v_x_8175_, 0);
                v_vs_8180_ = lean_ctor_get(v_x_8175_, 1);
                v_isSharedCheck_8204_ = (!lean_is_exclusive(v_x_8175_)) as u8;
                if v_isSharedCheck_8204_ == 0 {
                    v___x_8182_ = v_x_8175_;
                    v_isShared_8183_ = v_isSharedCheck_8204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_8180_);
                    lean_inc(v_ks_8179_);
                    lean_dec(v_x_8175_);
                    v___x_8182_ = lean_box(0);
                    v_isShared_8183_ = v_isSharedCheck_8204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8184_ = lean_array_get_size(v_ks_8179_);
                v___x_8185_ = lean_nat_dec_lt(v_x_8176_, v___x_8184_);
                if v___x_8185_ == 0 {
                    lean_dec(v_x_8176_);
                    v___x_8186_ = lean_array_push(v_ks_8179_, v_x_8177_);
                    v___x_8187_ = lean_array_push(v_vs_8180_, v_x_8178_);
                    if v_isShared_8183_ == 0 {
                        lean_ctor_set(v___x_8182_, 1, v___x_8187_);
                        lean_ctor_set(v___x_8182_, 0, v___x_8186_);
                        v___x_8189_ = v___x_8182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8190_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8190_, 0, v___x_8186_);
                        lean_ctor_set(v_reuseFailAlloc_8190_, 1, v___x_8187_);
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
                            v_reuseFailAlloc_8198_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_8198_, 0, v_ks_8179_);
                            lean_ctor_set(v_reuseFailAlloc_8198_, 1, v_vs_8180_);
                            v___x_8194_ = v_reuseFailAlloc_8198_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_8199_ = lean_array_fset(v_ks_8179_, v_x_8176_, v_x_8177_);
                        v___x_8200_ = lean_array_fset(v_vs_8180_, v_x_8176_, v_x_8178_);
                        lean_dec(v_x_8176_);
                        if v_isShared_8183_ == 0 {
                            lean_ctor_set(v___x_8182_, 1, v___x_8200_);
                            lean_ctor_set(v___x_8182_, 0, v___x_8199_);
                            v___x_8202_ = v___x_8182_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_8203_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_8203_, 0, v___x_8199_);
                            lean_ctor_set(v_reuseFailAlloc_8203_, 1, v___x_8200_);
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
                v___x_8195_ = lean_unsigned_to_nat(1);
                v___x_8196_ = lean_nat_add(v_x_8176_, v___x_8195_);
                lean_dec(v_x_8176_);
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
    mut v_n_8205_: *mut LeanObject,
    mut v_k_8206_: *mut LeanObject,
    mut v_v_8207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut LeanObject = core::ptr::null_mut();
    v___x_8208_ = lean_unsigned_to_nat(0);
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
    v___x_8214_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
    v___x_8215_ = lean_usize_sub(v___x_8214_, v___x_8213_);
    return v___x_8215_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_8216_: *mut LeanObject = core::ptr::null_mut();
    v___x_8216_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_8216_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(
    mut v_x_8217_: *mut LeanObject,
    mut v_x_8218_: usize,
    mut v_x_8219_: usize,
    mut v_x_8220_: *mut LeanObject,
    mut v_x_8221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: usize = 0;
    let mut v___x_8224_: usize = 0;
    let mut v___x_8225_: usize = 0;
    let mut v___x_8226_: usize = 0;
    let mut v_j_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: u8 = 0;
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8232_: u8 = 0;
    let mut v_v_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8246_: u8 = 0;
    let mut v___x_8247_: u8 = 0;
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8253_: u8 = 0;
    let mut v_node_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8257_: u8 = 0;
    let mut v___x_8258_: usize = 0;
    let mut v___x_8259_: usize = 0;
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8264_: u8 = 0;
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8266_: u8 = 0;
    let mut v_unused_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8272_: u8 = 0;
    let mut v___x_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8277_: u8 = 0;
    let mut v_ks_8278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: usize = 0;
    let mut v___x_8284_: u8 = 0;
    let mut v___x_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8287_: u8 = 0;
    let mut v_reuseFailAlloc_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8217_) == 0 {
                    v_es_8222_ = lean_ctor_get(v_x_8217_, 0);
                    v___x_8223_ = 5usize;
                    v___x_8224_ = 1usize;
                    v___x_8225_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1);
                    v___x_8226_ = lean_usize_land(v_x_8218_, v___x_8225_);
                    v_j_8227_ = lean_usize_to_nat(v___x_8226_);
                    v___x_8228_ = lean_array_get_size(v_es_8222_);
                    v___x_8229_ = lean_nat_dec_lt(v_j_8227_, v___x_8228_);
                    if v___x_8229_ == 0 {
                        lean_dec(v_j_8227_);
                        lean_dec(v_x_8221_);
                        lean_dec(v_x_8220_);
                        return v_x_8217_;
                    } else {
                        lean_inc_ref(v_es_8222_);
                        v_isSharedCheck_8266_ = (!lean_is_exclusive(v_x_8217_)) as u8;
                        if v_isSharedCheck_8266_ == 0 {
                            v_unused_8267_ = lean_ctor_get(v_x_8217_, 0);
                            lean_dec(v_unused_8267_);
                            v___x_8231_ = v_x_8217_;
                            v_isShared_8232_ = v_isSharedCheck_8266_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_8217_);
                            v___x_8231_ = lean_box(0);
                            v_isShared_8232_ = v_isSharedCheck_8266_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_8268_ = lean_ctor_get(v_x_8217_, 0);
                    v_vs_8269_ = lean_ctor_get(v_x_8217_, 1);
                    v_isSharedCheck_8289_ = (!lean_is_exclusive(v_x_8217_)) as u8;
                    if v_isSharedCheck_8289_ == 0 {
                        v___x_8271_ = v_x_8217_;
                        v_isShared_8272_ = v_isSharedCheck_8289_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_8269_);
                        lean_inc(v_ks_8268_);
                        lean_dec(v_x_8217_);
                        v___x_8271_ = lean_box(0);
                        v_isShared_8272_ = v_isSharedCheck_8289_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_8233_ = lean_array_fget(v_es_8222_, v_j_8227_);
                v___x_8234_ = lean_box(0);
                v_xs_x27_8235_ = lean_array_fset(v_es_8222_, v_j_8227_, v___x_8234_);
                match lean_obj_tag(v_v_8233_) {
                    0 => {
                        v_key_8242_ = lean_ctor_get(v_v_8233_, 0);
                        v_val_8243_ = lean_ctor_get(v_v_8233_, 1);
                        v_isSharedCheck_8253_ = (!lean_is_exclusive(v_v_8233_)) as u8;
                        if v_isSharedCheck_8253_ == 0 {
                            v___x_8245_ = v_v_8233_;
                            v_isShared_8246_ = v_isSharedCheck_8253_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_8243_);
                            lean_inc(v_key_8242_);
                            lean_dec(v_v_8233_);
                            v___x_8245_ = lean_box(0);
                            v_isShared_8246_ = v_isSharedCheck_8253_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_8254_ = lean_ctor_get(v_v_8233_, 0);
                        v_isSharedCheck_8264_ = (!lean_is_exclusive(v_v_8233_)) as u8;
                        if v_isSharedCheck_8264_ == 0 {
                            v___x_8256_ = v_v_8233_;
                            v_isShared_8257_ = v_isSharedCheck_8264_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_8254_);
                            lean_dec(v_v_8233_);
                            v___x_8256_ = lean_box(0);
                            v_isShared_8257_ = v_isSharedCheck_8264_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_8265_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_8265_, 0, v_x_8220_);
                        lean_ctor_set(v___x_8265_, 1, v_x_8221_);
                        v___y_8237_ = v___x_8265_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8238_ = lean_array_fset(v_xs_x27_8235_, v_j_8227_, v___y_8237_);
                lean_dec(v_j_8227_);
                if v_isShared_8232_ == 0 {
                    lean_ctor_set(v___x_8231_, 0, v___x_8238_);
                    v___x_8240_ = v___x_8231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8241_, 0, v___x_8238_);
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
                    lean_del_object(v___x_8245_);
                    v___x_8248_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_8242_,
                        v_val_8243_,
                        v_x_8220_,
                        v_x_8221_,
                    );
                    v___x_8249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8249_, 0, v___x_8248_);
                    v___y_8237_ = v___x_8249_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_8243_);
                    lean_dec(v_key_8242_);
                    if v_isShared_8246_ == 0 {
                        lean_ctor_set(v___x_8245_, 1, v_x_8221_);
                        lean_ctor_set(v___x_8245_, 0, v_x_8220_);
                        v___x_8251_ = v___x_8245_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8252_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8252_, 0, v_x_8220_);
                        lean_ctor_set(v_reuseFailAlloc_8252_, 1, v_x_8221_);
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
                    lean_ctor_set(v___x_8256_, 0, v___x_8260_);
                    v___x_8262_ = v___x_8256_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8263_, 0, v___x_8260_);
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
                    v_reuseFailAlloc_8288_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8288_, 0, v_ks_8268_);
                    lean_ctor_set(v_reuseFailAlloc_8288_, 1, v_vs_8269_);
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
                    v___x_8286_ = lean_unsigned_to_nat(4);
                    v___x_8287_ = lean_nat_dec_lt(v___x_8285_, v___x_8286_);
                    lean_dec(v___x_8285_);
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
                    v_ks_8278_ = lean_ctor_get(v_newNode_8275_, 0);
                    lean_inc_ref(v_ks_8278_);
                    v_vs_8279_ = lean_ctor_get(v_newNode_8275_, 1);
                    lean_inc_ref(v_vs_8279_);
                    lean_dec_ref(v_newNode_8275_);
                    v___x_8280_ = lean_unsigned_to_nat(0);
                    v___x_8281_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2);
                    v___x_8282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_8219_, v_ks_8278_, v_vs_8279_, v___x_8280_, v___x_8281_);
                    lean_dec_ref(v_vs_8279_);
                    lean_dec_ref(v_ks_8278_);
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
    mut v_keys_8291_: *mut LeanObject,
    mut v_vals_8292_: *mut LeanObject,
    mut v_i_8293_: *mut LeanObject,
    mut v_entries_8294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8296_: u8 = 0;
    let mut v_k_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: u64 = 0;
    let mut v_h_8300_: usize = 0;
    let mut v___x_8301_: usize = 0;
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8303_: usize = 0;
    let mut v___x_8304_: usize = 0;
    let mut v___x_8305_: usize = 0;
    let mut v_h_8306_: usize = 0;
    let mut v___x_8307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8295_ = lean_array_get_size(v_keys_8291_);
                v___x_8296_ = lean_nat_dec_lt(v_i_8293_, v___x_8295_);
                if v___x_8296_ == 0 {
                    lean_dec(v_i_8293_);
                    return v_entries_8294_;
                } else {
                    v_k_8297_ = lean_array_fget_borrowed(v_keys_8291_, v_i_8293_);
                    v_v_8298_ = lean_array_fget_borrowed(v_vals_8292_, v_i_8293_);
                    v___x_8299_ = l_Lean_instHashableMVarId_hash(v_k_8297_);
                    v_h_8300_ = lean_uint64_to_usize(v___x_8299_);
                    v___x_8301_ = 5usize;
                    v___x_8302_ = lean_unsigned_to_nat(1);
                    v___x_8303_ = 1usize;
                    v___x_8304_ = lean_usize_sub(v_depth_8290_, v___x_8303_);
                    v___x_8305_ = lean_usize_mul(v___x_8301_, v___x_8304_);
                    v_h_8306_ = lean_usize_shift_right(v_h_8300_, v___x_8305_);
                    v___x_8307_ = lean_nat_add(v_i_8293_, v___x_8302_);
                    lean_dec(v_i_8293_);
                    lean_inc(v_v_8298_);
                    lean_inc(v_k_8297_);
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
    mut v_depth_8310_: *mut LeanObject,
    mut v_keys_8311_: *mut LeanObject,
    mut v_vals_8312_: *mut LeanObject,
    mut v_i_8313_: *mut LeanObject,
    mut v_entries_8314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_8315_: usize = 0;
    let mut v_res_8316_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_8315_ = lean_unbox_usize(v_depth_8310_);
    lean_dec(v_depth_8310_);
    v_res_8316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_8315_, v_keys_8311_, v_vals_8312_, v_i_8313_, v_entries_8314_);
    lean_dec_ref(v_vals_8312_);
    lean_dec_ref(v_keys_8311_);
    return v_res_8316_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_x_8317_: *mut LeanObject,
    mut v_x_8318_: *mut LeanObject,
    mut v_x_8319_: *mut LeanObject,
    mut v_x_8320_: *mut LeanObject,
    mut v_x_8321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7972__boxed_8322_: usize = 0;
    let mut v_x_7973__boxed_8323_: usize = 0;
    let mut v_res_8324_: *mut LeanObject = core::ptr::null_mut();
    v_x_7972__boxed_8322_ = lean_unbox_usize(v_x_8318_);
    lean_dec(v_x_8318_);
    v_x_7973__boxed_8323_ = lean_unbox_usize(v_x_8319_);
    lean_dec(v_x_8319_);
    v_res_8324_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8317_, v_x_7972__boxed_8322_, v_x_7973__boxed_8323_, v_x_8320_, v_x_8321_);
    return v_res_8324_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(
    mut v_x_8325_: *mut LeanObject,
    mut v_x_8326_: *mut LeanObject,
    mut v_x_8327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8328_: u64 = 0;
    let mut v___x_8329_: usize = 0;
    let mut v___x_8330_: usize = 0;
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_instHashableMVarId_hash(v_x_8326_);
    v___x_8329_ = lean_uint64_to_usize(v___x_8328_);
    v___x_8330_ = 1usize;
    v___x_8331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8325_, v___x_8329_, v___x_8330_, v_x_8326_, v_x_8327_);
    return v___x_8331_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
    mut v_mvarId_8332_: *mut LeanObject,
    mut v_val_8333_: *mut LeanObject,
    mut v___y_8334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_8338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8344_: u8 = 0;
    let mut v_depth_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_8346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8357_: u8 = 0;
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8368_: u8 = 0;
    let mut v_isSharedCheck_8369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8336_ = lean_st_ref_take(v___y_8334_);
                v_mctx_8337_ = lean_ctor_get(v___x_8336_, 0);
                v_cache_8338_ = lean_ctor_get(v___x_8336_, 1);
                v_zetaDeltaFVarIds_8339_ = lean_ctor_get(v___x_8336_, 2);
                v_postponed_8340_ = lean_ctor_get(v___x_8336_, 3);
                v_diag_8341_ = lean_ctor_get(v___x_8336_, 4);
                v_isSharedCheck_8369_ = (!lean_is_exclusive(v___x_8336_)) as u8;
                if v_isSharedCheck_8369_ == 0 {
                    v___x_8343_ = v___x_8336_;
                    v_isShared_8344_ = v_isSharedCheck_8369_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_8341_);
                    lean_inc(v_postponed_8340_);
                    lean_inc(v_zetaDeltaFVarIds_8339_);
                    lean_inc(v_cache_8338_);
                    lean_inc(v_mctx_8337_);
                    lean_dec(v___x_8336_);
                    v___x_8343_ = lean_box(0);
                    v_isShared_8344_ = v_isSharedCheck_8369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_8345_ = lean_ctor_get(v_mctx_8337_, 0);
                v_levelAssignDepth_8346_ = lean_ctor_get(v_mctx_8337_, 1);
                v_lmvarCounter_8347_ = lean_ctor_get(v_mctx_8337_, 2);
                v_mvarCounter_8348_ = lean_ctor_get(v_mctx_8337_, 3);
                v_lDecls_8349_ = lean_ctor_get(v_mctx_8337_, 4);
                v_decls_8350_ = lean_ctor_get(v_mctx_8337_, 5);
                v_userNames_8351_ = lean_ctor_get(v_mctx_8337_, 6);
                v_lAssignment_8352_ = lean_ctor_get(v_mctx_8337_, 7);
                v_eAssignment_8353_ = lean_ctor_get(v_mctx_8337_, 8);
                v_dAssignment_8354_ = lean_ctor_get(v_mctx_8337_, 9);
                v_isSharedCheck_8368_ = (!lean_is_exclusive(v_mctx_8337_)) as u8;
                if v_isSharedCheck_8368_ == 0 {
                    v___x_8356_ = v_mctx_8337_;
                    v_isShared_8357_ = v_isSharedCheck_8368_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_8354_);
                    lean_inc(v_eAssignment_8353_);
                    lean_inc(v_lAssignment_8352_);
                    lean_inc(v_userNames_8351_);
                    lean_inc(v_decls_8350_);
                    lean_inc(v_lDecls_8349_);
                    lean_inc(v_mvarCounter_8348_);
                    lean_inc(v_lmvarCounter_8347_);
                    lean_inc(v_levelAssignDepth_8346_);
                    lean_inc(v_depth_8345_);
                    lean_dec(v_mctx_8337_);
                    v___x_8356_ = lean_box(0);
                    v_isShared_8357_ = v_isSharedCheck_8368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8358_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_8353_, v_mvarId_8332_, v_val_8333_);
                if v_isShared_8357_ == 0 {
                    lean_ctor_set(v___x_8356_, 8, v___x_8358_);
                    v___x_8360_ = v___x_8356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8367_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 0, v_depth_8345_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 1, v_levelAssignDepth_8346_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 2, v_lmvarCounter_8347_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 3, v_mvarCounter_8348_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 4, v_lDecls_8349_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 5, v_decls_8350_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 6, v_userNames_8351_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 7, v_lAssignment_8352_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 8, v___x_8358_);
                    lean_ctor_set(v_reuseFailAlloc_8367_, 9, v_dAssignment_8354_);
                    v___x_8360_ = v_reuseFailAlloc_8367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8344_ == 0 {
                    lean_ctor_set(v___x_8343_, 0, v___x_8360_);
                    v___x_8362_ = v___x_8343_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8366_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8366_, 0, v___x_8360_);
                    lean_ctor_set(v_reuseFailAlloc_8366_, 1, v_cache_8338_);
                    lean_ctor_set(v_reuseFailAlloc_8366_, 2, v_zetaDeltaFVarIds_8339_);
                    lean_ctor_set(v_reuseFailAlloc_8366_, 3, v_postponed_8340_);
                    lean_ctor_set(v_reuseFailAlloc_8366_, 4, v_diag_8341_);
                    v___x_8362_ = v_reuseFailAlloc_8366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8363_ = lean_st_ref_set(v___y_8334_, v___x_8362_);
                v___x_8364_ = lean_box(0);
                v___x_8365_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8365_, 0, v___x_8364_);
                return v___x_8365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(
    mut v_mvarId_8370_: *mut LeanObject,
    mut v_val_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
    mut v___y_8373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8374_: *mut LeanObject = core::ptr::null_mut();
    v_res_8374_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
        v_mvarId_8370_,
        v_val_8371_,
        v___y_8372_,
    );
    lean_dec(v___y_8372_);
    return v_res_8374_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets___lam__0(
    mut v_mvar_8377_: *mut LeanObject,
    mut v_elimTrivial_8378_: u8,
    mut v___y_8379_: *mut LeanObject,
    mut v___y_8380_: *mut LeanObject,
    mut v___y_8381_: *mut LeanObject,
    mut v___y_8382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8409_: usize = 0;
    let mut v___x_8410_: usize = 0;
    let mut v___x_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8415_: u8 = 0;
    let mut v___x_8417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8419_: u8 = 0;
    let mut v_a_8420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8423_: u8 = 0;
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8427_: u8 = 0;
    let mut v_a_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8431_: u8 = 0;
    let mut v___x_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8435_: u8 = 0;
    let mut v_a_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8439_: u8 = 0;
    let mut v___x_8441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8443_: u8 = 0;
    let mut v_a_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8447_: u8 = 0;
    let mut v___x_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8451_: u8 = 0;
    let mut v_a_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8455_: u8 = 0;
    let mut v___x_8457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8459_: u8 = 0;
    let mut v_a_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8463_: u8 = 0;
    let mut v___x_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvar_8377_);
                v___x_8384_ = l_Lean_MVarId_getType(
                    v_mvar_8377_,
                    v___y_8379_,
                    v___y_8380_,
                    v___y_8381_,
                    v___y_8382_,
                );
                if lean_obj_tag(v___x_8384_) == 0 {
                    v_a_8385_ = lean_ctor_get(v___x_8384_, 0);
                    lean_inc(v_a_8385_);
                    lean_dec_ref_known(v___x_8384_, 1);
                    v___x_8386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0;
                    v___x_8387_ = l_Lean_Elab_Tactic_Do_countUses(
                        v_a_8385_,
                        v___x_8386_,
                        v___y_8379_,
                        v___y_8380_,
                        v___y_8381_,
                        v___y_8382_,
                    );
                    if lean_obj_tag(v___x_8387_) == 0 {
                        v_a_8388_ = lean_ctor_get(v___x_8387_, 0);
                        lean_inc(v_a_8388_);
                        lean_dec_ref_known(v___x_8387_, 1);
                        v_fst_8389_ = lean_ctor_get(v_a_8388_, 0);
                        lean_inc(v_fst_8389_);
                        v_snd_8390_ = lean_ctor_get(v_a_8388_, 1);
                        lean_inc(v_snd_8390_);
                        lean_dec(v_a_8388_);
                        v_lctx_8391_ = lean_ctor_get(v___y_8379_, 2);
                        lean_inc_ref(v_lctx_8391_);
                        v___x_8392_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(
                            v_lctx_8391_,
                            v_snd_8390_,
                            v___y_8379_,
                            v___y_8380_,
                            v___y_8381_,
                            v___y_8382_,
                        );
                        if lean_obj_tag(v___x_8392_) == 0 {
                            v_a_8393_ = lean_ctor_get(v___x_8392_, 0);
                            lean_inc(v_a_8393_);
                            lean_dec_ref_known(v___x_8392_, 1);
                            v___x_8394_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0;
                            v_decls_8395_ = lean_ctor_get(v_a_8393_, 1);
                            lean_inc_ref(v_decls_8395_);
                            lean_dec(v_a_8393_);
                            v___x_8396_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_8378_, v_decls_8395_, v___x_8394_, v___y_8379_, v___y_8380_, v___y_8381_, v___y_8382_);
                            lean_dec_ref(v_decls_8395_);
                            if lean_obj_tag(v___x_8396_) == 0 {
                                v_a_8397_ = lean_ctor_get(v___x_8396_, 0);
                                lean_inc(v_a_8397_);
                                lean_dec_ref_known(v___x_8396_, 1);
                                v_fst_8398_ = lean_ctor_get(v_a_8397_, 0);
                                lean_inc(v_fst_8398_);
                                v_snd_8399_ = lean_ctor_get(v_a_8397_, 1);
                                lean_inc(v_snd_8399_);
                                lean_dec(v_a_8397_);
                                v___x_8400_ =
                                    l_Lean_Expr_replaceFVars(v_fst_8389_, v_fst_8398_, v_snd_8399_);
                                lean_dec(v_snd_8399_);
                                lean_dec(v_fst_8389_);
                                v___x_8401_ = l_Lean_Elab_Tactic_Do_elimLetsCore(
                                    v___x_8400_,
                                    v_elimTrivial_8378_,
                                    v___y_8379_,
                                    v___y_8380_,
                                    v___y_8381_,
                                    v___y_8382_,
                                );
                                if lean_obj_tag(v___x_8401_) == 0 {
                                    v_a_8402_ = lean_ctor_get(v___x_8401_, 0);
                                    lean_inc(v_a_8402_);
                                    lean_dec_ref_known(v___x_8401_, 1);
                                    lean_inc(v_mvar_8377_);
                                    v___x_8403_ = l_Lean_MVarId_getTag(
                                        v_mvar_8377_,
                                        v___y_8379_,
                                        v___y_8380_,
                                        v___y_8381_,
                                        v___y_8382_,
                                    );
                                    if lean_obj_tag(v___x_8403_) == 0 {
                                        v_a_8404_ = lean_ctor_get(v___x_8403_, 0);
                                        lean_inc(v_a_8404_);
                                        lean_dec_ref_known(v___x_8403_, 1);
                                        v___x_8405_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                            v_a_8402_,
                                            v_a_8404_,
                                            v___y_8379_,
                                            v___y_8380_,
                                            v___y_8381_,
                                            v___y_8382_,
                                        );
                                        if lean_obj_tag(v___x_8405_) == 0 {
                                            v_a_8406_ = lean_ctor_get(v___x_8405_, 0);
                                            lean_inc_n(v_a_8406_, 2);
                                            lean_dec_ref_known(v___x_8405_, 1);
                                            v___x_8407_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_8377_, v_a_8406_, v___y_8380_);
                                            lean_dec_ref(v___x_8407_);
                                            v___x_8408_ = l_Lean_Expr_mvarId_x21(v_a_8406_);
                                            lean_dec(v_a_8406_);
                                            v_sz_8409_ = lean_array_size(v_fst_8398_);
                                            v___x_8410_ = 0usize;
                                            v___x_8411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_8398_, v_sz_8409_, v___x_8410_, v___x_8408_, v___y_8379_, v___y_8380_, v___y_8381_, v___y_8382_);
                                            lean_dec_ref(v___y_8379_);
                                            lean_dec(v_fst_8398_);
                                            return v___x_8411_;
                                        } else {
                                            lean_dec(v_fst_8398_);
                                            lean_dec_ref(v___y_8379_);
                                            lean_dec(v_mvar_8377_);
                                            v_a_8412_ = lean_ctor_get(v___x_8405_, 0);
                                            v_isSharedCheck_8419_ =
                                                (!lean_is_exclusive(v___x_8405_)) as u8;
                                            if v_isSharedCheck_8419_ == 0 {
                                                v___x_8414_ = v___x_8405_;
                                                v_isShared_8415_ = v_isSharedCheck_8419_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_8412_);
                                                lean_dec(v___x_8405_);
                                                v___x_8414_ = lean_box(0);
                                                v_isShared_8415_ = v_isSharedCheck_8419_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_8402_);
                                        lean_dec(v_fst_8398_);
                                        lean_dec_ref(v___y_8379_);
                                        lean_dec(v_mvar_8377_);
                                        v_a_8420_ = lean_ctor_get(v___x_8403_, 0);
                                        v_isSharedCheck_8427_ =
                                            (!lean_is_exclusive(v___x_8403_)) as u8;
                                        if v_isSharedCheck_8427_ == 0 {
                                            v___x_8422_ = v___x_8403_;
                                            v_isShared_8423_ = v_isSharedCheck_8427_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_8420_);
                                            lean_dec(v___x_8403_);
                                            v___x_8422_ = lean_box(0);
                                            v_isShared_8423_ = v_isSharedCheck_8427_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_8398_);
                                    lean_dec_ref(v___y_8379_);
                                    lean_dec(v_mvar_8377_);
                                    v_a_8428_ = lean_ctor_get(v___x_8401_, 0);
                                    v_isSharedCheck_8435_ = (!lean_is_exclusive(v___x_8401_)) as u8;
                                    if v_isSharedCheck_8435_ == 0 {
                                        v___x_8430_ = v___x_8401_;
                                        v_isShared_8431_ = v_isSharedCheck_8435_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8428_);
                                        lean_dec(v___x_8401_);
                                        v___x_8430_ = lean_box(0);
                                        v_isShared_8431_ = v_isSharedCheck_8435_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_fst_8389_);
                                lean_dec_ref(v___y_8379_);
                                lean_dec(v_mvar_8377_);
                                v_a_8436_ = lean_ctor_get(v___x_8396_, 0);
                                v_isSharedCheck_8443_ = (!lean_is_exclusive(v___x_8396_)) as u8;
                                if v_isSharedCheck_8443_ == 0 {
                                    v___x_8438_ = v___x_8396_;
                                    v_isShared_8439_ = v_isSharedCheck_8443_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_8436_);
                                    lean_dec(v___x_8396_);
                                    v___x_8438_ = lean_box(0);
                                    v_isShared_8439_ = v_isSharedCheck_8443_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_fst_8389_);
                            lean_dec_ref(v___y_8379_);
                            lean_dec(v_mvar_8377_);
                            v_a_8444_ = lean_ctor_get(v___x_8392_, 0);
                            v_isSharedCheck_8451_ = (!lean_is_exclusive(v___x_8392_)) as u8;
                            if v_isSharedCheck_8451_ == 0 {
                                v___x_8446_ = v___x_8392_;
                                v_isShared_8447_ = v_isSharedCheck_8451_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_8444_);
                                lean_dec(v___x_8392_);
                                v___x_8446_ = lean_box(0);
                                v_isShared_8447_ = v_isSharedCheck_8451_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_8379_);
                        lean_dec(v_mvar_8377_);
                        v_a_8452_ = lean_ctor_get(v___x_8387_, 0);
                        v_isSharedCheck_8459_ = (!lean_is_exclusive(v___x_8387_)) as u8;
                        if v_isSharedCheck_8459_ == 0 {
                            v___x_8454_ = v___x_8387_;
                            v_isShared_8455_ = v_isSharedCheck_8459_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_8452_);
                            lean_dec(v___x_8387_);
                            v___x_8454_ = lean_box(0);
                            v_isShared_8455_ = v_isSharedCheck_8459_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_8379_);
                    lean_dec(v_mvar_8377_);
                    v_a_8460_ = lean_ctor_get(v___x_8384_, 0);
                    v_isSharedCheck_8467_ = (!lean_is_exclusive(v___x_8384_)) as u8;
                    if v_isSharedCheck_8467_ == 0 {
                        v___x_8462_ = v___x_8384_;
                        v_isShared_8463_ = v_isSharedCheck_8467_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_8460_);
                        lean_dec(v___x_8384_);
                        v___x_8462_ = lean_box(0);
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
                    v_reuseFailAlloc_8418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8418_, 0, v_a_8412_);
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
                    v_reuseFailAlloc_8426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8426_, 0, v_a_8420_);
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
                    v_reuseFailAlloc_8434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8434_, 0, v_a_8428_);
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
                    v_reuseFailAlloc_8442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8442_, 0, v_a_8436_);
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
                    v_reuseFailAlloc_8450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8450_, 0, v_a_8444_);
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
                    v_reuseFailAlloc_8458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8458_, 0, v_a_8452_);
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
                    v_reuseFailAlloc_8466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8466_, 0, v_a_8460_);
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
    mut v_mvar_8468_: *mut LeanObject,
    mut v_elimTrivial_8469_: *mut LeanObject,
    mut v___y_8470_: *mut LeanObject,
    mut v___y_8471_: *mut LeanObject,
    mut v___y_8472_: *mut LeanObject,
    mut v___y_8473_: *mut LeanObject,
    mut v___y_8474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8475_: u8 = 0;
    let mut v_res_8476_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8475_ = (lean_unbox(v_elimTrivial_8469_) as u8);
    v_res_8476_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(
        v_mvar_8468_,
        v_elimTrivial_boxed_8475_,
        v___y_8470_,
        v___y_8471_,
        v___y_8472_,
        v___y_8473_,
    );
    lean_dec(v___y_8473_);
    lean_dec_ref(v___y_8472_);
    lean_dec(v___y_8471_);
    return v_res_8476_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_elimLets(
    mut v_mvar_8477_: *mut LeanObject,
    mut v_elimTrivial_8478_: u8,
    mut v_a_8479_: *mut LeanObject,
    mut v_a_8480_: *mut LeanObject,
    mut v_a_8481_: *mut LeanObject,
    mut v_a_8482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: *mut LeanObject = core::ptr::null_mut();
    v___x_8484_ = lean_box((v_elimTrivial_8478_) as usize);
    lean_inc(v_mvar_8477_);
    v___f_8485_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_8485_, 0, v_mvar_8477_);
    lean_closure_set(v___f_8485_, 1, v___x_8484_);
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
    mut v_mvar_8487_: *mut LeanObject,
    mut v_elimTrivial_8488_: *mut LeanObject,
    mut v_a_8489_: *mut LeanObject,
    mut v_a_8490_: *mut LeanObject,
    mut v_a_8491_: *mut LeanObject,
    mut v_a_8492_: *mut LeanObject,
    mut v_a_8493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8494_: u8 = 0;
    let mut v_res_8495_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8494_ = (lean_unbox(v_elimTrivial_8488_) as u8);
    v_res_8495_ = l_Lean_Elab_Tactic_Do_elimLets(
        v_mvar_8487_,
        v_elimTrivial_boxed_8494_,
        v_a_8489_,
        v_a_8490_,
        v_a_8491_,
        v_a_8492_,
    );
    lean_dec(v_a_8492_);
    lean_dec_ref(v_a_8491_);
    lean_dec(v_a_8490_);
    lean_dec_ref(v_a_8489_);
    return v_res_8495_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(
    mut v_mvarId_8496_: *mut LeanObject,
    mut v_val_8497_: *mut LeanObject,
    mut v___y_8498_: *mut LeanObject,
    mut v___y_8499_: *mut LeanObject,
    mut v___y_8500_: *mut LeanObject,
    mut v___y_8501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    v___x_8503_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(
        v_mvarId_8496_,
        v_val_8497_,
        v___y_8499_,
    );
    return v___x_8503_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(
    mut v_mvarId_8504_: *mut LeanObject,
    mut v_val_8505_: *mut LeanObject,
    mut v___y_8506_: *mut LeanObject,
    mut v___y_8507_: *mut LeanObject,
    mut v___y_8508_: *mut LeanObject,
    mut v___y_8509_: *mut LeanObject,
    mut v___y_8510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8511_: *mut LeanObject = core::ptr::null_mut();
    v_res_8511_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(
        v_mvarId_8504_,
        v_val_8505_,
        v___y_8506_,
        v___y_8507_,
        v___y_8508_,
        v___y_8509_,
    );
    lean_dec(v___y_8509_);
    lean_dec_ref(v___y_8508_);
    lean_dec(v___y_8507_);
    lean_dec_ref(v___y_8506_);
    return v_res_8511_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(
    mut v_00_u03b2_8512_: *mut LeanObject,
    mut v_x_8513_: *mut LeanObject,
    mut v_x_8514_: *mut LeanObject,
    mut v_x_8515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8516_: *mut LeanObject = core::ptr::null_mut();
    v___x_8516_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_8513_, v_x_8514_, v_x_8515_);
    return v___x_8516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(
    mut v_elimTrivial_8517_: u8,
    mut v_as_8518_: *mut LeanObject,
    mut v_sz_8519_: usize,
    mut v_i_8520_: usize,
    mut v_b_8521_: *mut LeanObject,
    mut v___y_8522_: *mut LeanObject,
    mut v___y_8523_: *mut LeanObject,
    mut v___y_8524_: *mut LeanObject,
    mut v___y_8525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    v___x_8527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_8517_, v_as_8518_, v_sz_8519_, v_i_8520_, v_b_8521_);
    return v___x_8527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(
    mut v_elimTrivial_8528_: *mut LeanObject,
    mut v_as_8529_: *mut LeanObject,
    mut v_sz_8530_: *mut LeanObject,
    mut v_i_8531_: *mut LeanObject,
    mut v_b_8532_: *mut LeanObject,
    mut v___y_8533_: *mut LeanObject,
    mut v___y_8534_: *mut LeanObject,
    mut v___y_8535_: *mut LeanObject,
    mut v___y_8536_: *mut LeanObject,
    mut v___y_8537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8538_: u8 = 0;
    let mut v_sz_boxed_8539_: usize = 0;
    let mut v_i_boxed_8540_: usize = 0;
    let mut v_res_8541_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8538_ = (lean_unbox(v_elimTrivial_8528_) as u8);
    v_sz_boxed_8539_ = lean_unbox_usize(v_sz_8530_);
    lean_dec(v_sz_8530_);
    v_i_boxed_8540_ = lean_unbox_usize(v_i_8531_);
    lean_dec(v_i_8531_);
    v_res_8541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_8538_, v_as_8529_, v_sz_boxed_8539_, v_i_boxed_8540_, v_b_8532_, v___y_8533_, v___y_8534_, v___y_8535_, v___y_8536_);
    lean_dec(v___y_8536_);
    lean_dec_ref(v___y_8535_);
    lean_dec(v___y_8534_);
    lean_dec_ref(v___y_8533_);
    lean_dec_ref(v_as_8529_);
    return v_res_8541_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(
    mut v_00_u03b2_8542_: *mut LeanObject,
    mut v_x_8543_: *mut LeanObject,
    mut v_x_8544_: usize,
    mut v_x_8545_: usize,
    mut v_x_8546_: *mut LeanObject,
    mut v_x_8547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8548_: *mut LeanObject = core::ptr::null_mut();
    v___x_8548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_8543_, v_x_8544_, v_x_8545_, v_x_8546_, v_x_8547_);
    return v___x_8548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_8549_: *mut LeanObject,
    mut v_x_8550_: *mut LeanObject,
    mut v_x_8551_: *mut LeanObject,
    mut v_x_8552_: *mut LeanObject,
    mut v_x_8553_: *mut LeanObject,
    mut v_x_8554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8428__boxed_8555_: usize = 0;
    let mut v_x_8429__boxed_8556_: usize = 0;
    let mut v_res_8557_: *mut LeanObject = core::ptr::null_mut();
    v_x_8428__boxed_8555_ = lean_unbox_usize(v_x_8551_);
    lean_dec(v_x_8551_);
    v_x_8429__boxed_8556_ = lean_unbox_usize(v_x_8552_);
    lean_dec(v_x_8552_);
    v_res_8557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_8549_, v_x_8550_, v_x_8428__boxed_8555_, v_x_8429__boxed_8556_, v_x_8553_, v_x_8554_);
    return v_res_8557_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(
    mut v_elimTrivial_8558_: u8,
    mut v_as_8559_: *mut LeanObject,
    mut v_sz_8560_: usize,
    mut v_i_8561_: usize,
    mut v_b_8562_: *mut LeanObject,
    mut v___y_8563_: *mut LeanObject,
    mut v___y_8564_: *mut LeanObject,
    mut v___y_8565_: *mut LeanObject,
    mut v___y_8566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8568_: *mut LeanObject = core::ptr::null_mut();
    v___x_8568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_8558_, v_as_8559_, v_sz_8560_, v_i_8561_, v_b_8562_);
    return v___x_8568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(
    mut v_elimTrivial_8569_: *mut LeanObject,
    mut v_as_8570_: *mut LeanObject,
    mut v_sz_8571_: *mut LeanObject,
    mut v_i_8572_: *mut LeanObject,
    mut v_b_8573_: *mut LeanObject,
    mut v___y_8574_: *mut LeanObject,
    mut v___y_8575_: *mut LeanObject,
    mut v___y_8576_: *mut LeanObject,
    mut v___y_8577_: *mut LeanObject,
    mut v___y_8578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimTrivial_boxed_8579_: u8 = 0;
    let mut v_sz_boxed_8580_: usize = 0;
    let mut v_i_boxed_8581_: usize = 0;
    let mut v_res_8582_: *mut LeanObject = core::ptr::null_mut();
    v_elimTrivial_boxed_8579_ = (lean_unbox(v_elimTrivial_8569_) as u8);
    v_sz_boxed_8580_ = lean_unbox_usize(v_sz_8571_);
    lean_dec(v_sz_8571_);
    v_i_boxed_8581_ = lean_unbox_usize(v_i_8572_);
    lean_dec(v_i_8572_);
    v_res_8582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_8579_, v_as_8570_, v_sz_boxed_8580_, v_i_boxed_8581_, v_b_8573_, v___y_8574_, v___y_8575_, v___y_8576_, v___y_8577_);
    lean_dec(v___y_8577_);
    lean_dec_ref(v___y_8576_);
    lean_dec(v___y_8575_);
    lean_dec_ref(v___y_8574_);
    lean_dec_ref(v_as_8570_);
    return v_res_8582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(
    mut v_00_u03b2_8583_: *mut LeanObject,
    mut v_n_8584_: *mut LeanObject,
    mut v_k_8585_: *mut LeanObject,
    mut v_v_8586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8587_: *mut LeanObject = core::ptr::null_mut();
    v___x_8587_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_8584_, v_k_8585_, v_v_8586_);
    return v___x_8587_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(
    mut v_00_u03b2_8588_: *mut LeanObject,
    mut v_depth_8589_: usize,
    mut v_keys_8590_: *mut LeanObject,
    mut v_vals_8591_: *mut LeanObject,
    mut v_heq_8592_: *mut LeanObject,
    mut v_i_8593_: *mut LeanObject,
    mut v_entries_8594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8595_: *mut LeanObject = core::ptr::null_mut();
    v___x_8595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_8589_, v_keys_8590_, v_vals_8591_, v_i_8593_, v_entries_8594_);
    return v___x_8595_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(
    mut v_00_u03b2_8596_: *mut LeanObject,
    mut v_depth_8597_: *mut LeanObject,
    mut v_keys_8598_: *mut LeanObject,
    mut v_vals_8599_: *mut LeanObject,
    mut v_heq_8600_: *mut LeanObject,
    mut v_i_8601_: *mut LeanObject,
    mut v_entries_8602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_8603_: usize = 0;
    let mut v_res_8604_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_8603_ = lean_unbox_usize(v_depth_8597_);
    lean_dec(v_depth_8597_);
    v_res_8604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_8596_, v_depth_boxed_8603_, v_keys_8598_, v_vals_8599_, v_heq_8600_, v_i_8601_, v_entries_8602_);
    lean_dec_ref(v_vals_8599_);
    lean_dec_ref(v_keys_8598_);
    return v_res_8604_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(
    mut v_00_u03b2_8605_: *mut LeanObject,
    mut v_x_8606_: *mut LeanObject,
    mut v_x_8607_: *mut LeanObject,
    mut v_x_8608_: *mut LeanObject,
    mut v_x_8609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8610_: *mut LeanObject = core::ptr::null_mut();
    v___x_8610_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_8606_, v_x_8607_, v_x_8608_, v_x_8609_);
    return v___x_8610_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_instInhabitedUses_default =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
    l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 =
        _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_LetElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
