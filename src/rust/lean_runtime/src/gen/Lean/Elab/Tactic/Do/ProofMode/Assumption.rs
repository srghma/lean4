// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Assumption
// Imports: Lean.Elab.Tactic.Do.ProofMode.Exact Lean.Meta.Tactic.Assumption
use crate::r#gen::Init::Control::Option::l_OptionT_instInhabitedOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_pure___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Exact::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Exact,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f, l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkAppB,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_Meta_findLocalDeclWithType_x3f,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value: LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value: LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value: LeanStringObject<6> =
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
        m_data: [83, 80, 114, 101, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 110, 116, 97, 105, 108, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value: LeanStringObject<5> =
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
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_3: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value)
                as *mut LeanObject,
            515334035361346902 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value)
                as *mut LeanObject,
            1565800902179044421 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [65, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value: LeanStringObject<5> =
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
        m_data: [108, 101, 102, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
                as *mut LeanObject,
            18104247681175793831 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value)
                as *mut LeanObject,
            385610338673087938 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value)
                as *mut LeanObject,
            11125855241591742299 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
            as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
            as *mut LeanObject,
        18104247681175793831 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value)
            as *mut LeanObject,
        385610338673087938 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value)
                as *mut LeanObject,
            16860071401557120685 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12_value: LeanStringObject<
    41,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 65, 115, 115, 117, 109, 112, 116, 105, 111, 110,
        0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13_value: LeanStringObject<
    47,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 46, 97, 115, 115, 117,
        109, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14_value: LeanStringObject<
    49,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 58, 32, 104, 121, 112, 111, 116, 104, 101,
        115, 105, 115, 32, 119, 105, 116, 104, 111, 117, 116, 32, 112, 114, 111, 112, 101, 114, 32,
        109, 101, 116, 97, 100, 97, 116, 97, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 97, 117, 116, 111, 108, 111, 103, 105, 99, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
            as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_3:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
            as *mut LeanObject,
        18104247681175793831 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value)
            as *mut LeanObject,
        14581852829424383138 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value:
    LeanStringObject<21> = LeanStringObject {
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
        80, 114, 111, 112, 65, 115, 83, 80, 114, 101, 100, 84, 97, 117, 116, 111, 108, 111, 103,
        121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
            as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_3:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
            as *mut LeanObject,
        18104247681175793831 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value)
            as *mut LeanObject,
        2932917581903347504 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [69, 120, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value:
    LeanStringObject<15> = LeanStringObject {
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
        102, 114, 111, 109, 95, 116, 97, 117, 116, 111, 108, 111, 103, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value)
            as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_3:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value)
            as *mut LeanObject,
        18104247681175793831 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_4:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value)
            as *mut LeanObject,
        3997838883980794615 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value)
            as *mut LeanObject,
        18101383377255682623 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0_value:
    LeanStringObject<21> = LeanStringObject {
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
        104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 110, 111, 116, 32, 102, 111, 117,
        110, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        110, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value) as *mut LeanObject,1814919757381564531 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 77, 65, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value) as *mut LeanObject,14852202169383584319 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value) as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v___x_934_ = l_instMonadEIO(lean_box(0));
    return v___x_934_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(
    mut v_msg_937_: *mut LeanObject,
    mut v___y_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
    mut v___y_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v_toFunctor_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_955_: u8 = 0;
    let mut v___f_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557__overap_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_975_: u8 = 0;
    let mut v_unused_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut v_unused_978_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_943_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0_once), _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0);
                v___x_944_ = l_StateRefT_x27_instMonad___redArg(v___x_943_);
                v_toApplicative_945_ = lean_ctor_get(v___x_944_, 0);
                v_isSharedCheck_977_ = (!lean_is_exclusive(v___x_944_)) as u8;
                if v_isSharedCheck_977_ == 0 {
                    v_unused_978_ = lean_ctor_get(v___x_944_, 1);
                    lean_dec(v_unused_978_);
                    v___x_947_ = v___x_944_;
                    v_isShared_948_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_945_);
                    lean_dec(v___x_944_);
                    v___x_947_ = lean_box(0);
                    v_isShared_948_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_949_ = lean_ctor_get(v_toApplicative_945_, 0);
                v_toSeq_950_ = lean_ctor_get(v_toApplicative_945_, 2);
                v_toSeqLeft_951_ = lean_ctor_get(v_toApplicative_945_, 3);
                v_toSeqRight_952_ = lean_ctor_get(v_toApplicative_945_, 4);
                v_isSharedCheck_975_ = (!lean_is_exclusive(v_toApplicative_945_)) as u8;
                if v_isSharedCheck_975_ == 0 {
                    v_unused_976_ = lean_ctor_get(v_toApplicative_945_, 1);
                    lean_dec(v_unused_976_);
                    v___x_954_ = v_toApplicative_945_;
                    v_isShared_955_ = v_isSharedCheck_975_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_952_);
                    lean_inc(v_toSeqLeft_951_);
                    lean_inc(v_toSeq_950_);
                    lean_inc(v_toFunctor_949_);
                    lean_dec(v_toApplicative_945_);
                    v___x_954_ = lean_box(0);
                    v_isShared_955_ = v_isSharedCheck_975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_956_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1;
                v___f_957_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_949_);
                v___f_958_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_958_, 0, v_toFunctor_949_);
                v___f_959_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_959_, 0, v_toFunctor_949_);
                v___x_960_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_960_, 0, v___f_958_);
                lean_ctor_set(v___x_960_, 1, v___f_959_);
                v___f_961_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_961_, 0, v_toSeqRight_952_);
                v___f_962_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_962_, 0, v_toSeqLeft_951_);
                v___f_963_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_963_, 0, v_toSeq_950_);
                if v_isShared_955_ == 0 {
                    lean_ctor_set(v___x_954_, 4, v___f_961_);
                    lean_ctor_set(v___x_954_, 3, v___f_962_);
                    lean_ctor_set(v___x_954_, 2, v___f_963_);
                    lean_ctor_set(v___x_954_, 1, v___f_956_);
                    lean_ctor_set(v___x_954_, 0, v___x_960_);
                    v___x_965_ = v___x_954_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_960_);
                    lean_ctor_set(v_reuseFailAlloc_974_, 1, v___f_956_);
                    lean_ctor_set(v_reuseFailAlloc_974_, 2, v___f_963_);
                    lean_ctor_set(v_reuseFailAlloc_974_, 3, v___f_962_);
                    lean_ctor_set(v_reuseFailAlloc_974_, 4, v___f_961_);
                    v___x_965_ = v_reuseFailAlloc_974_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_948_ == 0 {
                    lean_ctor_set(v___x_947_, 1, v___f_957_);
                    lean_ctor_set(v___x_947_, 0, v___x_965_);
                    v___x_967_ = v___x_947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_965_);
                    lean_ctor_set(v_reuseFailAlloc_973_, 1, v___f_957_);
                    v___x_967_ = v_reuseFailAlloc_973_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_968_ = l_StateRefT_x27_instMonad___redArg(v___x_967_);
                v___x_969_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_969_, 0, lean_box(0));
                lean_closure_set(v___x_969_, 1, lean_box(0));
                lean_closure_set(v___x_969_, 2, v___x_968_);
                v___x_970_ = l_OptionT_instInhabitedOfPure___redArg(v___x_969_);
                v___x_3557__overap_971_ = lean_panic_fn_borrowed(v___x_970_, v_msg_937_);
                lean_dec(v___x_970_);
                lean_inc(v___y_941_);
                lean_inc_ref(v___y_940_);
                lean_inc(v___y_939_);
                lean_inc_ref(v___y_938_);
                v___x_972_ = lean_apply_5(
                    v___x_3557__overap_971_,
                    v___y_938_,
                    v___y_939_,
                    v___y_940_,
                    v___y_941_,
                    lean_box(0),
                );
                return v___x_972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___boxed(
    mut v_msg_979_: *mut LeanObject,
    mut v___y_980_: *mut LeanObject,
    mut v___y_981_: *mut LeanObject,
    mut v___y_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_985_: *mut LeanObject = core::ptr::null_mut();
    v_res_985_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(
        v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_,
    );
    lean_dec(v___y_983_);
    lean_dec_ref(v___y_982_);
    lean_dec(v___y_981_);
    lean_dec_ref(v___y_980_);
    return v_res_985_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
    mut v_goal_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1034_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v_unused_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v_p_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut v_a_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1072_: u8 = 0;
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1088_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v_val_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_unused_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v_val_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut v_unused_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_1024_ = lean_ctor_get(v_goal_1018_, 0);
                v_00_u03c3s_1025_ = lean_ctor_get(v_goal_1018_, 1);
                v_hyps_1026_ = lean_ctor_get(v_goal_1018_, 2);
                v_target_1027_ = lean_ctor_get(v_goal_1018_, 3);
                v_isSharedCheck_1152_ = (!lean_is_exclusive(v_goal_1018_)) as u8;
                if v_isSharedCheck_1152_ == 0 {
                    v___x_1029_ = v_goal_1018_;
                    v_isShared_1030_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_target_1027_);
                    lean_inc(v_hyps_1026_);
                    lean_inc(v_00_u03c3s_1025_);
                    lean_inc(v_u_1024_);
                    lean_dec(v_goal_1018_);
                    v___x_1029_ = lean_box(0);
                    v_isShared_1030_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_hyps_1026_);
                v___x_1031_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_hyps_1026_);
                if lean_obj_tag(v___x_1031_) == 1 {
                    lean_del_object(v___x_1029_);
                    lean_dec_ref(v_target_1027_);
                    lean_dec_ref(v_hyps_1026_);
                    lean_dec_ref(v_00_u03c3s_1025_);
                    lean_dec(v_u_1024_);
                    v_isSharedCheck_1039_ = (!lean_is_exclusive(v___x_1031_)) as u8;
                    if v_isSharedCheck_1039_ == 0 {
                        v_unused_1040_ = lean_ctor_get(v___x_1031_, 0);
                        lean_dec(v_unused_1040_);
                        v___x_1033_ = v___x_1031_;
                        v_isShared_1034_ = v_isSharedCheck_1039_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_1031_);
                        v___x_1033_ = lean_box(0);
                        v_isShared_1034_ = v_isSharedCheck_1039_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1031_);
                    lean_inc_ref(v_hyps_1026_);
                    v___x_1041_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_hyps_1026_);
                    if lean_obj_tag(v___x_1041_) == 1 {
                        lean_del_object(v___x_1029_);
                        lean_dec_ref(v_hyps_1026_);
                        v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
                        v_isSharedCheck_1077_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                        if v_isSharedCheck_1077_ == 0 {
                            v___x_1044_ = v___x_1041_;
                            v_isShared_1045_ = v_isSharedCheck_1077_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1042_);
                            lean_dec(v___x_1041_);
                            v___x_1044_ = lean_box(0);
                            v_isShared_1045_ = v_isSharedCheck_1077_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1041_);
                        v___x_1078_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_1026_);
                        if lean_obj_tag(v___x_1078_) == 1 {
                            lean_dec_ref(v_hyps_1026_);
                            v_val_1079_ = lean_ctor_get(v___x_1078_, 0);
                            lean_inc(v_val_1079_);
                            lean_dec_ref_known(v___x_1078_, 1);
                            v_snd_1080_ = lean_ctor_get(v_val_1079_, 1);
                            lean_inc(v_snd_1080_);
                            v_snd_1081_ = lean_ctor_get(v_snd_1080_, 1);
                            lean_inc(v_snd_1081_);
                            v_fst_1082_ = lean_ctor_get(v_val_1079_, 0);
                            lean_inc(v_fst_1082_);
                            lean_dec(v_val_1079_);
                            v_fst_1083_ = lean_ctor_get(v_snd_1080_, 0);
                            lean_inc(v_fst_1083_);
                            lean_dec(v_snd_1080_);
                            v_fst_1084_ = lean_ctor_get(v_snd_1081_, 0);
                            v_snd_1085_ = lean_ctor_get(v_snd_1081_, 1);
                            v_isSharedCheck_1142_ = (!lean_is_exclusive(v_snd_1081_)) as u8;
                            if v_isSharedCheck_1142_ == 0 {
                                v___x_1087_ = v_snd_1081_;
                                v_isShared_1088_ = v_isSharedCheck_1142_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_snd_1085_);
                                lean_inc(v_fst_1084_);
                                lean_dec(v_snd_1081_);
                                v___x_1087_ = lean_box(0);
                                v_isShared_1088_ = v_isSharedCheck_1142_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1078_);
                            lean_del_object(v___x_1029_);
                            lean_dec_ref(v_target_1027_);
                            lean_dec_ref(v_00_u03c3s_1025_);
                            lean_dec(v_u_1024_);
                            v___x_1143_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12;
                            v___x_1144_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13;
                            v___x_1145_ = lean_unsigned_to_nat(30);
                            v___x_1146_ = lean_unsigned_to_nat(4);
                            v___x_1147_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14;
                            v___x_1148_ = lean_expr_dbg_to_string(v_hyps_1026_);
                            lean_dec_ref(v_hyps_1026_);
                            v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
                            lean_dec_ref(v___x_1148_);
                            v___x_1150_ = l_mkPanicMessageWithDecl(
                                v___x_1143_,
                                v___x_1144_,
                                v___x_1145_,
                                v___x_1146_,
                                v___x_1149_,
                            );
                            lean_dec_ref(v___x_1149_);
                            v___x_1151_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(v___x_1150_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
                            return v___x_1151_;
                        }
                    }
                }
            }
            2 => {
                v___x_1035_ = lean_box(0);
                if v_isShared_1034_ == 0 {
                    lean_ctor_set_tag(v___x_1033_, 0);
                    lean_ctor_set(v___x_1033_, 0, v___x_1035_);
                    v___x_1037_ = v___x_1033_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1037_;
            }
            4 => {
                v_p_1046_ = lean_ctor_get(v_val_1042_, 2);
                lean_inc_ref_n(v_p_1046_, 2);
                lean_dec(v_val_1042_);
                v___x_1047_ = l_Lean_Meta_isExprDefEq(
                    v_p_1046_,
                    v_target_1027_,
                    v_a_1019_,
                    v_a_1020_,
                    v_a_1021_,
                    v_a_1022_,
                );
                if lean_obj_tag(v___x_1047_) == 0 {
                    v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
                    v_isSharedCheck_1068_ = (!lean_is_exclusive(v___x_1047_)) as u8;
                    if v_isSharedCheck_1068_ == 0 {
                        v___x_1050_ = v___x_1047_;
                        v_isShared_1051_ = v_isSharedCheck_1068_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1048_);
                        lean_dec(v___x_1047_);
                        v___x_1050_ = lean_box(0);
                        v_isShared_1051_ = v_isSharedCheck_1068_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_1046_);
                    lean_del_object(v___x_1044_);
                    lean_dec_ref(v_00_u03c3s_1025_);
                    lean_dec(v_u_1024_);
                    v_a_1069_ = lean_ctor_get(v___x_1047_, 0);
                    v_isSharedCheck_1076_ = (!lean_is_exclusive(v___x_1047_)) as u8;
                    if v_isSharedCheck_1076_ == 0 {
                        v___x_1071_ = v___x_1047_;
                        v_isShared_1072_ = v_isSharedCheck_1076_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1069_);
                        lean_dec(v___x_1047_);
                        v___x_1071_ = lean_box(0);
                        v_isShared_1072_ = v_isSharedCheck_1076_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1052_ = (lean_unbox(v_a_1048_) as u8);
                lean_dec(v_a_1048_);
                if v___x_1052_ == 0 {
                    lean_dec_ref(v_p_1046_);
                    lean_del_object(v___x_1044_);
                    lean_dec_ref(v_00_u03c3s_1025_);
                    lean_dec(v_u_1024_);
                    v___x_1053_ = lean_box(0);
                    if v_isShared_1051_ == 0 {
                        lean_ctor_set(v___x_1050_, 0, v___x_1053_);
                        v___x_1055_ = v___x_1050_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
                        v___x_1055_ = v_reuseFailAlloc_1056_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1057_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5;
                    v___x_1058_ = lean_box(0);
                    v___x_1059_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1059_, 0, v_u_1024_);
                    lean_ctor_set(v___x_1059_, 1, v___x_1058_);
                    v___x_1060_ = l_Lean_mkConst(v___x_1057_, v___x_1059_);
                    v___x_1061_ = l_Lean_mkAppB(v___x_1060_, v_00_u03c3s_1025_, v_p_1046_);
                    if v_isShared_1045_ == 0 {
                        lean_ctor_set(v___x_1044_, 0, v___x_1061_);
                        v___x_1063_ = v___x_1044_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1061_);
                        v___x_1063_ = v_reuseFailAlloc_1067_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1055_;
            }
            7 => {
                if v_isShared_1051_ == 0 {
                    lean_ctor_set(v___x_1050_, 0, v___x_1063_);
                    v___x_1065_ = v___x_1050_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
                    v___x_1065_ = v_reuseFailAlloc_1066_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1065_;
            }
            9 => {
                if v_isShared_1072_ == 0 {
                    v___x_1074_ = v___x_1071_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
                    v___x_1074_ = v_reuseFailAlloc_1075_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1074_;
            }
            11 => {
                v___x_1089_ = lean_box(0);
                if v_isShared_1088_ == 0 {
                    lean_ctor_set_tag(v___x_1087_, 1);
                    lean_ctor_set(v___x_1087_, 1, v___x_1089_);
                    lean_ctor_set(v___x_1087_, 0, v_fst_1082_);
                    v___x_1091_ = v___x_1087_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_fst_1082_);
                    lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1089_);
                    v___x_1091_ = v_reuseFailAlloc_1141_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_inc_ref(v_target_1027_);
                lean_inc(v_snd_1085_);
                lean_inc_ref(v_00_u03c3s_1025_);
                lean_inc(v_u_1024_);
                v___x_1119_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1119_, 0, v_u_1024_);
                lean_ctor_set(v___x_1119_, 1, v_00_u03c3s_1025_);
                lean_ctor_set(v___x_1119_, 2, v_snd_1085_);
                lean_ctor_set(v___x_1119_, 3, v_target_1027_);
                v___x_1120_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                    v___x_1119_,
                    v_a_1019_,
                    v_a_1020_,
                    v_a_1021_,
                    v_a_1022_,
                );
                if lean_obj_tag(v___x_1120_) == 0 {
                    v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
                    lean_inc(v_a_1121_);
                    if lean_obj_tag(v_a_1121_) == 0 {
                        v___y_1093_ = v___x_1120_;
                        state = 13;
                        continue;
                    } else {
                        lean_del_object(v___x_1029_);
                        lean_dec_ref(v_00_u03c3s_1025_);
                        lean_dec(v_u_1024_);
                        v_isSharedCheck_1139_ = (!lean_is_exclusive(v___x_1120_)) as u8;
                        if v_isSharedCheck_1139_ == 0 {
                            v_unused_1140_ = lean_ctor_get(v___x_1120_, 0);
                            lean_dec(v_unused_1140_);
                            v___x_1123_ = v___x_1120_;
                            v_isShared_1124_ = v_isSharedCheck_1139_;
                            state = 19;
                            continue;
                        } else {
                            lean_dec(v___x_1120_);
                            v___x_1123_ = lean_box(0);
                            v_isShared_1124_ = v_isSharedCheck_1139_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v___y_1093_ = v___x_1120_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if lean_obj_tag(v___y_1093_) == 0 {
                    v_a_1094_ = lean_ctor_get(v___y_1093_, 0);
                    if lean_obj_tag(v_a_1094_) == 0 {
                        lean_dec_ref_known(v___y_1093_, 1);
                        lean_inc_ref(v_target_1027_);
                        lean_inc(v_fst_1084_);
                        if v_isShared_1030_ == 0 {
                            lean_ctor_set(v___x_1029_, 2, v_fst_1084_);
                            v___x_1096_ = v___x_1029_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_u_1024_);
                            lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_00_u03c3s_1025_);
                            lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_fst_1084_);
                            lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_target_1027_);
                            v___x_1096_ = v_reuseFailAlloc_1118_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1091_);
                        lean_dec(v_snd_1085_);
                        lean_dec(v_fst_1084_);
                        lean_dec(v_fst_1083_);
                        lean_del_object(v___x_1029_);
                        lean_dec_ref(v_target_1027_);
                        lean_dec_ref(v_00_u03c3s_1025_);
                        lean_dec(v_u_1024_);
                        return v___y_1093_;
                    }
                } else {
                    lean_dec_ref(v___x_1091_);
                    lean_dec(v_snd_1085_);
                    lean_dec(v_fst_1084_);
                    lean_dec(v_fst_1083_);
                    lean_del_object(v___x_1029_);
                    lean_dec_ref(v_target_1027_);
                    lean_dec_ref(v_00_u03c3s_1025_);
                    lean_dec(v_u_1024_);
                    return v___y_1093_;
                }
            }
            14 => {
                v___x_1097_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                    v___x_1096_,
                    v_a_1019_,
                    v_a_1020_,
                    v_a_1021_,
                    v_a_1022_,
                );
                if lean_obj_tag(v___x_1097_) == 0 {
                    v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
                    lean_inc(v_a_1098_);
                    if lean_obj_tag(v_a_1098_) == 0 {
                        lean_dec_ref(v___x_1091_);
                        lean_dec(v_snd_1085_);
                        lean_dec(v_fst_1084_);
                        lean_dec(v_fst_1083_);
                        lean_dec_ref(v_target_1027_);
                        return v___x_1097_;
                    } else {
                        v_isSharedCheck_1116_ = (!lean_is_exclusive(v___x_1097_)) as u8;
                        if v_isSharedCheck_1116_ == 0 {
                            v_unused_1117_ = lean_ctor_get(v___x_1097_, 0);
                            lean_dec(v_unused_1117_);
                            v___x_1100_ = v___x_1097_;
                            v_isShared_1101_ = v_isSharedCheck_1116_;
                            state = 15;
                            continue;
                        } else {
                            lean_dec(v___x_1097_);
                            v___x_1100_ = lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1116_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1091_);
                    lean_dec(v_snd_1085_);
                    lean_dec(v_fst_1084_);
                    lean_dec(v_fst_1083_);
                    lean_dec_ref(v_target_1027_);
                    return v___x_1097_;
                }
            }
            15 => {
                v_val_1102_ = lean_ctor_get(v_a_1098_, 0);
                v_isSharedCheck_1115_ = (!lean_is_exclusive(v_a_1098_)) as u8;
                if v_isSharedCheck_1115_ == 0 {
                    v___x_1104_ = v_a_1098_;
                    v_isShared_1105_ = v_isSharedCheck_1115_;
                    state = 16;
                    continue;
                } else {
                    lean_inc(v_val_1102_);
                    lean_dec(v_a_1098_);
                    v___x_1104_ = lean_box(0);
                    v_isShared_1105_ = v_isSharedCheck_1115_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1106_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9;
                v___x_1107_ = l_Lean_mkConst(v___x_1106_, v___x_1091_);
                v___x_1108_ = l_Lean_mkApp5(
                    v___x_1107_,
                    v_fst_1083_,
                    v_fst_1084_,
                    v_snd_1085_,
                    v_target_1027_,
                    v_val_1102_,
                );
                if v_isShared_1105_ == 0 {
                    lean_ctor_set(v___x_1104_, 0, v___x_1108_);
                    v___x_1110_ = v___x_1104_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
                    v___x_1110_ = v_reuseFailAlloc_1114_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1101_ == 0 {
                    lean_ctor_set(v___x_1100_, 0, v___x_1110_);
                    v___x_1112_ = v___x_1100_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1112_;
            }
            19 => {
                v_val_1125_ = lean_ctor_get(v_a_1121_, 0);
                v_isSharedCheck_1138_ = (!lean_is_exclusive(v_a_1121_)) as u8;
                if v_isSharedCheck_1138_ == 0 {
                    v___x_1127_ = v_a_1121_;
                    v_isShared_1128_ = v_isSharedCheck_1138_;
                    state = 20;
                    continue;
                } else {
                    lean_inc(v_val_1125_);
                    lean_dec(v_a_1121_);
                    v___x_1127_ = lean_box(0);
                    v_isShared_1128_ = v_isSharedCheck_1138_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_1129_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11;
                v___x_1130_ = l_Lean_mkConst(v___x_1129_, v___x_1091_);
                v___x_1131_ = l_Lean_mkApp5(
                    v___x_1130_,
                    v_fst_1083_,
                    v_fst_1084_,
                    v_snd_1085_,
                    v_target_1027_,
                    v_val_1125_,
                );
                if v_isShared_1128_ == 0 {
                    lean_ctor_set(v___x_1127_, 0, v___x_1131_);
                    v___x_1133_ = v___x_1127_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1131_);
                    v___x_1133_ = v_reuseFailAlloc_1137_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_1124_ == 0 {
                    lean_ctor_set(v___x_1123_, 0, v___x_1133_);
                    v___x_1135_ = v___x_1123_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
                    v___x_1135_ = v_reuseFailAlloc_1136_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___boxed(
    mut v_goal_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1159_: *mut LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
        v_goal_1153_,
        v_a_1154_,
        v_a_1155_,
        v_a_1156_,
        v_a_1157_,
    );
    lean_dec(v_a_1157_);
    lean_dec_ref(v_a_1156_);
    lean_dec(v_a_1155_);
    lean_dec_ref(v_a_1154_);
    return v_res_1159_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(
    mut v_goal_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1216_: u8 = 0;
    let mut v_val_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_unused_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v_a_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1238_: u8 = 0;
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_1189_ = lean_ctor_get(v_goal_1183_, 0);
                lean_inc(v_u_1189_);
                v_00_u03c3s_1190_ = lean_ctor_get(v_goal_1183_, 1);
                lean_inc_ref_n(v_00_u03c3s_1190_, 2);
                v_hyps_1191_ = lean_ctor_get(v_goal_1183_, 2);
                lean_inc_ref(v_hyps_1191_);
                v_target_1192_ = lean_ctor_get(v_goal_1183_, 3);
                lean_inc_ref_n(v_target_1192_, 2);
                lean_dec_ref(v_goal_1183_);
                v___x_1193_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1;
                v___x_1194_ = lean_box(0);
                v___x_1195_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1195_, 0, v_u_1189_);
                lean_ctor_set(v___x_1195_, 1, v___x_1194_);
                lean_inc_ref(v___x_1195_);
                v___x_1196_ = l_Lean_mkConst(v___x_1193_, v___x_1195_);
                v_00_u03c6_1197_ = l_Lean_mkAppB(v___x_1196_, v_00_u03c3s_1190_, v_target_1192_);
                lean_inc_ref(v_00_u03c6_1197_);
                v___x_1198_ = l_Lean_Meta_findLocalDeclWithType_x3f(
                    v_00_u03c6_1197_,
                    v_a_1184_,
                    v_a_1185_,
                    v_a_1186_,
                    v_a_1187_,
                );
                if lean_obj_tag(v___x_1198_) == 0 {
                    v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
                    v_isSharedCheck_1234_ = (!lean_is_exclusive(v___x_1198_)) as u8;
                    if v_isSharedCheck_1234_ == 0 {
                        v___x_1201_ = v___x_1198_;
                        v_isShared_1202_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1199_);
                        lean_dec(v___x_1198_);
                        v___x_1201_ = lean_box(0);
                        v_isShared_1202_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_00_u03c6_1197_);
                    lean_dec_ref_known(v___x_1195_, 2);
                    lean_dec_ref(v_target_1192_);
                    lean_dec_ref(v_hyps_1191_);
                    lean_dec_ref(v_00_u03c3s_1190_);
                    v_a_1235_ = lean_ctor_get(v___x_1198_, 0);
                    v_isSharedCheck_1242_ = (!lean_is_exclusive(v___x_1198_)) as u8;
                    if v_isSharedCheck_1242_ == 0 {
                        v___x_1237_ = v___x_1198_;
                        v_isShared_1238_ = v_isSharedCheck_1242_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1235_);
                        lean_dec(v___x_1198_);
                        v___x_1237_ = lean_box(0);
                        v_isShared_1238_ = v_isSharedCheck_1242_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1199_) == 0 {
                    lean_dec_ref(v_00_u03c6_1197_);
                    lean_dec_ref_known(v___x_1195_, 2);
                    lean_dec_ref(v_target_1192_);
                    lean_dec_ref(v_hyps_1191_);
                    lean_dec_ref(v_00_u03c3s_1190_);
                    v___x_1203_ = lean_box(0);
                    if v_isShared_1202_ == 0 {
                        lean_ctor_set(v___x_1201_, 0, v___x_1203_);
                        v___x_1205_ = v___x_1201_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
                        v___x_1205_ = v_reuseFailAlloc_1206_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1201_);
                    v_val_1207_ = lean_ctor_get(v_a_1199_, 0);
                    lean_inc(v_val_1207_);
                    lean_dec_ref_known(v_a_1199_, 1);
                    v___x_1208_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3;
                    lean_inc_ref(v___x_1195_);
                    v___x_1209_ = l_Lean_mkConst(v___x_1208_, v___x_1195_);
                    lean_inc_ref(v_target_1192_);
                    lean_inc_ref(v_00_u03c3s_1190_);
                    lean_inc_ref(v_00_u03c6_1197_);
                    v___x_1210_ = l_Lean_mkApp3(
                        v___x_1209_,
                        v_00_u03c6_1197_,
                        v_00_u03c3s_1190_,
                        v_target_1192_,
                    );
                    v___x_1211_ = lean_box(0);
                    v___x_1212_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_1210_,
                        v___x_1211_,
                        v_a_1184_,
                        v_a_1185_,
                        v_a_1186_,
                        v_a_1187_,
                    );
                    if lean_obj_tag(v___x_1212_) == 0 {
                        v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
                        lean_inc(v_a_1213_);
                        if lean_obj_tag(v_a_1213_) == 0 {
                            lean_dec(v_val_1207_);
                            lean_dec_ref(v_00_u03c6_1197_);
                            lean_dec_ref_known(v___x_1195_, 2);
                            lean_dec_ref(v_target_1192_);
                            lean_dec_ref(v_hyps_1191_);
                            lean_dec_ref(v_00_u03c3s_1190_);
                            return v___x_1212_;
                        } else {
                            v_isSharedCheck_1232_ = (!lean_is_exclusive(v___x_1212_)) as u8;
                            if v_isSharedCheck_1232_ == 0 {
                                v_unused_1233_ = lean_ctor_get(v___x_1212_, 0);
                                lean_dec(v_unused_1233_);
                                v___x_1215_ = v___x_1212_;
                                v_isShared_1216_ = v_isSharedCheck_1232_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_1212_);
                                v___x_1215_ = lean_box(0);
                                v_isShared_1216_ = v_isSharedCheck_1232_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_1207_);
                        lean_dec_ref(v_00_u03c6_1197_);
                        lean_dec_ref_known(v___x_1195_, 2);
                        lean_dec_ref(v_target_1192_);
                        lean_dec_ref(v_hyps_1191_);
                        lean_dec_ref(v_00_u03c3s_1190_);
                        return v___x_1212_;
                    }
                }
            }
            2 => {
                return v___x_1205_;
            }
            3 => {
                v_val_1217_ = lean_ctor_get(v_a_1213_, 0);
                v_isSharedCheck_1231_ = (!lean_is_exclusive(v_a_1213_)) as u8;
                if v_isSharedCheck_1231_ == 0 {
                    v___x_1219_ = v_a_1213_;
                    v_isShared_1220_ = v_isSharedCheck_1231_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_1217_);
                    lean_dec(v_a_1213_);
                    v___x_1219_ = lean_box(0);
                    v_isShared_1220_ = v_isSharedCheck_1231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1221_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6;
                v___x_1222_ = l_Lean_mkConst(v___x_1221_, v___x_1195_);
                v___x_1223_ = l_Lean_Expr_fvar___override(v_val_1207_);
                v___x_1224_ = l_Lean_mkApp6(
                    v___x_1222_,
                    v_00_u03c3s_1190_,
                    v_00_u03c6_1197_,
                    v_hyps_1191_,
                    v_target_1192_,
                    v_val_1217_,
                    v___x_1223_,
                );
                if v_isShared_1220_ == 0 {
                    lean_ctor_set(v___x_1219_, 0, v___x_1224_);
                    v___x_1226_ = v___x_1219_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1224_);
                    v___x_1226_ = v_reuseFailAlloc_1230_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1216_ == 0 {
                    lean_ctor_set(v___x_1215_, 0, v___x_1226_);
                    v___x_1228_ = v___x_1215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
                    v___x_1228_ = v_reuseFailAlloc_1229_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1228_;
            }
            7 => {
                if v_isShared_1238_ == 0 {
                    v___x_1240_ = v___x_1237_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
                    v___x_1240_ = v_reuseFailAlloc_1241_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___boxed(
    mut v_goal_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
    mut v_a_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(
        v_goal_1243_,
        v_a_1244_,
        v_a_1245_,
        v_a_1246_,
        v_a_1247_,
    );
    lean_dec(v_a_1247_);
    lean_dec_ref(v_a_1246_);
    lean_dec(v_a_1245_);
    lean_dec_ref(v_a_1244_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(
    mut v_e_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1273_: u8 = 0;
    let mut v_unused_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = l_Lean_Expr_hasMVar(v_e_1250_);
                if v___x_1253_ == 0 {
                    v___x_1254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1254_, 0, v_e_1250_);
                    return v___x_1254_;
                } else {
                    v___x_1255_ = lean_st_ref_get(v___y_1251_);
                    v_mctx_1256_ = lean_ctor_get(v___x_1255_, 0);
                    lean_inc_ref(v_mctx_1256_);
                    lean_dec(v___x_1255_);
                    v___x_1257_ = l_Lean_instantiateMVarsCore(v_mctx_1256_, v_e_1250_);
                    v_fst_1258_ = lean_ctor_get(v___x_1257_, 0);
                    lean_inc(v_fst_1258_);
                    v_snd_1259_ = lean_ctor_get(v___x_1257_, 1);
                    lean_inc(v_snd_1259_);
                    lean_dec_ref(v___x_1257_);
                    v___x_1260_ = lean_st_ref_take(v___y_1251_);
                    v_cache_1261_ = lean_ctor_get(v___x_1260_, 1);
                    v_zetaDeltaFVarIds_1262_ = lean_ctor_get(v___x_1260_, 2);
                    v_postponed_1263_ = lean_ctor_get(v___x_1260_, 3);
                    v_diag_1264_ = lean_ctor_get(v___x_1260_, 4);
                    v_isSharedCheck_1273_ = (!lean_is_exclusive(v___x_1260_)) as u8;
                    if v_isSharedCheck_1273_ == 0 {
                        v_unused_1274_ = lean_ctor_get(v___x_1260_, 0);
                        lean_dec(v_unused_1274_);
                        v___x_1266_ = v___x_1260_;
                        v_isShared_1267_ = v_isSharedCheck_1273_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1264_);
                        lean_inc(v_postponed_1263_);
                        lean_inc(v_zetaDeltaFVarIds_1262_);
                        lean_inc(v_cache_1261_);
                        lean_dec(v___x_1260_);
                        v___x_1266_ = lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1273_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1267_ == 0 {
                    lean_ctor_set(v___x_1266_, 0, v_snd_1259_);
                    v___x_1269_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_snd_1259_);
                    lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_cache_1261_);
                    lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_zetaDeltaFVarIds_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_postponed_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_diag_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = lean_st_ref_set(v___y_1251_, v___x_1269_);
                v___x_1271_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1271_, 0, v_fst_1258_);
                return v___x_1271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(
    mut v_e_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1278_: *mut LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_1275_, v___y_1276_);
    lean_dec(v___y_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(
    mut v_e_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1289_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_1279_, v___y_1285_);
    return v___x_1289_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(
    mut v_e_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(
            v_e_1290_,
            v___y_1291_,
            v___y_1292_,
            v___y_1293_,
            v___y_1294_,
            v___y_1295_,
            v___y_1296_,
            v___y_1297_,
            v___y_1298_,
        );
    lean_dec(v___y_1298_);
    lean_dec_ref(v___y_1297_);
    lean_dec(v___y_1296_);
    lean_dec_ref(v___y_1295_);
    lean_dec(v___y_1294_);
    lean_dec_ref(v___y_1293_);
    lean_dec(v___y_1292_);
    lean_dec_ref(v___y_1291_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(
    mut v_x_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1305_);
    lean_inc_ref(v___y_1304_);
    lean_inc(v___y_1303_);
    lean_inc_ref(v___y_1302_);
    v___x_1311_ = lean_apply_9(
        v_x_1301_,
        v___y_1302_,
        v___y_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
        lean_box(0),
    );
    return v___x_1311_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(
    mut v_x_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
    lean_dec(v___y_1316_);
    lean_dec_ref(v___y_1315_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(
    mut v_mvarId_1323_: *mut LeanObject,
    mut v_x_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
    mut v___y_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1328_);
                lean_inc_ref(v___y_1327_);
                lean_inc(v___y_1326_);
                lean_inc_ref(v___y_1325_);
                v___f_1334_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_1334_, 0, v_x_1324_);
                lean_closure_set(v___f_1334_, 1, v___y_1325_);
                lean_closure_set(v___f_1334_, 2, v___y_1326_);
                lean_closure_set(v___f_1334_, 3, v___y_1327_);
                lean_closure_set(v___f_1334_, 4, v___y_1328_);
                v___x_1335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1323_,
                    v___f_1334_,
                    v___y_1329_,
                    v___y_1330_,
                    v___y_1331_,
                    v___y_1332_,
                );
                if lean_obj_tag(v___x_1335_) == 0 {
                    return v___x_1335_;
                } else {
                    v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
                    v_isSharedCheck_1343_ = (!lean_is_exclusive(v___x_1335_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1338_ = v___x_1335_;
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1336_);
                        lean_dec(v___x_1335_);
                        v___x_1338_ = lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(
    mut v_mvarId_1344_: *mut LeanObject,
    mut v_x_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
    mut v___y_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
    mut v___y_1351_: *mut LeanObject,
    mut v___y_1352_: *mut LeanObject,
    mut v___y_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_1344_, v_x_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
    lean_dec(v___y_1353_);
    lean_dec_ref(v___y_1352_);
    lean_dec(v___y_1351_);
    lean_dec_ref(v___y_1350_);
    lean_dec(v___y_1349_);
    lean_dec_ref(v___y_1348_);
    lean_dec(v___y_1347_);
    lean_dec_ref(v___y_1346_);
    return v_res_1355_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(
    mut v_00_u03b1_1356_: *mut LeanObject,
    mut v_mvarId_1357_: *mut LeanObject,
    mut v_x_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
    mut v___y_1362_: *mut LeanObject,
    mut v___y_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
    mut v___y_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    v___x_1368_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
    return v___x_1368_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(
    mut v_00_u03b1_1369_: *mut LeanObject,
    mut v_mvarId_1370_: *mut LeanObject,
    mut v_x_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
    mut v___y_1376_: *mut LeanObject,
    mut v___y_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_res_1381_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(
            v_00_u03b1_1369_,
            v_mvarId_1370_,
            v_x_1371_,
            v___y_1372_,
            v___y_1373_,
            v___y_1374_,
            v___y_1375_,
            v___y_1376_,
            v___y_1377_,
            v___y_1378_,
            v___y_1379_,
        );
    lean_dec(v___y_1379_);
    lean_dec_ref(v___y_1378_);
    lean_dec(v___y_1377_);
    lean_dec_ref(v___y_1376_);
    lean_dec(v___y_1375_);
    lean_dec_ref(v___y_1374_);
    lean_dec(v___y_1373_);
    lean_dec_ref(v___y_1372_);
    return v_res_1381_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(
    mut v_msgData_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_st_ref_get(v___y_1386_);
    v_env_1389_ = lean_ctor_get(v___x_1388_, 0);
    lean_inc_ref(v_env_1389_);
    lean_dec(v___x_1388_);
    v___x_1390_ = lean_st_ref_get(v___y_1384_);
    v_mctx_1391_ = lean_ctor_get(v___x_1390_, 0);
    lean_inc_ref(v_mctx_1391_);
    lean_dec(v___x_1390_);
    v_lctx_1392_ = lean_ctor_get(v___y_1383_, 2);
    v_options_1393_ = lean_ctor_get(v___y_1385_, 2);
    lean_inc_ref(v_options_1393_);
    lean_inc_ref(v_lctx_1392_);
    v___x_1394_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1394_, 0, v_env_1389_);
    lean_ctor_set(v___x_1394_, 1, v_mctx_1391_);
    lean_ctor_set(v___x_1394_, 2, v_lctx_1392_);
    lean_ctor_set(v___x_1394_, 3, v_options_1393_);
    v___x_1395_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1395_, 0, v___x_1394_);
    lean_ctor_set(v___x_1395_, 1, v_msgData_1382_);
    v___x_1396_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2___boxed(
    mut v_msgData_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1403_: *mut LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msgData_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
    lean_dec(v___y_1401_);
    lean_dec_ref(v___y_1400_);
    lean_dec(v___y_1399_);
    lean_dec_ref(v___y_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(
    mut v_msg_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1410_ = lean_ctor_get(v___y_1407_, 5);
                v___x_1411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
                v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
                v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1411_)) as u8;
                if v_isSharedCheck_1420_ == 0 {
                    v___x_1414_ = v___x_1411_;
                    v_isShared_1415_ = v_isSharedCheck_1420_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1412_);
                    lean_dec(v___x_1411_);
                    v___x_1414_ = lean_box(0);
                    v_isShared_1415_ = v_isSharedCheck_1420_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1410_);
                v___x_1416_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1416_, 0, v_ref_1410_);
                lean_ctor_set(v___x_1416_, 1, v_a_1412_);
                if v_isShared_1415_ == 0 {
                    lean_ctor_set_tag(v___x_1414_, 1);
                    lean_ctor_set(v___x_1414_, 0, v___x_1416_);
                    v___x_1418_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(
    mut v_msg_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1427_: *mut LeanObject = core::ptr::null_mut();
    v_res_1427_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(
            v_msg_1421_,
            v___y_1422_,
            v___y_1423_,
            v___y_1424_,
            v___y_1425_,
        );
    lean_dec(v___y_1425_);
    lean_dec_ref(v___y_1424_);
    lean_dec(v___y_1423_);
    lean_dec_ref(v___y_1422_);
    return v_res_1427_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(
    mut v_x_1428_: *mut LeanObject,
    mut v_x_1429_: *mut LeanObject,
    mut v_x_1430_: *mut LeanObject,
    mut v_x_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1436_: u8 = 0;
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1432_ = lean_ctor_get(v_x_1428_, 0);
                v_vs_1433_ = lean_ctor_get(v_x_1428_, 1);
                v_isSharedCheck_1457_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                if v_isSharedCheck_1457_ == 0 {
                    v___x_1435_ = v_x_1428_;
                    v_isShared_1436_ = v_isSharedCheck_1457_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1433_);
                    lean_inc(v_ks_1432_);
                    lean_dec(v_x_1428_);
                    v___x_1435_ = lean_box(0);
                    v_isShared_1436_ = v_isSharedCheck_1457_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1437_ = lean_array_get_size(v_ks_1432_);
                v___x_1438_ = lean_nat_dec_lt(v_x_1429_, v___x_1437_);
                if v___x_1438_ == 0 {
                    lean_dec(v_x_1429_);
                    v___x_1439_ = lean_array_push(v_ks_1432_, v_x_1430_);
                    v___x_1440_ = lean_array_push(v_vs_1433_, v_x_1431_);
                    if v_isShared_1436_ == 0 {
                        lean_ctor_set(v___x_1435_, 1, v___x_1440_);
                        lean_ctor_set(v___x_1435_, 0, v___x_1439_);
                        v___x_1442_ = v___x_1435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1439_);
                        lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1440_);
                        v___x_1442_ = v_reuseFailAlloc_1443_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1444_ = lean_array_fget_borrowed(v_ks_1432_, v_x_1429_);
                    v___x_1445_ = l_Lean_instBEqMVarId_beq(v_x_1430_, v_k_x27_1444_);
                    if v___x_1445_ == 0 {
                        if v_isShared_1436_ == 0 {
                            v___x_1447_ = v___x_1435_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_ks_1432_);
                            lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_vs_1433_);
                            v___x_1447_ = v_reuseFailAlloc_1451_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1452_ = lean_array_fset(v_ks_1432_, v_x_1429_, v_x_1430_);
                        v___x_1453_ = lean_array_fset(v_vs_1433_, v_x_1429_, v_x_1431_);
                        lean_dec(v_x_1429_);
                        if v_isShared_1436_ == 0 {
                            lean_ctor_set(v___x_1435_, 1, v___x_1453_);
                            lean_ctor_set(v___x_1435_, 0, v___x_1452_);
                            v___x_1455_ = v___x_1435_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1452_);
                            lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1453_);
                            v___x_1455_ = v_reuseFailAlloc_1456_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1442_;
            }
            3 => {
                v___x_1448_ = lean_unsigned_to_nat(1);
                v___x_1449_ = lean_nat_add(v_x_1429_, v___x_1448_);
                lean_dec(v_x_1429_);
                v_x_1428_ = v___x_1447_;
                v_x_1429_ = v___x_1449_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(
    mut v_n_1458_: *mut LeanObject,
    mut v_k_1459_: *mut LeanObject,
    mut v_v_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1461_ = lean_unsigned_to_nat(0);
    v___x_1462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_n_1458_, v___x_1461_, v_k_1459_, v_v_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1463_: usize = 0;
    let mut v___x_1464_: usize = 0;
    let mut v___x_1465_: usize = 0;
    v___x_1463_ = 5usize;
    v___x_1464_ = 1usize;
    v___x_1465_ = lean_usize_shift_left(v___x_1464_, v___x_1463_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1466_: usize = 0;
    let mut v___x_1467_: usize = 0;
    let mut v___x_1468_: usize = 0;
    v___x_1466_ = 1usize;
    v___x_1467_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0);
    v___x_1468_ = lean_usize_sub(v___x_1467_, v___x_1466_);
    return v___x_1468_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    v___x_1469_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1469_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(
    mut v_x_1470_: *mut LeanObject,
    mut v_x_1471_: usize,
    mut v_x_1472_: usize,
    mut v_x_1473_: *mut LeanObject,
    mut v_x_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: usize = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: usize = 0;
    let mut v_j_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v_v_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v_node_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1519_: u8 = 0;
    let mut v_unused_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: u8 = 0;
    let mut v_ks_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v_reuseFailAlloc_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1470_) == 0 {
                    v_es_1475_ = lean_ctor_get(v_x_1470_, 0);
                    v___x_1476_ = 5usize;
                    v___x_1477_ = 1usize;
                    v___x_1478_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_1479_ = lean_usize_land(v_x_1471_, v___x_1478_);
                    v_j_1480_ = lean_usize_to_nat(v___x_1479_);
                    v___x_1481_ = lean_array_get_size(v_es_1475_);
                    v___x_1482_ = lean_nat_dec_lt(v_j_1480_, v___x_1481_);
                    if v___x_1482_ == 0 {
                        lean_dec(v_j_1480_);
                        lean_dec(v_x_1474_);
                        lean_dec(v_x_1473_);
                        return v_x_1470_;
                    } else {
                        lean_inc_ref(v_es_1475_);
                        v_isSharedCheck_1519_ = (!lean_is_exclusive(v_x_1470_)) as u8;
                        if v_isSharedCheck_1519_ == 0 {
                            v_unused_1520_ = lean_ctor_get(v_x_1470_, 0);
                            lean_dec(v_unused_1520_);
                            v___x_1484_ = v_x_1470_;
                            v_isShared_1485_ = v_isSharedCheck_1519_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1470_);
                            v___x_1484_ = lean_box(0);
                            v_isShared_1485_ = v_isSharedCheck_1519_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1521_ = lean_ctor_get(v_x_1470_, 0);
                    v_vs_1522_ = lean_ctor_get(v_x_1470_, 1);
                    v_isSharedCheck_1542_ = (!lean_is_exclusive(v_x_1470_)) as u8;
                    if v_isSharedCheck_1542_ == 0 {
                        v___x_1524_ = v_x_1470_;
                        v_isShared_1525_ = v_isSharedCheck_1542_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1522_);
                        lean_inc(v_ks_1521_);
                        lean_dec(v_x_1470_);
                        v___x_1524_ = lean_box(0);
                        v_isShared_1525_ = v_isSharedCheck_1542_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1486_ = lean_array_fget(v_es_1475_, v_j_1480_);
                v___x_1487_ = lean_box(0);
                v_xs_x27_1488_ = lean_array_fset(v_es_1475_, v_j_1480_, v___x_1487_);
                match lean_obj_tag(v_v_1486_) {
                    0 => {
                        v_key_1495_ = lean_ctor_get(v_v_1486_, 0);
                        v_val_1496_ = lean_ctor_get(v_v_1486_, 1);
                        v_isSharedCheck_1506_ = (!lean_is_exclusive(v_v_1486_)) as u8;
                        if v_isSharedCheck_1506_ == 0 {
                            v___x_1498_ = v_v_1486_;
                            v_isShared_1499_ = v_isSharedCheck_1506_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1496_);
                            lean_inc(v_key_1495_);
                            lean_dec(v_v_1486_);
                            v___x_1498_ = lean_box(0);
                            v_isShared_1499_ = v_isSharedCheck_1506_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1507_ = lean_ctor_get(v_v_1486_, 0);
                        v_isSharedCheck_1517_ = (!lean_is_exclusive(v_v_1486_)) as u8;
                        if v_isSharedCheck_1517_ == 0 {
                            v___x_1509_ = v_v_1486_;
                            v_isShared_1510_ = v_isSharedCheck_1517_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1507_);
                            lean_dec(v_v_1486_);
                            v___x_1509_ = lean_box(0);
                            v_isShared_1510_ = v_isSharedCheck_1517_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1518_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1518_, 0, v_x_1473_);
                        lean_ctor_set(v___x_1518_, 1, v_x_1474_);
                        v___y_1490_ = v___x_1518_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1491_ = lean_array_fset(v_xs_x27_1488_, v_j_1480_, v___y_1490_);
                lean_dec(v_j_1480_);
                if v_isShared_1485_ == 0 {
                    lean_ctor_set(v___x_1484_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1484_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1493_;
            }
            4 => {
                v___x_1500_ = l_Lean_instBEqMVarId_beq(v_x_1473_, v_key_1495_);
                if v___x_1500_ == 0 {
                    lean_del_object(v___x_1498_);
                    v___x_1501_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1495_,
                        v_val_1496_,
                        v_x_1473_,
                        v_x_1474_,
                    );
                    v___x_1502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1502_, 0, v___x_1501_);
                    v___y_1490_ = v___x_1502_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1496_);
                    lean_dec(v_key_1495_);
                    if v_isShared_1499_ == 0 {
                        lean_ctor_set(v___x_1498_, 1, v_x_1474_);
                        lean_ctor_set(v___x_1498_, 0, v_x_1473_);
                        v___x_1504_ = v___x_1498_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_x_1473_);
                        lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_x_1474_);
                        v___x_1504_ = v_reuseFailAlloc_1505_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1490_ = v___x_1504_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1511_ = lean_usize_shift_right(v_x_1471_, v___x_1476_);
                v___x_1512_ = lean_usize_add(v_x_1472_, v___x_1477_);
                v___x_1513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_node_1507_, v___x_1511_, v___x_1512_, v_x_1473_, v_x_1474_);
                if v_isShared_1510_ == 0 {
                    lean_ctor_set(v___x_1509_, 0, v___x_1513_);
                    v___x_1515_ = v___x_1509_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1490_ = v___x_1515_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1525_ == 0 {
                    v___x_1527_ = v___x_1524_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_ks_1521_);
                    lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_vs_1522_);
                    v___x_1527_ = v_reuseFailAlloc_1541_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1528_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v___x_1527_, v_x_1473_, v_x_1474_);
                v___x_1536_ = 7usize;
                v___x_1537_ = lean_usize_dec_le(v___x_1536_, v_x_1472_);
                if v___x_1537_ == 0 {
                    v___x_1538_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1528_);
                    v___x_1539_ = lean_unsigned_to_nat(4);
                    v___x_1540_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
                    lean_dec(v___x_1538_);
                    v___y_1530_ = v___x_1540_;
                    state = 10;
                    continue;
                } else {
                    v___y_1530_ = v___x_1537_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1530_ == 0 {
                    v_ks_1531_ = lean_ctor_get(v_newNode_1528_, 0);
                    lean_inc_ref(v_ks_1531_);
                    v_vs_1532_ = lean_ctor_get(v_newNode_1528_, 1);
                    lean_inc_ref(v_vs_1532_);
                    lean_dec_ref(v_newNode_1528_);
                    v___x_1533_ = lean_unsigned_to_nat(0);
                    v___x_1534_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2);
                    v___x_1535_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_x_1472_, v_ks_1531_, v_vs_1532_, v___x_1533_, v___x_1534_);
                    lean_dec_ref(v_vs_1532_);
                    lean_dec_ref(v_ks_1531_);
                    return v___x_1535_;
                } else {
                    return v_newNode_1528_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(
    mut v_depth_1543_: usize,
    mut v_keys_1544_: *mut LeanObject,
    mut v_vals_1545_: *mut LeanObject,
    mut v_i_1546_: *mut LeanObject,
    mut v_entries_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v_k_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u64 = 0;
    let mut v_h_1553_: usize = 0;
    let mut v___x_1554_: usize = 0;
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: usize = 0;
    let mut v___x_1558_: usize = 0;
    let mut v_h_1559_: usize = 0;
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1548_ = lean_array_get_size(v_keys_1544_);
                v___x_1549_ = lean_nat_dec_lt(v_i_1546_, v___x_1548_);
                if v___x_1549_ == 0 {
                    lean_dec(v_i_1546_);
                    return v_entries_1547_;
                } else {
                    v_k_1550_ = lean_array_fget_borrowed(v_keys_1544_, v_i_1546_);
                    v_v_1551_ = lean_array_fget_borrowed(v_vals_1545_, v_i_1546_);
                    v___x_1552_ = l_Lean_instHashableMVarId_hash(v_k_1550_);
                    v_h_1553_ = lean_uint64_to_usize(v___x_1552_);
                    v___x_1554_ = 5usize;
                    v___x_1555_ = lean_unsigned_to_nat(1);
                    v___x_1556_ = 1usize;
                    v___x_1557_ = lean_usize_sub(v_depth_1543_, v___x_1556_);
                    v___x_1558_ = lean_usize_mul(v___x_1554_, v___x_1557_);
                    v_h_1559_ = lean_usize_shift_right(v_h_1553_, v___x_1558_);
                    v___x_1560_ = lean_nat_add(v_i_1546_, v___x_1555_);
                    lean_dec(v_i_1546_);
                    lean_inc(v_v_1551_);
                    lean_inc(v_k_1550_);
                    v___x_1561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_entries_1547_, v_h_1559_, v_depth_1543_, v_k_1550_, v_v_1551_);
                    v_i_1546_ = v___x_1560_;
                    v_entries_1547_ = v___x_1561_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg___boxed(
    mut v_depth_1563_: *mut LeanObject,
    mut v_keys_1564_: *mut LeanObject,
    mut v_vals_1565_: *mut LeanObject,
    mut v_i_1566_: *mut LeanObject,
    mut v_entries_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1568_: usize = 0;
    let mut v_res_1569_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1568_ = lean_unbox_usize(v_depth_1563_);
    lean_dec(v_depth_1563_);
    v_res_1569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_boxed_1568_, v_keys_1564_, v_vals_1565_, v_i_1566_, v_entries_1567_);
    lean_dec_ref(v_vals_1565_);
    lean_dec_ref(v_keys_1564_);
    return v_res_1569_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_x_1570_: *mut LeanObject,
    mut v_x_1571_: *mut LeanObject,
    mut v_x_1572_: *mut LeanObject,
    mut v_x_1573_: *mut LeanObject,
    mut v_x_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6319__boxed_1575_: usize = 0;
    let mut v_x_6320__boxed_1576_: usize = 0;
    let mut v_res_1577_: *mut LeanObject = core::ptr::null_mut();
    v_x_6319__boxed_1575_ = lean_unbox_usize(v_x_1571_);
    lean_dec(v_x_1571_);
    v_x_6320__boxed_1576_ = lean_unbox_usize(v_x_1572_);
    lean_dec(v_x_1572_);
    v_res_1577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_1570_, v_x_6319__boxed_1575_, v_x_6320__boxed_1576_, v_x_1573_, v_x_1574_);
    return v_res_1577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(
    mut v_x_1578_: *mut LeanObject,
    mut v_x_1579_: *mut LeanObject,
    mut v_x_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1581_: u64 = 0;
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1581_ = l_Lean_instHashableMVarId_hash(v_x_1579_);
    v___x_1582_ = lean_uint64_to_usize(v___x_1581_);
    v___x_1583_ = 1usize;
    v___x_1584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_1578_, v___x_1582_, v___x_1583_, v_x_1579_, v_x_1580_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(
    mut v_mvarId_1585_: *mut LeanObject,
    mut v_val_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v_depth_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1589_ = lean_st_ref_take(v___y_1587_);
                v_mctx_1590_ = lean_ctor_get(v___x_1589_, 0);
                v_cache_1591_ = lean_ctor_get(v___x_1589_, 1);
                v_zetaDeltaFVarIds_1592_ = lean_ctor_get(v___x_1589_, 2);
                v_postponed_1593_ = lean_ctor_get(v___x_1589_, 3);
                v_diag_1594_ = lean_ctor_get(v___x_1589_, 4);
                v_isSharedCheck_1622_ = (!lean_is_exclusive(v___x_1589_)) as u8;
                if v_isSharedCheck_1622_ == 0 {
                    v___x_1596_ = v___x_1589_;
                    v_isShared_1597_ = v_isSharedCheck_1622_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1594_);
                    lean_inc(v_postponed_1593_);
                    lean_inc(v_zetaDeltaFVarIds_1592_);
                    lean_inc(v_cache_1591_);
                    lean_inc(v_mctx_1590_);
                    lean_dec(v___x_1589_);
                    v___x_1596_ = lean_box(0);
                    v_isShared_1597_ = v_isSharedCheck_1622_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1598_ = lean_ctor_get(v_mctx_1590_, 0);
                v_levelAssignDepth_1599_ = lean_ctor_get(v_mctx_1590_, 1);
                v_lmvarCounter_1600_ = lean_ctor_get(v_mctx_1590_, 2);
                v_mvarCounter_1601_ = lean_ctor_get(v_mctx_1590_, 3);
                v_lDecls_1602_ = lean_ctor_get(v_mctx_1590_, 4);
                v_decls_1603_ = lean_ctor_get(v_mctx_1590_, 5);
                v_userNames_1604_ = lean_ctor_get(v_mctx_1590_, 6);
                v_lAssignment_1605_ = lean_ctor_get(v_mctx_1590_, 7);
                v_eAssignment_1606_ = lean_ctor_get(v_mctx_1590_, 8);
                v_dAssignment_1607_ = lean_ctor_get(v_mctx_1590_, 9);
                v_isSharedCheck_1621_ = (!lean_is_exclusive(v_mctx_1590_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v___x_1609_ = v_mctx_1590_;
                    v_isShared_1610_ = v_isSharedCheck_1621_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1607_);
                    lean_inc(v_eAssignment_1606_);
                    lean_inc(v_lAssignment_1605_);
                    lean_inc(v_userNames_1604_);
                    lean_inc(v_decls_1603_);
                    lean_inc(v_lDecls_1602_);
                    lean_inc(v_mvarCounter_1601_);
                    lean_inc(v_lmvarCounter_1600_);
                    lean_inc(v_levelAssignDepth_1599_);
                    lean_inc(v_depth_1598_);
                    lean_dec(v_mctx_1590_);
                    v___x_1609_ = lean_box(0);
                    v_isShared_1610_ = v_isSharedCheck_1621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1611_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_eAssignment_1606_, v_mvarId_1585_, v_val_1586_);
                if v_isShared_1610_ == 0 {
                    lean_ctor_set(v___x_1609_, 8, v___x_1611_);
                    v___x_1613_ = v___x_1609_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_depth_1598_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_levelAssignDepth_1599_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_lmvarCounter_1600_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_mvarCounter_1601_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_lDecls_1602_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 5, v_decls_1603_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 6, v_userNames_1604_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 7, v_lAssignment_1605_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 8, v___x_1611_);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 9, v_dAssignment_1607_);
                    v___x_1613_ = v_reuseFailAlloc_1620_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1597_ == 0 {
                    lean_ctor_set(v___x_1596_, 0, v___x_1613_);
                    v___x_1615_ = v___x_1596_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_cache_1591_);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_zetaDeltaFVarIds_1592_);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_postponed_1593_);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_diag_1594_);
                    v___x_1615_ = v_reuseFailAlloc_1619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1616_ = lean_st_ref_set(v___y_1587_, v___x_1615_);
                v___x_1617_ = lean_box(0);
                v___x_1618_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1618_, 0, v___x_1617_);
                return v___x_1618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg___boxed(
    mut v_mvarId_1623_: *mut LeanObject,
    mut v_val_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1627_: *mut LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_1623_, v_val_1624_, v___y_1625_);
    lean_dec(v___y_1625_);
    return v_res_1627_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0;
    v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
    return v___x_1630_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2;
    v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
    return v___x_1633_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(
    mut v_a_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1675_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1634_);
                v___x_1661_ = l_Lean_MVarId_getType(
                    v_a_1634_,
                    v___y_1639_,
                    v___y_1640_,
                    v___y_1641_,
                    v___y_1642_,
                );
                if lean_obj_tag(v___x_1661_) == 0 {
                    v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
                    lean_inc(v_a_1662_);
                    lean_dec_ref_known(v___x_1661_, 1);
                    v___x_1663_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_a_1662_, v___y_1640_);
                    v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
                    lean_inc(v_a_1664_);
                    lean_dec_ref(v___x_1663_);
                    v___x_1665_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1664_);
                    lean_dec(v_a_1664_);
                    if lean_obj_tag(v___x_1665_) == 1 {
                        v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
                        lean_inc_n(v_val_1666_, 2);
                        lean_dec_ref_known(v___x_1665_, 1);
                        v___x_1667_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                            v_val_1666_,
                            v___y_1639_,
                            v___y_1640_,
                            v___y_1641_,
                            v___y_1642_,
                        );
                        if lean_obj_tag(v___x_1667_) == 0 {
                            v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
                            lean_inc(v_a_1668_);
                            if lean_obj_tag(v_a_1668_) == 0 {
                                lean_dec_ref_known(v___x_1667_, 1);
                                v___x_1669_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(
                                    v_val_1666_,
                                    v___y_1639_,
                                    v___y_1640_,
                                    v___y_1641_,
                                    v___y_1642_,
                                );
                                v___y_1645_ = v___x_1669_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v_a_1668_, 1);
                                lean_dec(v_val_1666_);
                                v___y_1645_ = v___x_1667_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_1666_);
                            v___y_1645_ = v___x_1667_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1665_);
                        lean_dec(v_a_1634_);
                        v___x_1670_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3);
                        v___x_1671_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_1670_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
                        return v___x_1671_;
                    }
                } else {
                    lean_dec(v_a_1634_);
                    v_a_1672_ = lean_ctor_get(v___x_1661_, 0);
                    v_isSharedCheck_1679_ = (!lean_is_exclusive(v___x_1661_)) as u8;
                    if v_isSharedCheck_1679_ == 0 {
                        v___x_1674_ = v___x_1661_;
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1672_);
                        lean_dec(v___x_1661_);
                        v___x_1674_ = lean_box(0);
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_1645_) == 0 {
                    v_a_1646_ = lean_ctor_get(v___y_1645_, 0);
                    lean_inc(v_a_1646_);
                    lean_dec_ref_known(v___y_1645_, 1);
                    if lean_obj_tag(v_a_1646_) == 1 {
                        v_val_1647_ = lean_ctor_get(v_a_1646_, 0);
                        lean_inc(v_val_1647_);
                        lean_dec_ref_known(v_a_1646_, 1);
                        v___x_1648_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_a_1634_, v_val_1647_, v___y_1640_);
                        lean_dec_ref(v___x_1648_);
                        v___x_1649_ = lean_box(0);
                        v___x_1650_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1649_,
                            v___y_1636_,
                            v___y_1639_,
                            v___y_1640_,
                            v___y_1641_,
                            v___y_1642_,
                        );
                        return v___x_1650_;
                    } else {
                        lean_dec(v_a_1646_);
                        lean_dec(v_a_1634_);
                        v___x_1651_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1);
                        v___x_1652_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_1651_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
                        return v___x_1652_;
                    }
                } else {
                    lean_dec(v_a_1634_);
                    v_a_1653_ = lean_ctor_get(v___y_1645_, 0);
                    v_isSharedCheck_1660_ = (!lean_is_exclusive(v___y_1645_)) as u8;
                    if v_isSharedCheck_1660_ == 0 {
                        v___x_1655_ = v___y_1645_;
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1653_);
                        lean_dec(v___y_1645_);
                        v___x_1655_ = lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1656_ == 0 {
                    v___x_1658_ = v___x_1655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
                    v___x_1658_ = v_reuseFailAlloc_1659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1658_;
            }
            4 => {
                if v_isShared_1675_ == 0 {
                    v___x_1677_ = v___x_1674_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
                    v___x_1677_ = v_reuseFailAlloc_1678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed(
    mut v_a_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1690_: *mut LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(
        v_a_1680_,
        v___y_1681_,
        v___y_1682_,
        v___y_1683_,
        v___y_1684_,
        v___y_1685_,
        v___y_1686_,
        v___y_1687_,
        v___y_1688_,
    );
    lean_dec(v___y_1688_);
    lean_dec_ref(v___y_1687_);
    lean_dec(v___y_1686_);
    lean_dec_ref(v___y_1685_);
    lean_dec(v___y_1684_);
    lean_dec_ref(v___y_1683_);
    lean_dec(v___y_1682_);
    lean_dec_ref(v___y_1681_);
    return v_res_1690_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(
    mut v_a_1691_: *mut LeanObject,
    mut v_a_1692_: *mut LeanObject,
    mut v_a_1693_: *mut LeanObject,
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_a_1696_: *mut LeanObject,
    mut v_a_1697_: *mut LeanObject,
    mut v_a_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1707_: u8 = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1700_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1692_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_,
                );
                if lean_obj_tag(v___x_1700_) == 0 {
                    v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
                    lean_inc_n(v_a_1701_, 2);
                    lean_dec_ref_known(v___x_1700_, 1);
                    v___f_1702_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_1702_, 0, v_a_1701_);
                    v___x_1703_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_a_1701_, v___f_1702_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
                    return v___x_1703_;
                } else {
                    v_a_1704_ = lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1711_ = (!lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1706_ = v___x_1700_;
                        v_isShared_1707_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1704_);
                        lean_dec(v___x_1700_);
                        v___x_1706_ = lean_box(0);
                        v_isShared_1707_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1707_ == 0 {
                    v___x_1709_ = v___x_1706_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
                    v___x_1709_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___boxed(
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
    mut v_a_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(
        v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_,
    );
    lean_dec(v_a_1719_);
    lean_dec_ref(v_a_1718_);
    lean_dec(v_a_1717_);
    lean_dec_ref(v_a_1716_);
    lean_dec(v_a_1715_);
    lean_dec_ref(v_a_1714_);
    lean_dec(v_a_1713_);
    lean_dec_ref(v_a_1712_);
    return v_res_1721_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(
    mut v_x_1722_: *mut LeanObject,
    mut v_a_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
    mut v_a_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
    mut v_a_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(
        v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_,
    );
    return v___x_1732_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed(
    mut v_x_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
    mut v_a_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
    mut v_a_1737_: *mut LeanObject,
    mut v_a_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1743_: *mut LeanObject = core::ptr::null_mut();
    v_res_1743_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(
        v_x_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_,
        v_a_1741_,
    );
    lean_dec(v_a_1741_);
    lean_dec_ref(v_a_1740_);
    lean_dec(v_a_1739_);
    lean_dec_ref(v_a_1738_);
    lean_dec(v_a_1737_);
    lean_dec_ref(v_a_1736_);
    lean_dec(v_a_1735_);
    lean_dec_ref(v_a_1734_);
    lean_dec(v_x_1733_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(
    mut v_mvarId_1744_: *mut LeanObject,
    mut v_val_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_1744_, v_val_1745_, v___y_1751_);
    return v___x_1755_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___boxed(
    mut v_mvarId_1756_: *mut LeanObject,
    mut v_val_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1767_: *mut LeanObject = core::ptr::null_mut();
    v_res_1767_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(
            v_mvarId_1756_,
            v_val_1757_,
            v___y_1758_,
            v___y_1759_,
            v___y_1760_,
            v___y_1761_,
            v___y_1762_,
            v___y_1763_,
            v___y_1764_,
            v___y_1765_,
        );
    lean_dec(v___y_1765_);
    lean_dec_ref(v___y_1764_);
    lean_dec(v___y_1763_);
    lean_dec_ref(v___y_1762_);
    lean_dec(v___y_1761_);
    lean_dec_ref(v___y_1760_);
    lean_dec(v___y_1759_);
    lean_dec_ref(v___y_1758_);
    return v_res_1767_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(
    mut v_00_u03b1_1768_: *mut LeanObject,
    mut v_msg_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
    mut v___y_1776_: *mut LeanObject,
    mut v___y_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v___x_1779_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(
            v_msg_1769_,
            v___y_1774_,
            v___y_1775_,
            v___y_1776_,
            v___y_1777_,
        );
    return v___x_1779_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(
    mut v_00_u03b1_1780_: *mut LeanObject,
    mut v_msg_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1791_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(
        v_00_u03b1_1780_,
        v_msg_1781_,
        v___y_1782_,
        v___y_1783_,
        v___y_1784_,
        v___y_1785_,
        v___y_1786_,
        v___y_1787_,
        v___y_1788_,
        v___y_1789_,
    );
    lean_dec(v___y_1789_);
    lean_dec_ref(v___y_1788_);
    lean_dec(v___y_1787_);
    lean_dec_ref(v___y_1786_);
    lean_dec(v___y_1785_);
    lean_dec_ref(v___y_1784_);
    lean_dec(v___y_1783_);
    lean_dec_ref(v___y_1782_);
    return v_res_1791_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0(
    mut v_00_u03b2_1792_: *mut LeanObject,
    mut v_x_1793_: *mut LeanObject,
    mut v_x_1794_: *mut LeanObject,
    mut v_x_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_x_1793_, v_x_1794_, v_x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1797_: *mut LeanObject,
    mut v_x_1798_: *mut LeanObject,
    mut v_x_1799_: usize,
    mut v_x_1800_: usize,
    mut v_x_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_1798_, v_x_1799_, v_x_1800_, v_x_1801_, v_x_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1804_: *mut LeanObject,
    mut v_x_1805_: *mut LeanObject,
    mut v_x_1806_: *mut LeanObject,
    mut v_x_1807_: *mut LeanObject,
    mut v_x_1808_: *mut LeanObject,
    mut v_x_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6765__boxed_1810_: usize = 0;
    let mut v_x_6766__boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_x_6765__boxed_1810_ = lean_unbox_usize(v_x_1806_);
    lean_dec(v_x_1806_);
    v_x_6766__boxed_1811_ = lean_unbox_usize(v_x_1807_);
    lean_dec(v_x_1807_);
    v_res_1812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(v_00_u03b2_1804_, v_x_1805_, v_x_6765__boxed_1810_, v_x_6766__boxed_1811_, v_x_1808_, v_x_1809_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6(
    mut v_00_u03b2_1813_: *mut LeanObject,
    mut v_n_1814_: *mut LeanObject,
    mut v_k_1815_: *mut LeanObject,
    mut v_v_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v_n_1814_, v_k_1815_, v_v_1816_);
    return v___x_1817_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(
    mut v_00_u03b2_1818_: *mut LeanObject,
    mut v_depth_1819_: usize,
    mut v_keys_1820_: *mut LeanObject,
    mut v_vals_1821_: *mut LeanObject,
    mut v_heq_1822_: *mut LeanObject,
    mut v_i_1823_: *mut LeanObject,
    mut v_entries_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_1819_, v_keys_1820_, v_vals_1821_, v_i_1823_, v_entries_1824_);
    return v___x_1825_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_00_u03b2_1826_: *mut LeanObject,
    mut v_depth_1827_: *mut LeanObject,
    mut v_keys_1828_: *mut LeanObject,
    mut v_vals_1829_: *mut LeanObject,
    mut v_heq_1830_: *mut LeanObject,
    mut v_i_1831_: *mut LeanObject,
    mut v_entries_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1833_: usize = 0;
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1833_ = lean_unbox_usize(v_depth_1827_);
    lean_dec(v_depth_1827_);
    v_res_1834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(v_00_u03b2_1826_, v_depth_boxed_1833_, v_keys_1828_, v_vals_1829_, v_heq_1830_, v_i_1831_, v_entries_1832_);
    lean_dec_ref(v_vals_1829_);
    lean_dec_ref(v_keys_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7(
    mut v_00_u03b2_1835_: *mut LeanObject,
    mut v_x_1836_: *mut LeanObject,
    mut v_x_1837_: *mut LeanObject,
    mut v_x_1838_: *mut LeanObject,
    mut v_x_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_x_1836_, v_x_1837_, v_x_1838_, v_x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1()
-> *mut LeanObject {
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1860_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1861_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3;
    v___x_1862_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7;
    v___x_1863_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1860_,
        v___x_1861_,
        v___x_1862_,
        v___x_1863_,
    );
    return v___x_1864_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(
    mut v_a_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
    return v_res_1866_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
}
