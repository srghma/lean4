// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{l_StateT_bind, l_StateT_get};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_num___override};
use crate::r#gen::Init::Util::l_ptrEqList___redArg;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_hasMVar, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_hasMVar, l_Lean_Level_succ___override, l_Lean_instBEqLevelMVarId_beq,
    l_Lean_instHashableLevelMVarId_hash, l_Lean_mkLevelIMax_x27, l_Lean_mkLevelMax_x27,
    l_Lean_mkLevelParam, l_Lean_simpLevelIMax_x27, l_Lean_simpLevelMax_x27,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkLambda, l_Lean_LocalContext_mkLocalDecl,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_AbstractMVarsResult_numMVars,
    l_Lean_Meta_lambdaMetaTelescope, l_Lean_Meta_mkFreshLevelMVar,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_MetavarContext_getLevelDepth, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParamsArray;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_get as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value: LeanClosureObject<7> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_bind as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 7,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 97, 98, 115, 116, 77, 86, 97, 114, 0]};
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut LeanObject,6357867680762384532 as *mut LeanObject] };
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [120, 0],
    };
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
                as *mut LeanObject,
            13655884332201764339 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_abstractMVars___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_abstractMVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_abstractMVars___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_abstractMVars___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_abstractMVars___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_abstractMVars___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_abstractMVars___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(
    mut v_____do__lift_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mctx_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v_mctx_1165_ = lean_ctor_get(v_____do__lift_1163_, 2);
    lean_inc_ref(v_mctx_1165_);
    v___x_1166_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1166_, 0, v_mctx_1165_);
    lean_ctor_set(v___x_1166_, 1, v___y_1164_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(
    mut v_____do__lift_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1169_: *mut LeanObject = core::ptr::null_mut();
    v_res_1169_ =
        l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(v_____do__lift_1167_, v___y_1168_);
    lean_dec_ref(v_____do__lift_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(
    mut v_f_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ngen_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmap_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1181_: u8 = 0;
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1172_ = lean_ctor_get(v___y_1171_, 0);
                v_lctx_1173_ = lean_ctor_get(v___y_1171_, 1);
                v_mctx_1174_ = lean_ctor_get(v___y_1171_, 2);
                v_nextParamIdx_1175_ = lean_ctor_get(v___y_1171_, 3);
                v_paramNames_1176_ = lean_ctor_get(v___y_1171_, 4);
                v_fvars_1177_ = lean_ctor_get(v___y_1171_, 5);
                v_mvars_1178_ = lean_ctor_get(v___y_1171_, 6);
                v_lmap_1179_ = lean_ctor_get(v___y_1171_, 7);
                v_emap_1180_ = lean_ctor_get(v___y_1171_, 8);
                v_abstractLevels_1181_ = lean_ctor_get_uint8(
                    v___y_1171_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1191_ = (!lean_is_exclusive(v___y_1171_)) as u8;
                if v_isSharedCheck_1191_ == 0 {
                    v___x_1183_ = v___y_1171_;
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_emap_1180_);
                    lean_inc(v_lmap_1179_);
                    lean_inc(v_mvars_1178_);
                    lean_inc(v_fvars_1177_);
                    lean_inc(v_paramNames_1176_);
                    lean_inc(v_nextParamIdx_1175_);
                    lean_inc(v_mctx_1174_);
                    lean_inc(v_lctx_1173_);
                    lean_inc(v_ngen_1172_);
                    lean_dec(v___y_1171_);
                    v___x_1183_ = lean_box(0);
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1185_ = lean_box(0);
                v___x_1186_ = lean_apply_1(v_f_1170_, v_mctx_1174_);
                if v_isShared_1184_ == 0 {
                    lean_ctor_set(v___x_1183_, 2, v___x_1186_);
                    v___x_1188_ = v___x_1183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_ngen_1172_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_lctx_1173_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 2, v___x_1186_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_nextParamIdx_1175_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_paramNames_1176_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_fvars_1177_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_mvars_1178_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_lmap_1179_);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_emap_1180_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1190_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_abstractLevels_1181_,
                    );
                    v___x_1188_ = v_reuseFailAlloc_1190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1189_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1189_, 0, v___x_1185_);
                lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                return v___x_1189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshId(
    mut v_a_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ngen_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmap_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1233_: u8 = 0;
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v_namePrefix_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1224_ = lean_ctor_get(v_a_1223_, 0);
                v_lctx_1225_ = lean_ctor_get(v_a_1223_, 1);
                v_mctx_1226_ = lean_ctor_get(v_a_1223_, 2);
                v_nextParamIdx_1227_ = lean_ctor_get(v_a_1223_, 3);
                v_paramNames_1228_ = lean_ctor_get(v_a_1223_, 4);
                v_fvars_1229_ = lean_ctor_get(v_a_1223_, 5);
                v_mvars_1230_ = lean_ctor_get(v_a_1223_, 6);
                v_lmap_1231_ = lean_ctor_get(v_a_1223_, 7);
                v_emap_1232_ = lean_ctor_get(v_a_1223_, 8);
                v_abstractLevels_1233_ = lean_ctor_get_uint8(
                    v_a_1223_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1253_ = (!lean_is_exclusive(v_a_1223_)) as u8;
                if v_isSharedCheck_1253_ == 0 {
                    v___x_1235_ = v_a_1223_;
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_emap_1232_);
                    lean_inc(v_lmap_1231_);
                    lean_inc(v_mvars_1230_);
                    lean_inc(v_fvars_1229_);
                    lean_inc(v_paramNames_1228_);
                    lean_inc(v_nextParamIdx_1227_);
                    lean_inc(v_mctx_1226_);
                    lean_inc(v_lctx_1225_);
                    lean_inc(v_ngen_1224_);
                    lean_dec(v_a_1223_);
                    v___x_1235_ = lean_box(0);
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_namePrefix_1237_ = lean_ctor_get(v_ngen_1224_, 0);
                v_idx_1238_ = lean_ctor_get(v_ngen_1224_, 1);
                v_isSharedCheck_1252_ = (!lean_is_exclusive(v_ngen_1224_)) as u8;
                if v_isSharedCheck_1252_ == 0 {
                    v___x_1240_ = v_ngen_1224_;
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_idx_1238_);
                    lean_inc(v_namePrefix_1237_);
                    lean_dec(v_ngen_1224_);
                    v___x_1240_ = lean_box(0);
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_1238_);
                lean_inc(v_namePrefix_1237_);
                v___x_1242_ = l_Lean_Name_num___override(v_namePrefix_1237_, v_idx_1238_);
                v___x_1243_ = lean_unsigned_to_nat(1);
                v___x_1244_ = lean_nat_add(v_idx_1238_, v___x_1243_);
                lean_dec(v_idx_1238_);
                if v_isShared_1241_ == 0 {
                    lean_ctor_set(v___x_1240_, 1, v___x_1244_);
                    v___x_1246_ = v___x_1240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_namePrefix_1237_);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1244_);
                    v___x_1246_ = v_reuseFailAlloc_1251_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1236_ == 0 {
                    lean_ctor_set(v___x_1235_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_lctx_1225_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_mctx_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_nextParamIdx_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_paramNames_1228_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_fvars_1229_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_mvars_1230_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_lmap_1231_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_emap_1232_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1250_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_abstractLevels_1233_,
                    );
                    v___x_1248_ = v_reuseFailAlloc_1250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1249_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1249_, 0, v___x_1242_);
                lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshFVarId(
    mut v_a_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1255_ = l_Lean_Meta_AbstractMVars_mkFreshId(v_a_1254_);
                v_fst_1256_ = lean_ctor_get(v___x_1255_, 0);
                v_snd_1257_ = lean_ctor_get(v___x_1255_, 1);
                v_isSharedCheck_1264_ = (!lean_is_exclusive(v___x_1255_)) as u8;
                if v_isSharedCheck_1264_ == 0 {
                    v___x_1259_ = v___x_1255_;
                    v_isShared_1260_ = v_isSharedCheck_1264_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1257_);
                    lean_inc(v_fst_1256_);
                    lean_dec(v___x_1255_);
                    v___x_1259_ = lean_box(0);
                    v_isShared_1260_ = v_isSharedCheck_1264_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1260_ == 0 {
                    v___x_1262_ = v___x_1259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_fst_1256_);
                    lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_snd_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_1265_: *mut LeanObject,
    mut v_x_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: u64 = 0;
    let mut v___x_1275_: u64 = 0;
    let mut v___x_1276_: u64 = 0;
    let mut v_fold_1277_: u64 = 0;
    let mut v___x_1278_: u64 = 0;
    let mut v___x_1279_: u64 = 0;
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1266_) == 0 {
                    return v_x_1265_;
                } else {
                    v_key_1267_ = lean_ctor_get(v_x_1266_, 0);
                    v_value_1268_ = lean_ctor_get(v_x_1266_, 1);
                    v_tail_1269_ = lean_ctor_get(v_x_1266_, 2);
                    v_isSharedCheck_1292_ = (!lean_is_exclusive(v_x_1266_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1271_ = v_x_1266_;
                        v_isShared_1272_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1269_);
                        lean_inc(v_value_1268_);
                        lean_inc(v_key_1267_);
                        lean_dec(v_x_1266_);
                        v___x_1271_ = lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1273_ = lean_array_get_size(v_x_1265_);
                v___x_1274_ = l_Lean_instHashableLevelMVarId_hash(v_key_1267_);
                v___x_1275_ = 32u64;
                v___x_1276_ = lean_uint64_shift_right(v___x_1274_, v___x_1275_);
                v_fold_1277_ = lean_uint64_xor(v___x_1274_, v___x_1276_);
                v___x_1278_ = 16u64;
                v___x_1279_ = lean_uint64_shift_right(v_fold_1277_, v___x_1278_);
                v___x_1280_ = lean_uint64_xor(v_fold_1277_, v___x_1279_);
                v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
                v___x_1282_ = lean_usize_of_nat(v___x_1273_);
                v___x_1283_ = 1usize;
                v___x_1284_ = lean_usize_sub(v___x_1282_, v___x_1283_);
                v___x_1285_ = lean_usize_land(v___x_1281_, v___x_1284_);
                v___x_1286_ = lean_array_uget_borrowed(v_x_1265_, v___x_1285_);
                lean_inc(v___x_1286_);
                if v_isShared_1272_ == 0 {
                    lean_ctor_set(v___x_1271_, 2, v___x_1286_);
                    v___x_1288_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_key_1267_);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_value_1268_);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1286_);
                    v___x_1288_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1289_ = lean_array_uset(v_x_1265_, v___x_1285_, v___x_1288_);
                v_x_1265_ = v___x_1289_;
                v_x_1266_ = v_tail_1269_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(
    mut v_i_1293_: *mut LeanObject,
    mut v_source_1294_: *mut LeanObject,
    mut v_target_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v_es_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = lean_array_get_size(v_source_1294_);
                v___x_1297_ = lean_nat_dec_lt(v_i_1293_, v___x_1296_);
                if v___x_1297_ == 0 {
                    lean_dec_ref(v_source_1294_);
                    lean_dec(v_i_1293_);
                    return v_target_1295_;
                } else {
                    v_es_1298_ = lean_array_fget(v_source_1294_, v_i_1293_);
                    v___x_1299_ = lean_box(0);
                    v_source_1300_ = lean_array_fset(v_source_1294_, v_i_1293_, v___x_1299_);
                    v_target_1301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1295_, v_es_1298_);
                    v___x_1302_ = lean_unsigned_to_nat(1);
                    v___x_1303_ = lean_nat_add(v_i_1293_, v___x_1302_);
                    lean_dec(v_i_1293_);
                    v_i_1293_ = v___x_1303_;
                    v_source_1294_ = v_source_1300_;
                    v_target_1295_ = v_target_1301_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(
    mut v_data_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1306_ = lean_array_get_size(v_data_1305_);
    v___x_1307_ = lean_unsigned_to_nat(2);
    v_nbuckets_1308_ = lean_nat_mul(v___x_1306_, v___x_1307_);
    v___x_1309_ = lean_unsigned_to_nat(0);
    v___x_1310_ = lean_box(0);
    v___x_1311_ = lean_mk_array(v_nbuckets_1308_, v___x_1310_);
    v___x_1312_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v___x_1309_, v_data_1305_, v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(
    mut v_a_1313_: *mut LeanObject,
    mut v_b_1314_: *mut LeanObject,
    mut v_x_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1315_) == 0 {
                    lean_dec(v_b_1314_);
                    lean_dec(v_a_1313_);
                    return v_x_1315_;
                } else {
                    v_key_1316_ = lean_ctor_get(v_x_1315_, 0);
                    v_value_1317_ = lean_ctor_get(v_x_1315_, 1);
                    v_tail_1318_ = lean_ctor_get(v_x_1315_, 2);
                    v_isSharedCheck_1330_ = (!lean_is_exclusive(v_x_1315_)) as u8;
                    if v_isSharedCheck_1330_ == 0 {
                        v___x_1320_ = v_x_1315_;
                        v_isShared_1321_ = v_isSharedCheck_1330_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1318_);
                        lean_inc(v_value_1317_);
                        lean_inc(v_key_1316_);
                        lean_dec(v_x_1315_);
                        v___x_1320_ = lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1330_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1322_ = l_Lean_instBEqLevelMVarId_beq(v_key_1316_, v_a_1313_);
                if v___x_1322_ == 0 {
                    v___x_1323_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1313_, v_b_1314_, v_tail_1318_);
                    if v_isShared_1321_ == 0 {
                        lean_ctor_set(v___x_1320_, 2, v___x_1323_);
                        v___x_1325_ = v___x_1320_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_key_1316_);
                        lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_value_1317_);
                        lean_ctor_set(v_reuseFailAlloc_1326_, 2, v___x_1323_);
                        v___x_1325_ = v_reuseFailAlloc_1326_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1317_);
                    lean_dec(v_key_1316_);
                    if v_isShared_1321_ == 0 {
                        lean_ctor_set(v___x_1320_, 1, v_b_1314_);
                        lean_ctor_set(v___x_1320_, 0, v_a_1313_);
                        v___x_1328_ = v___x_1320_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1313_);
                        lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_b_1314_);
                        lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_tail_1318_);
                        v___x_1328_ = v_reuseFailAlloc_1329_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1325_;
            }
            3 => {
                return v___x_1328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(
    mut v_a_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    let mut v_key_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1332_) == 0 {
                    v___x_1333_ = 0;
                    return v___x_1333_;
                } else {
                    v_key_1334_ = lean_ctor_get(v_x_1332_, 0);
                    v_tail_1335_ = lean_ctor_get(v_x_1332_, 2);
                    v___x_1336_ = l_Lean_instBEqLevelMVarId_beq(v_key_1334_, v_a_1331_);
                    if v___x_1336_ == 0 {
                        v_x_1332_ = v_tail_1335_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1336_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(
    mut v_a_1338_: *mut LeanObject,
    mut v_x_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: u8 = 0;
    let mut v_r_1341_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1338_, v_x_1339_);
    lean_dec(v_x_1339_);
    lean_dec(v_a_1338_);
    v_r_1341_ = lean_box((v_res_1340_) as usize);
    return v_r_1341_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(
    mut v_m_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
    mut v_b_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u64 = 0;
    let mut v___x_1352_: u64 = 0;
    let mut v___x_1353_: u64 = 0;
    let mut v_fold_1354_: u64 = 0;
    let mut v___x_1355_: u64 = 0;
    let mut v___x_1356_: u64 = 0;
    let mut v___x_1357_: u64 = 0;
    let mut v___x_1358_: usize = 0;
    let mut v___x_1359_: usize = 0;
    let mut v___x_1360_: usize = 0;
    let mut v___x_1361_: usize = 0;
    let mut v___x_1362_: usize = 0;
    let mut v_bkt_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v_val_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1345_ = lean_ctor_get(v_m_1342_, 0);
                v_buckets_1346_ = lean_ctor_get(v_m_1342_, 1);
                v_isSharedCheck_1389_ = (!lean_is_exclusive(v_m_1342_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v___x_1348_ = v_m_1342_;
                    v_isShared_1349_ = v_isSharedCheck_1389_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1346_);
                    lean_inc(v_size_1345_);
                    lean_dec(v_m_1342_);
                    v___x_1348_ = lean_box(0);
                    v_isShared_1349_ = v_isSharedCheck_1389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1350_ = lean_array_get_size(v_buckets_1346_);
                v___x_1351_ = l_Lean_instHashableLevelMVarId_hash(v_a_1343_);
                v___x_1352_ = 32u64;
                v___x_1353_ = lean_uint64_shift_right(v___x_1351_, v___x_1352_);
                v_fold_1354_ = lean_uint64_xor(v___x_1351_, v___x_1353_);
                v___x_1355_ = 16u64;
                v___x_1356_ = lean_uint64_shift_right(v_fold_1354_, v___x_1355_);
                v___x_1357_ = lean_uint64_xor(v_fold_1354_, v___x_1356_);
                v___x_1358_ = lean_uint64_to_usize(v___x_1357_);
                v___x_1359_ = lean_usize_of_nat(v___x_1350_);
                v___x_1360_ = 1usize;
                v___x_1361_ = lean_usize_sub(v___x_1359_, v___x_1360_);
                v___x_1362_ = lean_usize_land(v___x_1358_, v___x_1361_);
                v_bkt_1363_ = lean_array_uget_borrowed(v_buckets_1346_, v___x_1362_);
                v___x_1364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1343_, v_bkt_1363_);
                if v___x_1364_ == 0 {
                    v___x_1365_ = lean_unsigned_to_nat(1);
                    v_size_x27_1366_ = lean_nat_add(v_size_1345_, v___x_1365_);
                    lean_dec(v_size_1345_);
                    lean_inc(v_bkt_1363_);
                    v___x_1367_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1367_, 0, v_a_1343_);
                    lean_ctor_set(v___x_1367_, 1, v_b_1344_);
                    lean_ctor_set(v___x_1367_, 2, v_bkt_1363_);
                    v_buckets_x27_1368_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1367_);
                    v___x_1369_ = lean_unsigned_to_nat(4);
                    v___x_1370_ = lean_nat_mul(v_size_x27_1366_, v___x_1369_);
                    v___x_1371_ = lean_unsigned_to_nat(3);
                    v___x_1372_ = lean_nat_div(v___x_1370_, v___x_1371_);
                    lean_dec(v___x_1370_);
                    v___x_1373_ = lean_array_get_size(v_buckets_x27_1368_);
                    v___x_1374_ = lean_nat_dec_le(v___x_1372_, v___x_1373_);
                    lean_dec(v___x_1372_);
                    if v___x_1374_ == 0 {
                        v_val_1375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_1368_);
                        if v_isShared_1349_ == 0 {
                            lean_ctor_set(v___x_1348_, 1, v_val_1375_);
                            lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1377_ = v___x_1348_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_size_x27_1366_);
                            lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_val_1375_);
                            v___x_1377_ = v_reuseFailAlloc_1378_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1349_ == 0 {
                            lean_ctor_set(v___x_1348_, 1, v_buckets_x27_1368_);
                            lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1380_ = v___x_1348_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_size_x27_1366_);
                            lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_buckets_x27_1368_);
                            v___x_1380_ = v_reuseFailAlloc_1381_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1363_);
                    v___x_1382_ = lean_box(0);
                    v_buckets_x27_1383_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1382_);
                    v___x_1384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1343_, v_b_1344_, v_bkt_1363_);
                    v___x_1385_ = lean_array_uset(v_buckets_x27_1383_, v___x_1362_, v___x_1384_);
                    if v_isShared_1349_ == 0 {
                        lean_ctor_set(v___x_1348_, 1, v___x_1385_);
                        v___x_1387_ = v___x_1348_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_1345_);
                        lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
                        v___x_1387_ = v_reuseFailAlloc_1388_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1377_;
            }
            3 => {
                return v___x_1380_;
            }
            4 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(
    mut v_a_1390_: *mut LeanObject,
    mut v_x_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1391_) == 0 {
                    v___x_1392_ = lean_box(0);
                    return v___x_1392_;
                } else {
                    v_key_1393_ = lean_ctor_get(v_x_1391_, 0);
                    v_value_1394_ = lean_ctor_get(v_x_1391_, 1);
                    v_tail_1395_ = lean_ctor_get(v_x_1391_, 2);
                    v___x_1396_ = l_Lean_instBEqLevelMVarId_beq(v_key_1393_, v_a_1390_);
                    if v___x_1396_ == 0 {
                        v_x_1391_ = v_tail_1395_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1394_);
                        v___x_1398_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1398_, 0, v_value_1394_);
                        return v___x_1398_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1399_: *mut LeanObject,
    mut v_x_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1401_: *mut LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1399_, v_x_1400_);
    lean_dec(v_x_1400_);
    lean_dec(v_a_1399_);
    return v_res_1401_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(
    mut v_m_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u64 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v___x_1408_: u64 = 0;
    let mut v_fold_1409_: u64 = 0;
    let mut v___x_1410_: u64 = 0;
    let mut v___x_1411_: u64 = 0;
    let mut v___x_1412_: u64 = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: usize = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: usize = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1404_ = lean_ctor_get(v_m_1402_, 1);
    v___x_1405_ = lean_array_get_size(v_buckets_1404_);
    v___x_1406_ = l_Lean_instHashableLevelMVarId_hash(v_a_1403_);
    v___x_1407_ = 32u64;
    v___x_1408_ = lean_uint64_shift_right(v___x_1406_, v___x_1407_);
    v_fold_1409_ = lean_uint64_xor(v___x_1406_, v___x_1408_);
    v___x_1410_ = 16u64;
    v___x_1411_ = lean_uint64_shift_right(v_fold_1409_, v___x_1410_);
    v___x_1412_ = lean_uint64_xor(v_fold_1409_, v___x_1411_);
    v___x_1413_ = lean_uint64_to_usize(v___x_1412_);
    v___x_1414_ = lean_usize_of_nat(v___x_1405_);
    v___x_1415_ = 1usize;
    v___x_1416_ = lean_usize_sub(v___x_1414_, v___x_1415_);
    v___x_1417_ = lean_usize_land(v___x_1413_, v___x_1416_);
    v___x_1418_ = lean_array_uget_borrowed(v_buckets_1404_, v___x_1417_);
    v___x_1419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1403_, v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(
    mut v_m_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1420_, v_a_1421_);
    lean_dec(v_a_1421_);
    lean_dec_ref(v_m_1420_);
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(
    mut v_u_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_abstractLevels_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmap_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v_a_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___y_1499_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut v_a_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_abstractLevels_1428_ = lean_ctor_get_uint8(
                    v_a_1427_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                if v_abstractLevels_1428_ == 0 {
                    v___x_1429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1429_, 0, v_u_1426_);
                    lean_ctor_set(v___x_1429_, 1, v_a_1427_);
                    return v___x_1429_;
                } else {
                    v_ngen_1430_ = lean_ctor_get(v_a_1427_, 0);
                    v_lctx_1431_ = lean_ctor_get(v_a_1427_, 1);
                    v_mctx_1432_ = lean_ctor_get(v_a_1427_, 2);
                    v_nextParamIdx_1433_ = lean_ctor_get(v_a_1427_, 3);
                    v_paramNames_1434_ = lean_ctor_get(v_a_1427_, 4);
                    v_fvars_1435_ = lean_ctor_get(v_a_1427_, 5);
                    v_mvars_1436_ = lean_ctor_get(v_a_1427_, 6);
                    v_lmap_1437_ = lean_ctor_get(v_a_1427_, 7);
                    v_emap_1438_ = lean_ctor_get(v_a_1427_, 8);
                    v___x_1439_ = l_Lean_Level_hasMVar(v_u_1426_);
                    if v___x_1439_ == 0 {
                        v___x_1440_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1440_, 0, v_u_1426_);
                        lean_ctor_set(v___x_1440_, 1, v_a_1427_);
                        return v___x_1440_;
                    } else {
                        match lean_obj_tag(v_u_1426_) {
                            1 => {
                                v_a_1441_ = lean_ctor_get(v_u_1426_, 0);
                                lean_inc(v_a_1441_);
                                v___x_1442_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1441_, v_a_1427_);
                                v_fst_1443_ = lean_ctor_get(v___x_1442_, 0);
                                v_snd_1444_ = lean_ctor_get(v___x_1442_, 1);
                                v_isSharedCheck_1458_ = (!lean_is_exclusive(v___x_1442_)) as u8;
                                if v_isSharedCheck_1458_ == 0 {
                                    v___x_1446_ = v___x_1442_;
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_1444_);
                                    lean_inc(v_fst_1443_);
                                    lean_dec(v___x_1442_);
                                    v___x_1446_ = lean_box(0);
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                }
                            }
                            2 => {
                                v_a_1459_ = lean_ctor_get(v_u_1426_, 0);
                                v_a_1460_ = lean_ctor_get(v_u_1426_, 1);
                                lean_inc(v_a_1459_);
                                v___x_1461_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1459_, v_a_1427_);
                                v_fst_1462_ = lean_ctor_get(v___x_1461_, 0);
                                lean_inc(v_fst_1462_);
                                v_snd_1463_ = lean_ctor_get(v___x_1461_, 1);
                                lean_inc(v_snd_1463_);
                                lean_dec_ref(v___x_1461_);
                                lean_inc(v_a_1460_);
                                v___x_1464_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1460_, v_snd_1463_);
                                v_fst_1465_ = lean_ctor_get(v___x_1464_, 0);
                                v_snd_1466_ = lean_ctor_get(v___x_1464_, 1);
                                v_isSharedCheck_1486_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                                if v_isSharedCheck_1486_ == 0 {
                                    v___x_1468_ = v___x_1464_;
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_snd_1466_);
                                    lean_inc(v_fst_1465_);
                                    lean_dec(v___x_1464_);
                                    v___x_1468_ = lean_box(0);
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                }
                            }
                            3 => {
                                v_a_1487_ = lean_ctor_get(v_u_1426_, 0);
                                v_a_1488_ = lean_ctor_get(v_u_1426_, 1);
                                lean_inc(v_a_1487_);
                                v___x_1489_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1487_, v_a_1427_);
                                v_fst_1490_ = lean_ctor_get(v___x_1489_, 0);
                                lean_inc(v_fst_1490_);
                                v_snd_1491_ = lean_ctor_get(v___x_1489_, 1);
                                lean_inc(v_snd_1491_);
                                lean_dec_ref(v___x_1489_);
                                lean_inc(v_a_1488_);
                                v___x_1492_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1488_, v_snd_1491_);
                                v_fst_1493_ = lean_ctor_get(v___x_1492_, 0);
                                v_snd_1494_ = lean_ctor_get(v___x_1492_, 1);
                                v_isSharedCheck_1514_ = (!lean_is_exclusive(v___x_1492_)) as u8;
                                if v_isSharedCheck_1514_ == 0 {
                                    v___x_1496_ = v___x_1492_;
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_snd_1494_);
                                    lean_inc(v_fst_1493_);
                                    lean_dec(v___x_1492_);
                                    v___x_1496_ = lean_box(0);
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                }
                            }
                            5 => {
                                v_a_1515_ = lean_ctor_get(v_u_1426_, 0);
                                v_depth_1516_ = lean_ctor_get(v_mctx_1432_, 0);
                                lean_inc(v_a_1515_);
                                v___x_1517_ =
                                    l_Lean_MetavarContext_getLevelDepth(v_mctx_1432_, v_a_1515_);
                                v___x_1518_ = lean_nat_dec_eq(v___x_1517_, v_depth_1516_);
                                lean_dec(v___x_1517_);
                                if v___x_1518_ == 0 {
                                    v___x_1519_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_1519_, 0, v_u_1426_);
                                    lean_ctor_set(v___x_1519_, 1, v_a_1427_);
                                    return v___x_1519_;
                                } else {
                                    lean_inc(v_a_1515_);
                                    lean_dec_ref_known(v_u_1426_, 1);
                                    v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_1437_, v_a_1515_);
                                    if lean_obj_tag(v___x_1520_) == 0 {
                                        lean_inc_ref(v_emap_1438_);
                                        lean_inc_ref(v_lmap_1437_);
                                        lean_inc_ref(v_mvars_1436_);
                                        lean_inc_ref(v_fvars_1435_);
                                        lean_inc_ref(v_paramNames_1434_);
                                        lean_inc(v_nextParamIdx_1433_);
                                        lean_inc_ref(v_mctx_1432_);
                                        lean_inc_ref(v_lctx_1431_);
                                        lean_inc_ref(v_ngen_1430_);
                                        v_isSharedCheck_1535_ =
                                            (!lean_is_exclusive(v_a_1427_)) as u8;
                                        if v_isSharedCheck_1535_ == 0 {
                                            v_unused_1536_ = lean_ctor_get(v_a_1427_, 8);
                                            lean_dec(v_unused_1536_);
                                            v_unused_1537_ = lean_ctor_get(v_a_1427_, 7);
                                            lean_dec(v_unused_1537_);
                                            v_unused_1538_ = lean_ctor_get(v_a_1427_, 6);
                                            lean_dec(v_unused_1538_);
                                            v_unused_1539_ = lean_ctor_get(v_a_1427_, 5);
                                            lean_dec(v_unused_1539_);
                                            v_unused_1540_ = lean_ctor_get(v_a_1427_, 4);
                                            lean_dec(v_unused_1540_);
                                            v_unused_1541_ = lean_ctor_get(v_a_1427_, 3);
                                            lean_dec(v_unused_1541_);
                                            v_unused_1542_ = lean_ctor_get(v_a_1427_, 2);
                                            lean_dec(v_unused_1542_);
                                            v_unused_1543_ = lean_ctor_get(v_a_1427_, 1);
                                            lean_dec(v_unused_1543_);
                                            v_unused_1544_ = lean_ctor_get(v_a_1427_, 0);
                                            lean_dec(v_unused_1544_);
                                            v___x_1522_ = v_a_1427_;
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        } else {
                                            lean_dec(v_a_1427_);
                                            v___x_1522_ = lean_box(0);
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_1515_);
                                        v_val_1545_ = lean_ctor_get(v___x_1520_, 0);
                                        lean_inc(v_val_1545_);
                                        lean_dec_ref_known(v___x_1520_, 1);
                                        v___x_1546_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_1546_, 0, v_val_1545_);
                                        lean_ctor_set(v___x_1546_, 1, v_a_1427_);
                                        return v___x_1546_;
                                    }
                                }
                            }
                            _ => {
                                v___x_1547_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1547_, 0, v_u_1426_);
                                lean_ctor_set(v___x_1547_, 1, v_a_1427_);
                                return v___x_1547_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1448_ = lean_ptr_addr(v_a_1441_);
                v___x_1449_ = lean_ptr_addr(v_fst_1443_);
                v___x_1450_ = lean_usize_dec_eq(v___x_1448_, v___x_1449_);
                if v___x_1450_ == 0 {
                    lean_dec_ref_known(v_u_1426_, 1);
                    v___x_1451_ = l_Lean_Level_succ___override(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        lean_ctor_set(v___x_1446_, 0, v___x_1451_);
                        v___x_1453_ = v___x_1446_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
                        lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1444_);
                        v___x_1453_ = v_reuseFailAlloc_1454_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        lean_ctor_set(v___x_1446_, 0, v_u_1426_);
                        v___x_1456_ = v___x_1446_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_u_1426_);
                        lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1444_);
                        v___x_1456_ = v_reuseFailAlloc_1457_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1453_;
            }
            3 => {
                return v___x_1456_;
            }
            4 => {
                v___x_1480_ = lean_ptr_addr(v_a_1459_);
                v___x_1481_ = lean_ptr_addr(v_fst_1462_);
                v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
                if v___x_1482_ == 0 {
                    v___y_1471_ = v___x_1482_;
                    state = 5;
                    continue;
                } else {
                    v___x_1483_ = lean_ptr_addr(v_a_1460_);
                    v___x_1484_ = lean_ptr_addr(v_fst_1465_);
                    v___x_1485_ = lean_usize_dec_eq(v___x_1483_, v___x_1484_);
                    v___y_1471_ = v___x_1485_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_1471_ == 0 {
                    lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1472_ = l_Lean_mkLevelMax_x27(v_fst_1462_, v_fst_1465_);
                    if v_isShared_1469_ == 0 {
                        lean_ctor_set(v___x_1468_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1468_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_snd_1466_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1476_ = l_Lean_simpLevelMax_x27(v_fst_1462_, v_fst_1465_, v_u_1426_);
                    lean_dec_ref_known(v_u_1426_, 2);
                    lean_dec(v_fst_1465_);
                    lean_dec(v_fst_1462_);
                    if v_isShared_1469_ == 0 {
                        lean_ctor_set(v___x_1468_, 0, v___x_1476_);
                        v___x_1478_ = v___x_1468_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                        lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_snd_1466_);
                        v___x_1478_ = v_reuseFailAlloc_1479_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1474_;
            }
            7 => {
                return v___x_1478_;
            }
            8 => {
                v___x_1508_ = lean_ptr_addr(v_a_1487_);
                v___x_1509_ = lean_ptr_addr(v_fst_1490_);
                v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
                if v___x_1510_ == 0 {
                    v___y_1499_ = v___x_1510_;
                    state = 9;
                    continue;
                } else {
                    v___x_1511_ = lean_ptr_addr(v_a_1488_);
                    v___x_1512_ = lean_ptr_addr(v_fst_1493_);
                    v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
                    v___y_1499_ = v___x_1513_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v___y_1499_ == 0 {
                    lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1500_ = l_Lean_mkLevelIMax_x27(v_fst_1490_, v_fst_1493_);
                    if v_isShared_1497_ == 0 {
                        lean_ctor_set(v___x_1496_, 0, v___x_1500_);
                        v___x_1502_ = v___x_1496_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                        lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1494_);
                        v___x_1502_ = v_reuseFailAlloc_1503_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_1504_ = l_Lean_simpLevelIMax_x27(v_fst_1490_, v_fst_1493_, v_u_1426_);
                    lean_dec_ref_known(v_u_1426_, 2);
                    if v_isShared_1497_ == 0 {
                        lean_ctor_set(v___x_1496_, 0, v___x_1504_);
                        v___x_1506_ = v___x_1496_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                        lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1494_);
                        v___x_1506_ = v_reuseFailAlloc_1507_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1502_;
            }
            11 => {
                return v___x_1506_;
            }
            12 => {
                v___x_1524_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
                lean_inc(v_nextParamIdx_1433_);
                v___x_1525_ = l_Lean_Name_num___override(v___x_1524_, v_nextParamIdx_1433_);
                lean_inc(v___x_1525_);
                v___x_1526_ = l_Lean_mkLevelParam(v___x_1525_);
                v___x_1527_ = lean_unsigned_to_nat(1);
                v___x_1528_ = lean_nat_add(v_nextParamIdx_1433_, v___x_1527_);
                lean_dec(v_nextParamIdx_1433_);
                v___x_1529_ = lean_array_push(v_paramNames_1434_, v___x_1525_);
                lean_inc(v___x_1526_);
                v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_1437_, v_a_1515_, v___x_1526_);
                if v_isShared_1523_ == 0 {
                    lean_ctor_set(v___x_1522_, 7, v___x_1530_);
                    lean_ctor_set(v___x_1522_, 4, v___x_1529_);
                    lean_ctor_set(v___x_1522_, 3, v___x_1528_);
                    v___x_1532_ = v___x_1522_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_ngen_1430_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_lctx_1431_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_mctx_1432_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1528_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 4, v___x_1529_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 5, v_fvars_1435_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_mvars_1436_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 7, v___x_1530_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 8, v_emap_1438_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1534_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_abstractLevels_1428_,
                    );
                    v___x_1532_ = v_reuseFailAlloc_1534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1533_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1533_, 0, v___x_1526_);
                lean_ctor_set(v___x_1533_, 1, v___x_1532_);
                return v___x_1533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(
    mut v_00_u03b2_1548_: *mut LeanObject,
    mut v_m_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1549_, v_a_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(
    mut v_00_u03b2_1552_: *mut LeanObject,
    mut v_m_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_1552_, v_m_1553_, v_a_1554_);
    lean_dec(v_a_1554_);
    lean_dec_ref(v_m_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(
    mut v_00_u03b2_1556_: *mut LeanObject,
    mut v_m_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_b_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_1557_, v_a_1558_, v_b_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(
    mut v_00_u03b2_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
    mut v_x_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    v___x_1564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1562_, v_x_1563_);
    return v___x_1564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
    mut v_x_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1568_: *mut LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_1565_, v_a_1566_, v_x_1567_);
    lean_dec(v_x_1567_);
    lean_dec(v_a_1566_);
    return v_res_1568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(
    mut v_00_u03b2_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
    mut v_x_1571_: *mut LeanObject,
) -> u8 {
    let mut v___x_1572_: u8 = 0;
    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1570_, v_x_1571_);
    return v___x_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(
    mut v_00_u03b2_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
    mut v_x_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1576_: u8 = 0;
    let mut v_r_1577_: *mut LeanObject = core::ptr::null_mut();
    v_res_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_1573_, v_a_1574_, v_x_1575_);
    lean_dec(v_x_1575_);
    lean_dec(v_a_1574_);
    v_r_1577_ = lean_box((v_res_1576_) as usize);
    return v_r_1577_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(
    mut v_00_u03b2_1578_: *mut LeanObject,
    mut v_data_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(
    mut v_00_u03b2_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
    mut v_b_1583_: *mut LeanObject,
    mut v_x_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1582_, v_b_1583_, v_x_1584_);
    return v___x_1585_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1586_: *mut LeanObject,
    mut v_i_1587_: *mut LeanObject,
    mut v_source_1588_: *mut LeanObject,
    mut v_target_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1590_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_1587_, v_source_1588_, v_target_1589_);
    return v___x_1590_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1591_: *mut LeanObject,
    mut v_x_1592_: *mut LeanObject,
    mut v_x_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1592_, v_x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(
    mut v_e_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmap_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1608_: u8 = 0;
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1597_ = l_Lean_Expr_hasMVar(v_e_1595_);
                if v___x_1597_ == 0 {
                    v___x_1598_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1598_, 0, v_e_1595_);
                    lean_ctor_set(v___x_1598_, 1, v___y_1596_);
                    return v___x_1598_;
                } else {
                    v_ngen_1599_ = lean_ctor_get(v___y_1596_, 0);
                    v_lctx_1600_ = lean_ctor_get(v___y_1596_, 1);
                    v_mctx_1601_ = lean_ctor_get(v___y_1596_, 2);
                    v_nextParamIdx_1602_ = lean_ctor_get(v___y_1596_, 3);
                    v_paramNames_1603_ = lean_ctor_get(v___y_1596_, 4);
                    v_fvars_1604_ = lean_ctor_get(v___y_1596_, 5);
                    v_mvars_1605_ = lean_ctor_get(v___y_1596_, 6);
                    v_lmap_1606_ = lean_ctor_get(v___y_1596_, 7);
                    v_emap_1607_ = lean_ctor_get(v___y_1596_, 8);
                    v_abstractLevels_1608_ = lean_ctor_get_uint8(
                        v___y_1596_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    );
                    v_isSharedCheck_1625_ = (!lean_is_exclusive(v___y_1596_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1610_ = v___y_1596_;
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_emap_1607_);
                        lean_inc(v_lmap_1606_);
                        lean_inc(v_mvars_1605_);
                        lean_inc(v_fvars_1604_);
                        lean_inc(v_paramNames_1603_);
                        lean_inc(v_nextParamIdx_1602_);
                        lean_inc(v_mctx_1601_);
                        lean_inc(v_lctx_1600_);
                        lean_inc(v_ngen_1599_);
                        lean_dec(v___y_1596_);
                        v___x_1610_ = lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = l_Lean_instantiateMVarsCore(v_mctx_1601_, v_e_1595_);
                v_fst_1613_ = lean_ctor_get(v___x_1612_, 0);
                v_snd_1614_ = lean_ctor_get(v___x_1612_, 1);
                v_isSharedCheck_1624_ = (!lean_is_exclusive(v___x_1612_)) as u8;
                if v_isSharedCheck_1624_ == 0 {
                    v___x_1616_ = v___x_1612_;
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1614_);
                    lean_inc(v_fst_1613_);
                    lean_dec(v___x_1612_);
                    v___x_1616_ = lean_box(0);
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1611_ == 0 {
                    lean_ctor_set(v___x_1610_, 2, v_snd_1614_);
                    v___x_1619_ = v___x_1610_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_ngen_1599_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_lctx_1600_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_snd_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_nextParamIdx_1602_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_paramNames_1603_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 5, v_fvars_1604_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 6, v_mvars_1605_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 7, v_lmap_1606_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 8, v_emap_1607_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1623_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_abstractLevels_1608_,
                    );
                    v___x_1619_ = v_reuseFailAlloc_1623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1617_ == 0 {
                    lean_ctor_set(v___x_1616_, 1, v___x_1619_);
                    v___x_1621_ = v___x_1616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(
    mut v_a_1626_: *mut LeanObject,
    mut v_x_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1627_) == 0 {
                    v___x_1628_ = lean_box(0);
                    return v___x_1628_;
                } else {
                    v_key_1629_ = lean_ctor_get(v_x_1627_, 0);
                    v_value_1630_ = lean_ctor_get(v_x_1627_, 1);
                    v_tail_1631_ = lean_ctor_get(v_x_1627_, 2);
                    v___x_1632_ = l_Lean_instBEqMVarId_beq(v_key_1629_, v_a_1626_);
                    if v___x_1632_ == 0 {
                        v_x_1627_ = v_tail_1631_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1630_);
                        v___x_1634_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1634_, 0, v_value_1630_);
                        return v___x_1634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1635_: *mut LeanObject,
    mut v_x_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1637_: *mut LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_1635_, v_x_1636_);
    lean_dec(v_x_1636_);
    lean_dec(v_a_1635_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(
    mut v_m_1638_: *mut LeanObject,
    mut v_a_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u64 = 0;
    let mut v___x_1643_: u64 = 0;
    let mut v___x_1644_: u64 = 0;
    let mut v_fold_1645_: u64 = 0;
    let mut v___x_1646_: u64 = 0;
    let mut v___x_1647_: u64 = 0;
    let mut v___x_1648_: u64 = 0;
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: usize = 0;
    let mut v___x_1653_: usize = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1640_ = lean_ctor_get(v_m_1638_, 1);
    v___x_1641_ = lean_array_get_size(v_buckets_1640_);
    v___x_1642_ = l_Lean_instHashableMVarId_hash(v_a_1639_);
    v___x_1643_ = 32u64;
    v___x_1644_ = lean_uint64_shift_right(v___x_1642_, v___x_1643_);
    v_fold_1645_ = lean_uint64_xor(v___x_1642_, v___x_1644_);
    v___x_1646_ = 16u64;
    v___x_1647_ = lean_uint64_shift_right(v_fold_1645_, v___x_1646_);
    v___x_1648_ = lean_uint64_xor(v_fold_1645_, v___x_1647_);
    v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
    v___x_1650_ = lean_usize_of_nat(v___x_1641_);
    v___x_1651_ = 1usize;
    v___x_1652_ = lean_usize_sub(v___x_1650_, v___x_1651_);
    v___x_1653_ = lean_usize_land(v___x_1649_, v___x_1652_);
    v___x_1654_ = lean_array_uget_borrowed(v_buckets_1640_, v___x_1653_);
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_1639_, v___x_1654_);
    return v___x_1655_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(
    mut v_m_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1658_: *mut LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_1656_, v_a_1657_);
    lean_dec(v_a_1657_);
    lean_dec_ref(v_m_1656_);
    return v_res_1658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(
    mut v_a_1659_: *mut LeanObject,
    mut v_x_1660_: *mut LeanObject,
) -> u8 {
    let mut v___x_1661_: u8 = 0;
    let mut v_key_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1660_) == 0 {
                    v___x_1661_ = 0;
                    return v___x_1661_;
                } else {
                    v_key_1662_ = lean_ctor_get(v_x_1660_, 0);
                    v_tail_1663_ = lean_ctor_get(v_x_1660_, 2);
                    v___x_1664_ = l_Lean_instBEqMVarId_beq(v_key_1662_, v_a_1659_);
                    if v___x_1664_ == 0 {
                        v_x_1660_ = v_tail_1663_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1664_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(
    mut v_a_1666_: *mut LeanObject,
    mut v_x_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1668_: u8 = 0;
    let mut v_r_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_1666_, v_x_1667_);
    lean_dec(v_x_1667_);
    lean_dec(v_a_1666_);
    v_r_1669_ = lean_box((v_res_1668_) as usize);
    return v_r_1669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(
    mut v_a_1670_: *mut LeanObject,
    mut v_b_1671_: *mut LeanObject,
    mut v_x_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1672_) == 0 {
                    lean_dec(v_b_1671_);
                    lean_dec(v_a_1670_);
                    return v_x_1672_;
                } else {
                    v_key_1673_ = lean_ctor_get(v_x_1672_, 0);
                    v_value_1674_ = lean_ctor_get(v_x_1672_, 1);
                    v_tail_1675_ = lean_ctor_get(v_x_1672_, 2);
                    v_isSharedCheck_1687_ = (!lean_is_exclusive(v_x_1672_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1677_ = v_x_1672_;
                        v_isShared_1678_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1675_);
                        lean_inc(v_value_1674_);
                        lean_inc(v_key_1673_);
                        lean_dec(v_x_1672_);
                        v___x_1677_ = lean_box(0);
                        v_isShared_1678_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1679_ = l_Lean_instBEqMVarId_beq(v_key_1673_, v_a_1670_);
                if v___x_1679_ == 0 {
                    v___x_1680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_1670_, v_b_1671_, v_tail_1675_);
                    if v_isShared_1678_ == 0 {
                        lean_ctor_set(v___x_1677_, 2, v___x_1680_);
                        v___x_1682_ = v___x_1677_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_key_1673_);
                        lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_value_1674_);
                        lean_ctor_set(v_reuseFailAlloc_1683_, 2, v___x_1680_);
                        v___x_1682_ = v_reuseFailAlloc_1683_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1674_);
                    lean_dec(v_key_1673_);
                    if v_isShared_1678_ == 0 {
                        lean_ctor_set(v___x_1677_, 1, v_b_1671_);
                        lean_ctor_set(v___x_1677_, 0, v_a_1670_);
                        v___x_1685_ = v___x_1677_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1670_);
                        lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_b_1671_);
                        lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_tail_1675_);
                        v___x_1685_ = v_reuseFailAlloc_1686_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1682_;
            }
            3 => {
                return v___x_1685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(
    mut v_x_1688_: *mut LeanObject,
    mut v_x_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u64 = 0;
    let mut v___x_1698_: u64 = 0;
    let mut v___x_1699_: u64 = 0;
    let mut v_fold_1700_: u64 = 0;
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: u64 = 0;
    let mut v___x_1703_: u64 = 0;
    let mut v___x_1704_: usize = 0;
    let mut v___x_1705_: usize = 0;
    let mut v___x_1706_: usize = 0;
    let mut v___x_1707_: usize = 0;
    let mut v___x_1708_: usize = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1689_) == 0 {
                    return v_x_1688_;
                } else {
                    v_key_1690_ = lean_ctor_get(v_x_1689_, 0);
                    v_value_1691_ = lean_ctor_get(v_x_1689_, 1);
                    v_tail_1692_ = lean_ctor_get(v_x_1689_, 2);
                    v_isSharedCheck_1715_ = (!lean_is_exclusive(v_x_1689_)) as u8;
                    if v_isSharedCheck_1715_ == 0 {
                        v___x_1694_ = v_x_1689_;
                        v_isShared_1695_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1692_);
                        lean_inc(v_value_1691_);
                        lean_inc(v_key_1690_);
                        lean_dec(v_x_1689_);
                        v___x_1694_ = lean_box(0);
                        v_isShared_1695_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1696_ = lean_array_get_size(v_x_1688_);
                v___x_1697_ = l_Lean_instHashableMVarId_hash(v_key_1690_);
                v___x_1698_ = 32u64;
                v___x_1699_ = lean_uint64_shift_right(v___x_1697_, v___x_1698_);
                v_fold_1700_ = lean_uint64_xor(v___x_1697_, v___x_1699_);
                v___x_1701_ = 16u64;
                v___x_1702_ = lean_uint64_shift_right(v_fold_1700_, v___x_1701_);
                v___x_1703_ = lean_uint64_xor(v_fold_1700_, v___x_1702_);
                v___x_1704_ = lean_uint64_to_usize(v___x_1703_);
                v___x_1705_ = lean_usize_of_nat(v___x_1696_);
                v___x_1706_ = 1usize;
                v___x_1707_ = lean_usize_sub(v___x_1705_, v___x_1706_);
                v___x_1708_ = lean_usize_land(v___x_1704_, v___x_1707_);
                v___x_1709_ = lean_array_uget_borrowed(v_x_1688_, v___x_1708_);
                lean_inc(v___x_1709_);
                if v_isShared_1695_ == 0 {
                    lean_ctor_set(v___x_1694_, 2, v___x_1709_);
                    v___x_1711_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_key_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_value_1691_);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1712_ = lean_array_uset(v_x_1688_, v___x_1708_, v___x_1711_);
                v_x_1688_ = v___x_1712_;
                v_x_1689_ = v_tail_1692_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(
    mut v_i_1716_: *mut LeanObject,
    mut v_source_1717_: *mut LeanObject,
    mut v_target_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v_es_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_array_get_size(v_source_1717_);
                v___x_1720_ = lean_nat_dec_lt(v_i_1716_, v___x_1719_);
                if v___x_1720_ == 0 {
                    lean_dec_ref(v_source_1717_);
                    lean_dec(v_i_1716_);
                    return v_target_1718_;
                } else {
                    v_es_1721_ = lean_array_fget(v_source_1717_, v_i_1716_);
                    v___x_1722_ = lean_box(0);
                    v_source_1723_ = lean_array_fset(v_source_1717_, v_i_1716_, v___x_1722_);
                    v_target_1724_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_1718_, v_es_1721_);
                    v___x_1725_ = lean_unsigned_to_nat(1);
                    v___x_1726_ = lean_nat_add(v_i_1716_, v___x_1725_);
                    lean_dec(v_i_1716_);
                    v_i_1716_ = v___x_1726_;
                    v_source_1717_ = v_source_1723_;
                    v_target_1718_ = v_target_1724_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(
    mut v_data_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_array_get_size(v_data_1728_);
    v___x_1730_ = lean_unsigned_to_nat(2);
    v_nbuckets_1731_ = lean_nat_mul(v___x_1729_, v___x_1730_);
    v___x_1732_ = lean_unsigned_to_nat(0);
    v___x_1733_ = lean_box(0);
    v___x_1734_ = lean_mk_array(v_nbuckets_1731_, v___x_1733_);
    v___x_1735_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_1732_, v_data_1728_, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(
    mut v_m_1736_: *mut LeanObject,
    mut v_a_1737_: *mut LeanObject,
    mut v_b_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v_fold_1748_: u64 = 0;
    let mut v___x_1749_: u64 = 0;
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: usize = 0;
    let mut v___x_1753_: usize = 0;
    let mut v___x_1754_: usize = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1756_: usize = 0;
    let mut v_bkt_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_val_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1739_ = lean_ctor_get(v_m_1736_, 0);
                v_buckets_1740_ = lean_ctor_get(v_m_1736_, 1);
                v_isSharedCheck_1783_ = (!lean_is_exclusive(v_m_1736_)) as u8;
                if v_isSharedCheck_1783_ == 0 {
                    v___x_1742_ = v_m_1736_;
                    v_isShared_1743_ = v_isSharedCheck_1783_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1740_);
                    lean_inc(v_size_1739_);
                    lean_dec(v_m_1736_);
                    v___x_1742_ = lean_box(0);
                    v_isShared_1743_ = v_isSharedCheck_1783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1744_ = lean_array_get_size(v_buckets_1740_);
                v___x_1745_ = l_Lean_instHashableMVarId_hash(v_a_1737_);
                v___x_1746_ = 32u64;
                v___x_1747_ = lean_uint64_shift_right(v___x_1745_, v___x_1746_);
                v_fold_1748_ = lean_uint64_xor(v___x_1745_, v___x_1747_);
                v___x_1749_ = 16u64;
                v___x_1750_ = lean_uint64_shift_right(v_fold_1748_, v___x_1749_);
                v___x_1751_ = lean_uint64_xor(v_fold_1748_, v___x_1750_);
                v___x_1752_ = lean_uint64_to_usize(v___x_1751_);
                v___x_1753_ = lean_usize_of_nat(v___x_1744_);
                v___x_1754_ = 1usize;
                v___x_1755_ = lean_usize_sub(v___x_1753_, v___x_1754_);
                v___x_1756_ = lean_usize_land(v___x_1752_, v___x_1755_);
                v_bkt_1757_ = lean_array_uget_borrowed(v_buckets_1740_, v___x_1756_);
                v___x_1758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_1737_, v_bkt_1757_);
                if v___x_1758_ == 0 {
                    v___x_1759_ = lean_unsigned_to_nat(1);
                    v_size_x27_1760_ = lean_nat_add(v_size_1739_, v___x_1759_);
                    lean_dec(v_size_1739_);
                    lean_inc(v_bkt_1757_);
                    v___x_1761_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1761_, 0, v_a_1737_);
                    lean_ctor_set(v___x_1761_, 1, v_b_1738_);
                    lean_ctor_set(v___x_1761_, 2, v_bkt_1757_);
                    v_buckets_x27_1762_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1761_);
                    v___x_1763_ = lean_unsigned_to_nat(4);
                    v___x_1764_ = lean_nat_mul(v_size_x27_1760_, v___x_1763_);
                    v___x_1765_ = lean_unsigned_to_nat(3);
                    v___x_1766_ = lean_nat_div(v___x_1764_, v___x_1765_);
                    lean_dec(v___x_1764_);
                    v___x_1767_ = lean_array_get_size(v_buckets_x27_1762_);
                    v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1767_);
                    lean_dec(v___x_1766_);
                    if v___x_1768_ == 0 {
                        v_val_1769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_1762_);
                        if v_isShared_1743_ == 0 {
                            lean_ctor_set(v___x_1742_, 1, v_val_1769_);
                            lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1771_ = v___x_1742_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_size_x27_1760_);
                            lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_val_1769_);
                            v___x_1771_ = v_reuseFailAlloc_1772_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1743_ == 0 {
                            lean_ctor_set(v___x_1742_, 1, v_buckets_x27_1762_);
                            lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1774_ = v___x_1742_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_size_x27_1760_);
                            lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_buckets_x27_1762_);
                            v___x_1774_ = v_reuseFailAlloc_1775_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1757_);
                    v___x_1776_ = lean_box(0);
                    v_buckets_x27_1777_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1776_);
                    v___x_1778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_1737_, v_b_1738_, v_bkt_1757_);
                    v___x_1779_ = lean_array_uset(v_buckets_x27_1777_, v___x_1756_, v___x_1778_);
                    if v_isShared_1743_ == 0 {
                        lean_ctor_set(v___x_1742_, 1, v___x_1779_);
                        v___x_1781_ = v___x_1742_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_size_1739_);
                        lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
                        v___x_1781_ = v_reuseFailAlloc_1782_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1771_;
            }
            3 => {
                return v___x_1774_;
            }
            4 => {
                return v___x_1781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(
    mut v_x_1784_: *mut LeanObject,
    mut v_x_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1784_) == 0 {
                    v___x_1787_ = l_List_reverse___redArg(v_x_1785_);
                    v___x_1788_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                    lean_ctor_set(v___x_1788_, 1, v___y_1786_);
                    return v___x_1788_;
                } else {
                    v_head_1789_ = lean_ctor_get(v_x_1784_, 0);
                    v_tail_1790_ = lean_ctor_get(v_x_1784_, 1);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1792_ = v_x_1784_;
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1790_);
                        lean_inc(v_head_1789_);
                        lean_dec(v_x_1784_);
                        v___x_1792_ = lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1794_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_1789_, v___y_1786_);
                v_fst_1795_ = lean_ctor_get(v___x_1794_, 0);
                lean_inc(v_fst_1795_);
                v_snd_1796_ = lean_ctor_get(v___x_1794_, 1);
                lean_inc(v_snd_1796_);
                lean_dec_ref(v___x_1794_);
                if v_isShared_1793_ == 0 {
                    lean_ctor_set(v___x_1792_, 1, v_x_1785_);
                    lean_ctor_set(v___x_1792_, 0, v_fst_1795_);
                    v___x_1798_ = v___x_1792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fst_1795_);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_x_1785_);
                    v___x_1798_ = v_reuseFailAlloc_1800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1784_ = v_tail_1790_;
                v_x_1785_ = v___x_1798_;
                v___y_1786_ = v_snd_1796_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_abstractExprMVars(
    mut v_e_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmap_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_emap_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1844_: u8 = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v_fvars_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_val_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_declName_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_fn_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___y_1917_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: usize = 0;
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: usize = 0;
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: u8 = 0;
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_binderName_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___y_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_binderName_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___y_1980_: u8 = 0;
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_declName_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_2004_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___y_2018_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: usize = 0;
    let mut v___x_2024_: usize = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_data_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: u8 = 0;
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_typeName_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: usize = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1807_ = l_Lean_Expr_hasMVar(v_e_1805_);
                if v___x_1807_ == 0 {
                    v___x_1808_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1808_, 0, v_e_1805_);
                    lean_ctor_set(v___x_1808_, 1, v_a_1806_);
                    return v___x_1808_;
                } else {
                    match lean_obj_tag(v_e_1805_) {
                        2 => {
                            v_mvarId_1809_ = lean_ctor_get(v_e_1805_, 0);
                            v_mctx_1810_ = lean_ctor_get(v_a_1806_, 2);
                            v_emap_1811_ = lean_ctor_get(v_a_1806_, 8);
                            lean_inc(v_mvarId_1809_);
                            v___x_1812_ =
                                l_Lean_MetavarContext_getDecl(v_mctx_1810_, v_mvarId_1809_);
                            v_userName_1813_ = lean_ctor_get(v___x_1812_, 0);
                            lean_inc(v_userName_1813_);
                            v_type_1814_ = lean_ctor_get(v___x_1812_, 2);
                            lean_inc_ref(v_type_1814_);
                            v_depth_1815_ = lean_ctor_get(v___x_1812_, 3);
                            lean_inc(v_depth_1815_);
                            lean_dec_ref(v___x_1812_);
                            v_depth_1816_ = lean_ctor_get(v_mctx_1810_, 0);
                            v___x_1817_ = lean_nat_dec_eq(v_depth_1815_, v_depth_1816_);
                            lean_dec(v_depth_1815_);
                            if v___x_1817_ == 0 {
                                lean_dec_ref(v_type_1814_);
                                lean_dec(v_userName_1813_);
                                v___x_1818_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1818_, 0, v_e_1805_);
                                lean_ctor_set(v___x_1818_, 1, v_a_1806_);
                                return v___x_1818_;
                            } else {
                                lean_inc(v_mvarId_1809_);
                                v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_1811_, v_mvarId_1809_);
                                if lean_obj_tag(v___x_1819_) == 0 {
                                    v___x_1820_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_1814_, v_a_1806_);
                                    v_fst_1821_ = lean_ctor_get(v___x_1820_, 0);
                                    lean_inc(v_fst_1821_);
                                    v_snd_1822_ = lean_ctor_get(v___x_1820_, 1);
                                    lean_inc(v_snd_1822_);
                                    lean_dec_ref(v___x_1820_);
                                    v___x_1823_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                        v_fst_1821_,
                                        v_snd_1822_,
                                    );
                                    v_fst_1824_ = lean_ctor_get(v___x_1823_, 0);
                                    lean_inc(v_fst_1824_);
                                    v_snd_1825_ = lean_ctor_get(v___x_1823_, 1);
                                    lean_inc(v_snd_1825_);
                                    lean_dec_ref(v___x_1823_);
                                    v___x_1826_ =
                                        l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_1825_);
                                    v_fst_1827_ = lean_ctor_get(v___x_1826_, 0);
                                    v_snd_1828_ = lean_ctor_get(v___x_1826_, 1);
                                    v_isSharedCheck_1866_ = (!lean_is_exclusive(v___x_1826_)) as u8;
                                    if v_isSharedCheck_1866_ == 0 {
                                        v___x_1830_ = v___x_1826_;
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_1828_);
                                        lean_inc(v_fst_1827_);
                                        lean_dec(v___x_1826_);
                                        v___x_1830_ = lean_box(0);
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_type_1814_);
                                    lean_dec(v_userName_1813_);
                                    lean_dec_ref_known(v_e_1805_, 1);
                                    lean_dec(v_mvarId_1809_);
                                    v_val_1867_ = lean_ctor_get(v___x_1819_, 0);
                                    lean_inc(v_val_1867_);
                                    lean_dec_ref_known(v___x_1819_, 1);
                                    v___x_1868_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_1868_, 0, v_val_1867_);
                                    lean_ctor_set(v___x_1868_, 1, v_a_1806_);
                                    return v___x_1868_;
                                }
                            }
                        }
                        3 => {
                            v_u_1869_ = lean_ctor_get(v_e_1805_, 0);
                            lean_inc(v_u_1869_);
                            v___x_1870_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_1869_, v_a_1806_);
                            v_fst_1871_ = lean_ctor_get(v___x_1870_, 0);
                            v_snd_1872_ = lean_ctor_get(v___x_1870_, 1);
                            v_isSharedCheck_1886_ = (!lean_is_exclusive(v___x_1870_)) as u8;
                            if v_isSharedCheck_1886_ == 0 {
                                v___x_1874_ = v___x_1870_;
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_snd_1872_);
                                lean_inc(v_fst_1871_);
                                lean_dec(v___x_1870_);
                                v___x_1874_ = lean_box(0);
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            }
                        }
                        4 => {
                            v_declName_1887_ = lean_ctor_get(v_e_1805_, 0);
                            v_us_1888_ = lean_ctor_get(v_e_1805_, 1);
                            v___x_1889_ = lean_box(0);
                            lean_inc(v_us_1888_);
                            v___x_1890_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_1888_, v___x_1889_, v_a_1806_);
                            v_fst_1891_ = lean_ctor_get(v___x_1890_, 0);
                            v_snd_1892_ = lean_ctor_get(v___x_1890_, 1);
                            v_isSharedCheck_1904_ = (!lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1904_ == 0 {
                                v___x_1894_ = v___x_1890_;
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_snd_1892_);
                                lean_inc(v_fst_1891_);
                                lean_dec(v___x_1890_);
                                v___x_1894_ = lean_box(0);
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_1905_ = lean_ctor_get(v_e_1805_, 0);
                            v_arg_1906_ = lean_ctor_get(v_e_1805_, 1);
                            lean_inc_ref(v_fn_1905_);
                            v___x_1907_ =
                                l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_1905_, v_a_1806_);
                            v_fst_1908_ = lean_ctor_get(v___x_1907_, 0);
                            lean_inc(v_fst_1908_);
                            v_snd_1909_ = lean_ctor_get(v___x_1907_, 1);
                            lean_inc(v_snd_1909_);
                            lean_dec_ref(v___x_1907_);
                            lean_inc_ref(v_arg_1906_);
                            v___x_1910_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_arg_1906_,
                                v_snd_1909_,
                            );
                            v_fst_1911_ = lean_ctor_get(v___x_1910_, 0);
                            v_snd_1912_ = lean_ctor_get(v___x_1910_, 1);
                            v_isSharedCheck_1931_ = (!lean_is_exclusive(v___x_1910_)) as u8;
                            if v_isSharedCheck_1931_ == 0 {
                                v___x_1914_ = v___x_1910_;
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_snd_1912_);
                                lean_inc(v_fst_1911_);
                                lean_dec(v___x_1910_);
                                v___x_1914_ = lean_box(0);
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_1932_ = lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1933_ = lean_ctor_get(v_e_1805_, 1);
                            v_body_1934_ = lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1935_ = lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_1933_);
                            v___x_1936_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1933_,
                                v_a_1806_,
                            );
                            v_fst_1937_ = lean_ctor_get(v___x_1936_, 0);
                            lean_inc(v_fst_1937_);
                            v_snd_1938_ = lean_ctor_get(v___x_1936_, 1);
                            lean_inc(v_snd_1938_);
                            lean_dec_ref(v___x_1936_);
                            lean_inc_ref(v_body_1934_);
                            v___x_1939_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1934_,
                                v_snd_1938_,
                            );
                            v_fst_1940_ = lean_ctor_get(v___x_1939_, 0);
                            v_snd_1941_ = lean_ctor_get(v___x_1939_, 1);
                            v_isSharedCheck_1965_ = (!lean_is_exclusive(v___x_1939_)) as u8;
                            if v_isSharedCheck_1965_ == 0 {
                                v___x_1943_ = v___x_1939_;
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_snd_1941_);
                                lean_inc(v_fst_1940_);
                                lean_dec(v___x_1939_);
                                v___x_1943_ = lean_box(0);
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            }
                        }
                        7 => {
                            v_binderName_1966_ = lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1967_ = lean_ctor_get(v_e_1805_, 1);
                            v_body_1968_ = lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1969_ = lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_1967_);
                            v___x_1970_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1967_,
                                v_a_1806_,
                            );
                            v_fst_1971_ = lean_ctor_get(v___x_1970_, 0);
                            lean_inc(v_fst_1971_);
                            v_snd_1972_ = lean_ctor_get(v___x_1970_, 1);
                            lean_inc(v_snd_1972_);
                            lean_dec_ref(v___x_1970_);
                            lean_inc_ref(v_body_1968_);
                            v___x_1973_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1968_,
                                v_snd_1972_,
                            );
                            v_fst_1974_ = lean_ctor_get(v___x_1973_, 0);
                            v_snd_1975_ = lean_ctor_get(v___x_1973_, 1);
                            v_isSharedCheck_1999_ = (!lean_is_exclusive(v___x_1973_)) as u8;
                            if v_isSharedCheck_1999_ == 0 {
                                v___x_1977_ = v___x_1973_;
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_snd_1975_);
                                lean_inc(v_fst_1974_);
                                lean_dec(v___x_1973_);
                                v___x_1977_ = lean_box(0);
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            }
                        }
                        8 => {
                            v_declName_2000_ = lean_ctor_get(v_e_1805_, 0);
                            v_type_2001_ = lean_ctor_get(v_e_1805_, 1);
                            v_value_2002_ = lean_ctor_get(v_e_1805_, 2);
                            v_body_2003_ = lean_ctor_get(v_e_1805_, 3);
                            v_nondep_2004_ = lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                            );
                            lean_inc_ref(v_type_2001_);
                            v___x_2005_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_type_2001_,
                                v_a_1806_,
                            );
                            v_fst_2006_ = lean_ctor_get(v___x_2005_, 0);
                            lean_inc(v_fst_2006_);
                            v_snd_2007_ = lean_ctor_get(v___x_2005_, 1);
                            lean_inc(v_snd_2007_);
                            lean_dec_ref(v___x_2005_);
                            lean_inc_ref(v_value_2002_);
                            v___x_2008_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_value_2002_,
                                v_snd_2007_,
                            );
                            v_fst_2009_ = lean_ctor_get(v___x_2008_, 0);
                            lean_inc(v_fst_2009_);
                            v_snd_2010_ = lean_ctor_get(v___x_2008_, 1);
                            lean_inc(v_snd_2010_);
                            lean_dec_ref(v___x_2008_);
                            lean_inc_ref(v_body_2003_);
                            v___x_2011_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_2003_,
                                v_snd_2010_,
                            );
                            v_fst_2012_ = lean_ctor_get(v___x_2011_, 0);
                            v_snd_2013_ = lean_ctor_get(v___x_2011_, 1);
                            v_isSharedCheck_2039_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                            if v_isSharedCheck_2039_ == 0 {
                                v___x_2015_ = v___x_2011_;
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_snd_2013_);
                                lean_inc(v_fst_2012_);
                                lean_dec(v___x_2011_);
                                v___x_2015_ = lean_box(0);
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            }
                        }
                        10 => {
                            v_data_2040_ = lean_ctor_get(v_e_1805_, 0);
                            v_expr_2041_ = lean_ctor_get(v_e_1805_, 1);
                            lean_inc_ref(v_expr_2041_);
                            v___x_2042_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_expr_2041_,
                                v_a_1806_,
                            );
                            v_fst_2043_ = lean_ctor_get(v___x_2042_, 0);
                            v_snd_2044_ = lean_ctor_get(v___x_2042_, 1);
                            v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_2042_)) as u8;
                            if v_isSharedCheck_2058_ == 0 {
                                v___x_2046_ = v___x_2042_;
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_snd_2044_);
                                lean_inc(v_fst_2043_);
                                lean_dec(v___x_2042_);
                                v___x_2046_ = lean_box(0);
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_2059_ = lean_ctor_get(v_e_1805_, 0);
                            v_idx_2060_ = lean_ctor_get(v_e_1805_, 1);
                            v_struct_2061_ = lean_ctor_get(v_e_1805_, 2);
                            lean_inc_ref(v_struct_2061_);
                            v___x_2062_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_struct_2061_,
                                v_a_1806_,
                            );
                            v_fst_2063_ = lean_ctor_get(v___x_2062_, 0);
                            v_snd_2064_ = lean_ctor_get(v___x_2062_, 1);
                            v_isSharedCheck_2078_ = (!lean_is_exclusive(v___x_2062_)) as u8;
                            if v_isSharedCheck_2078_ == 0 {
                                v___x_2066_ = v___x_2062_;
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_snd_2064_);
                                lean_inc(v_fst_2063_);
                                lean_dec(v___x_2062_);
                                v___x_2066_ = lean_box(0);
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            }
                        }
                        _ => {
                            v___x_2079_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2079_, 0, v_e_1805_);
                            lean_ctor_set(v___x_2079_, 1, v_a_1806_);
                            return v___x_2079_;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_fst_1827_);
                v___x_1832_ = l_Lean_mkFVar(v_fst_1827_);
                v___x_1861_ = l_Lean_Name_isAnonymous(v_userName_1813_);
                if v___x_1861_ == 0 {
                    v_userName_1834_ = v_userName_1813_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_userName_1813_);
                    v_fvars_1862_ = lean_ctor_get(v_snd_1828_, 5);
                    v___x_1863_ = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
                    v___x_1864_ = lean_array_get_size(v_fvars_1862_);
                    v___x_1865_ = lean_name_append_index_after(v___x_1863_, v___x_1864_);
                    v_userName_1834_ = v___x_1865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ngen_1835_ = lean_ctor_get(v_snd_1828_, 0);
                v_lctx_1836_ = lean_ctor_get(v_snd_1828_, 1);
                v_mctx_1837_ = lean_ctor_get(v_snd_1828_, 2);
                v_nextParamIdx_1838_ = lean_ctor_get(v_snd_1828_, 3);
                v_paramNames_1839_ = lean_ctor_get(v_snd_1828_, 4);
                v_fvars_1840_ = lean_ctor_get(v_snd_1828_, 5);
                v_mvars_1841_ = lean_ctor_get(v_snd_1828_, 6);
                v_lmap_1842_ = lean_ctor_get(v_snd_1828_, 7);
                v_emap_1843_ = lean_ctor_get(v_snd_1828_, 8);
                v_abstractLevels_1844_ = lean_ctor_get_uint8(
                    v_snd_1828_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1860_ = (!lean_is_exclusive(v_snd_1828_)) as u8;
                if v_isSharedCheck_1860_ == 0 {
                    v___x_1846_ = v_snd_1828_;
                    v_isShared_1847_ = v_isSharedCheck_1860_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_emap_1843_);
                    lean_inc(v_lmap_1842_);
                    lean_inc(v_mvars_1841_);
                    lean_inc(v_fvars_1840_);
                    lean_inc(v_paramNames_1839_);
                    lean_inc(v_nextParamIdx_1838_);
                    lean_inc(v_mctx_1837_);
                    lean_inc(v_lctx_1836_);
                    lean_inc(v_ngen_1835_);
                    lean_dec(v_snd_1828_);
                    v___x_1846_ = lean_box(0);
                    v_isShared_1847_ = v_isSharedCheck_1860_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1848_ = 0;
                v___x_1849_ = 0;
                v___x_1850_ = l_Lean_LocalContext_mkLocalDecl(
                    v_lctx_1836_,
                    v_fst_1827_,
                    v_userName_1834_,
                    v_fst_1824_,
                    v___x_1848_,
                    v___x_1849_,
                );
                lean_inc_ref_n(v___x_1832_, 2);
                v___x_1851_ = lean_array_push(v_fvars_1840_, v___x_1832_);
                v___x_1852_ = lean_array_push(v_mvars_1841_, v_e_1805_);
                v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_1843_, v_mvarId_1809_, v___x_1832_);
                if v_isShared_1847_ == 0 {
                    lean_ctor_set(v___x_1846_, 8, v___x_1853_);
                    lean_ctor_set(v___x_1846_, 6, v___x_1852_);
                    lean_ctor_set(v___x_1846_, 5, v___x_1851_);
                    lean_ctor_set(v___x_1846_, 1, v___x_1850_);
                    v___x_1855_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_ngen_1835_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1850_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_mctx_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_nextParamIdx_1838_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_paramNames_1839_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 5, v___x_1851_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 6, v___x_1852_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_lmap_1842_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 8, v___x_1853_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1859_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_abstractLevels_1844_,
                    );
                    v___x_1855_ = v_reuseFailAlloc_1859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1831_ == 0 {
                    lean_ctor_set(v___x_1830_, 1, v___x_1855_);
                    lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1857_ = v___x_1830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1832_);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
                    v___x_1857_ = v_reuseFailAlloc_1858_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1857_;
            }
            6 => {
                v___x_1876_ = lean_ptr_addr(v_u_1869_);
                v___x_1877_ = lean_ptr_addr(v_fst_1871_);
                v___x_1878_ = lean_usize_dec_eq(v___x_1876_, v___x_1877_);
                if v___x_1878_ == 0 {
                    lean_dec_ref_known(v_e_1805_, 1);
                    v___x_1879_ = l_Lean_Expr_sort___override(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        lean_ctor_set(v___x_1874_, 0, v___x_1879_);
                        v___x_1881_ = v___x_1874_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
                        lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_snd_1872_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        lean_ctor_set(v___x_1874_, 0, v_e_1805_);
                        v___x_1884_ = v___x_1874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_e_1805_);
                        lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1872_);
                        v___x_1884_ = v_reuseFailAlloc_1885_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1881_;
            }
            8 => {
                return v___x_1884_;
            }
            9 => {
                v___x_1896_ = l_ptrEqList___redArg(v_us_1888_, v_fst_1891_);
                if v___x_1896_ == 0 {
                    lean_inc(v_declName_1887_);
                    lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1897_ = l_Lean_Expr_const___override(v_declName_1887_, v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        lean_ctor_set(v___x_1894_, 0, v___x_1897_);
                        v___x_1899_ = v___x_1894_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                        lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1892_);
                        v___x_1899_ = v_reuseFailAlloc_1900_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        lean_ctor_set(v___x_1894_, 0, v_e_1805_);
                        v___x_1902_ = v___x_1894_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_e_1805_);
                        lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_snd_1892_);
                        v___x_1902_ = v_reuseFailAlloc_1903_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1899_;
            }
            11 => {
                return v___x_1902_;
            }
            12 => {
                v___x_1925_ = lean_ptr_addr(v_fn_1905_);
                v___x_1926_ = lean_ptr_addr(v_fst_1908_);
                v___x_1927_ = lean_usize_dec_eq(v___x_1925_, v___x_1926_);
                if v___x_1927_ == 0 {
                    v___y_1917_ = v___x_1927_;
                    state = 13;
                    continue;
                } else {
                    v___x_1928_ = lean_ptr_addr(v_arg_1906_);
                    v___x_1929_ = lean_ptr_addr(v_fst_1911_);
                    v___x_1930_ = lean_usize_dec_eq(v___x_1928_, v___x_1929_);
                    v___y_1917_ = v___x_1930_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_1917_ == 0 {
                    lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1918_ = l_Lean_Expr_app___override(v_fst_1908_, v_fst_1911_);
                    if v_isShared_1915_ == 0 {
                        lean_ctor_set(v___x_1914_, 0, v___x_1918_);
                        v___x_1920_ = v___x_1914_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                        lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_snd_1912_);
                        v___x_1920_ = v_reuseFailAlloc_1921_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1911_);
                    lean_dec(v_fst_1908_);
                    if v_isShared_1915_ == 0 {
                        lean_ctor_set(v___x_1914_, 0, v_e_1805_);
                        v___x_1923_ = v___x_1914_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_e_1805_);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_snd_1912_);
                        v___x_1923_ = v_reuseFailAlloc_1924_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_1920_;
            }
            15 => {
                return v___x_1923_;
            }
            16 => {
                v___x_1959_ = lean_ptr_addr(v_binderType_1933_);
                v___x_1960_ = lean_ptr_addr(v_fst_1937_);
                v___x_1961_ = lean_usize_dec_eq(v___x_1959_, v___x_1960_);
                if v___x_1961_ == 0 {
                    v___y_1946_ = v___x_1961_;
                    state = 17;
                    continue;
                } else {
                    v___x_1962_ = lean_ptr_addr(v_body_1934_);
                    v___x_1963_ = lean_ptr_addr(v_fst_1940_);
                    v___x_1964_ = lean_usize_dec_eq(v___x_1962_, v___x_1963_);
                    v___y_1946_ = v___x_1964_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_1946_ == 0 {
                    lean_inc(v_binderName_1932_);
                    lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1947_ = l_Lean_Expr_lam___override(
                        v_binderName_1932_,
                        v_fst_1937_,
                        v_fst_1940_,
                        v_binderInfo_1935_,
                    );
                    if v_isShared_1944_ == 0 {
                        lean_ctor_set(v___x_1943_, 0, v___x_1947_);
                        v___x_1949_ = v___x_1943_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
                        lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_snd_1941_);
                        v___x_1949_ = v_reuseFailAlloc_1950_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_1951_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1935_, v_binderInfo_1935_);
                    if v___x_1951_ == 0 {
                        lean_inc(v_binderName_1932_);
                        lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1952_ = l_Lean_Expr_lam___override(
                            v_binderName_1932_,
                            v_fst_1937_,
                            v_fst_1940_,
                            v_binderInfo_1935_,
                        );
                        if v_isShared_1944_ == 0 {
                            lean_ctor_set(v___x_1943_, 0, v___x_1952_);
                            v___x_1954_ = v___x_1943_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                            lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_snd_1941_);
                            v___x_1954_ = v_reuseFailAlloc_1955_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_1940_);
                        lean_dec(v_fst_1937_);
                        if v_isShared_1944_ == 0 {
                            lean_ctor_set(v___x_1943_, 0, v_e_1805_);
                            v___x_1957_ = v___x_1943_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_e_1805_);
                            lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1941_);
                            v___x_1957_ = v_reuseFailAlloc_1958_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                return v___x_1949_;
            }
            19 => {
                return v___x_1954_;
            }
            20 => {
                return v___x_1957_;
            }
            21 => {
                v___x_1993_ = lean_ptr_addr(v_binderType_1967_);
                v___x_1994_ = lean_ptr_addr(v_fst_1971_);
                v___x_1995_ = lean_usize_dec_eq(v___x_1993_, v___x_1994_);
                if v___x_1995_ == 0 {
                    v___y_1980_ = v___x_1995_;
                    state = 22;
                    continue;
                } else {
                    v___x_1996_ = lean_ptr_addr(v_body_1968_);
                    v___x_1997_ = lean_ptr_addr(v_fst_1974_);
                    v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
                    v___y_1980_ = v___x_1998_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_1980_ == 0 {
                    lean_inc(v_binderName_1966_);
                    lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1981_ = l_Lean_Expr_forallE___override(
                        v_binderName_1966_,
                        v_fst_1971_,
                        v_fst_1974_,
                        v_binderInfo_1969_,
                    );
                    if v_isShared_1978_ == 0 {
                        lean_ctor_set(v___x_1977_, 0, v___x_1981_);
                        v___x_1983_ = v___x_1977_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
                        lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_snd_1975_);
                        v___x_1983_ = v_reuseFailAlloc_1984_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___x_1985_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1969_, v_binderInfo_1969_);
                    if v___x_1985_ == 0 {
                        lean_inc(v_binderName_1966_);
                        lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1986_ = l_Lean_Expr_forallE___override(
                            v_binderName_1966_,
                            v_fst_1971_,
                            v_fst_1974_,
                            v_binderInfo_1969_,
                        );
                        if v_isShared_1978_ == 0 {
                            lean_ctor_set(v___x_1977_, 0, v___x_1986_);
                            v___x_1988_ = v___x_1977_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
                            lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_snd_1975_);
                            v___x_1988_ = v_reuseFailAlloc_1989_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_1974_);
                        lean_dec(v_fst_1971_);
                        if v_isShared_1978_ == 0 {
                            lean_ctor_set(v___x_1977_, 0, v_e_1805_);
                            v___x_1991_ = v___x_1977_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_e_1805_);
                            lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1975_);
                            v___x_1991_ = v_reuseFailAlloc_1992_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            23 => {
                return v___x_1983_;
            }
            24 => {
                return v___x_1988_;
            }
            25 => {
                return v___x_1991_;
            }
            26 => {
                v___x_2033_ = lean_ptr_addr(v_type_2001_);
                v___x_2034_ = lean_ptr_addr(v_fst_2006_);
                v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
                if v___x_2035_ == 0 {
                    v___y_2018_ = v___x_2035_;
                    state = 27;
                    continue;
                } else {
                    v___x_2036_ = lean_ptr_addr(v_value_2002_);
                    v___x_2037_ = lean_ptr_addr(v_fst_2009_);
                    v___x_2038_ = lean_usize_dec_eq(v___x_2036_, v___x_2037_);
                    v___y_2018_ = v___x_2038_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v___y_2018_ == 0 {
                    lean_inc(v_declName_2000_);
                    lean_dec_ref_known(v_e_1805_, 4);
                    v___x_2019_ = l_Lean_Expr_letE___override(
                        v_declName_2000_,
                        v_fst_2006_,
                        v_fst_2009_,
                        v_fst_2012_,
                        v_nondep_2004_,
                    );
                    if v_isShared_2016_ == 0 {
                        lean_ctor_set(v___x_2015_, 0, v___x_2019_);
                        v___x_2021_ = v___x_2015_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
                        lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2013_);
                        v___x_2021_ = v_reuseFailAlloc_2022_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___x_2023_ = lean_ptr_addr(v_body_2003_);
                    v___x_2024_ = lean_ptr_addr(v_fst_2012_);
                    v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
                    if v___x_2025_ == 0 {
                        lean_inc(v_declName_2000_);
                        lean_dec_ref_known(v_e_1805_, 4);
                        v___x_2026_ = l_Lean_Expr_letE___override(
                            v_declName_2000_,
                            v_fst_2006_,
                            v_fst_2009_,
                            v_fst_2012_,
                            v_nondep_2004_,
                        );
                        if v_isShared_2016_ == 0 {
                            lean_ctor_set(v___x_2015_, 0, v___x_2026_);
                            v___x_2028_ = v___x_2015_;
                            state = 29;
                            continue;
                        } else {
                            v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                            lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_snd_2013_);
                            v___x_2028_ = v_reuseFailAlloc_2029_;
                            state = 29;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_2012_);
                        lean_dec(v_fst_2009_);
                        lean_dec(v_fst_2006_);
                        if v_isShared_2016_ == 0 {
                            lean_ctor_set(v___x_2015_, 0, v_e_1805_);
                            v___x_2031_ = v___x_2015_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_e_1805_);
                            lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2013_);
                            v___x_2031_ = v_reuseFailAlloc_2032_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            28 => {
                return v___x_2021_;
            }
            29 => {
                return v___x_2028_;
            }
            30 => {
                return v___x_2031_;
            }
            31 => {
                v___x_2048_ = lean_ptr_addr(v_expr_2041_);
                v___x_2049_ = lean_ptr_addr(v_fst_2043_);
                v___x_2050_ = lean_usize_dec_eq(v___x_2048_, v___x_2049_);
                if v___x_2050_ == 0 {
                    lean_inc(v_data_2040_);
                    lean_dec_ref_known(v_e_1805_, 2);
                    v___x_2051_ = l_Lean_Expr_mdata___override(v_data_2040_, v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        lean_ctor_set(v___x_2046_, 0, v___x_2051_);
                        v___x_2053_ = v___x_2046_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
                        lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_snd_2044_);
                        v___x_2053_ = v_reuseFailAlloc_2054_;
                        state = 32;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        lean_ctor_set(v___x_2046_, 0, v_e_1805_);
                        v___x_2056_ = v___x_2046_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_e_1805_);
                        lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2044_);
                        v___x_2056_ = v_reuseFailAlloc_2057_;
                        state = 33;
                        continue;
                    }
                }
            }
            32 => {
                return v___x_2053_;
            }
            33 => {
                return v___x_2056_;
            }
            34 => {
                v___x_2068_ = lean_ptr_addr(v_struct_2061_);
                v___x_2069_ = lean_ptr_addr(v_fst_2063_);
                v___x_2070_ = lean_usize_dec_eq(v___x_2068_, v___x_2069_);
                if v___x_2070_ == 0 {
                    lean_inc(v_idx_2060_);
                    lean_inc(v_typeName_2059_);
                    lean_dec_ref_known(v_e_1805_, 3);
                    v___x_2071_ =
                        l_Lean_Expr_proj___override(v_typeName_2059_, v_idx_2060_, v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        lean_ctor_set(v___x_2066_, 0, v___x_2071_);
                        v___x_2073_ = v___x_2066_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                        lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_snd_2064_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        lean_ctor_set(v___x_2066_, 0, v_e_1805_);
                        v___x_2076_ = v___x_2066_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_e_1805_);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_snd_2064_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 36;
                        continue;
                    }
                }
            }
            35 => {
                return v___x_2073_;
            }
            36 => {
                return v___x_2076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(
    mut v_00_u03b2_2080_: *mut LeanObject,
    mut v_m_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_2081_, v_a_2082_);
    return v___x_2083_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(
    mut v_00_u03b2_2084_: *mut LeanObject,
    mut v_m_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_2084_, v_m_2085_, v_a_2086_);
    lean_dec(v_a_2086_);
    lean_dec_ref(v_m_2085_);
    return v_res_2087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(
    mut v_00_u03b2_2088_: *mut LeanObject,
    mut v_m_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_b_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_2089_, v_a_2090_, v_b_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(
    mut v_00_u03b2_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_x_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_2094_, v_x_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_x_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
    lean_dec(v_x_2099_);
    lean_dec(v_a_2098_);
    return v_res_2100_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(
    mut v_00_u03b2_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_x_2103_: *mut LeanObject,
) -> u8 {
    let mut v___x_2104_: u8 = 0;
    v___x_2104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_2102_, v_x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(
    mut v_00_u03b2_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: u8 = 0;
    let mut v_r_2109_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_2105_, v_a_2106_, v_x_2107_);
    lean_dec(v_x_2107_);
    lean_dec(v_a_2106_);
    v_r_2109_ = lean_box((v_res_2108_) as usize);
    return v_r_2109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(
    mut v_00_u03b2_2110_: *mut LeanObject,
    mut v_data_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(
    mut v_00_u03b2_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
    mut v_b_2115_: *mut LeanObject,
    mut v_x_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_2114_, v_b_2115_, v_x_2116_);
    return v___x_2117_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2118_: *mut LeanObject,
    mut v_i_2119_: *mut LeanObject,
    mut v_source_2120_: *mut LeanObject,
    mut v_target_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_2119_, v_source_2120_, v_target_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_2123_: *mut LeanObject,
    mut v_x_2124_: *mut LeanObject,
    mut v_x_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_2124_, v_x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
    mut v_e_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_unused_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = l_Lean_Expr_hasMVar(v_e_2127_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2131_, 0, v_e_2127_);
                    return v___x_2131_;
                } else {
                    v___x_2132_ = lean_st_ref_get(v___y_2128_);
                    v_mctx_2133_ = lean_ctor_get(v___x_2132_, 0);
                    lean_inc_ref(v_mctx_2133_);
                    lean_dec(v___x_2132_);
                    v___x_2134_ = l_Lean_instantiateMVarsCore(v_mctx_2133_, v_e_2127_);
                    v_fst_2135_ = lean_ctor_get(v___x_2134_, 0);
                    lean_inc(v_fst_2135_);
                    v_snd_2136_ = lean_ctor_get(v___x_2134_, 1);
                    lean_inc(v_snd_2136_);
                    lean_dec_ref(v___x_2134_);
                    v___x_2137_ = lean_st_ref_take(v___y_2128_);
                    v_cache_2138_ = lean_ctor_get(v___x_2137_, 1);
                    v_zetaDeltaFVarIds_2139_ = lean_ctor_get(v___x_2137_, 2);
                    v_postponed_2140_ = lean_ctor_get(v___x_2137_, 3);
                    v_diag_2141_ = lean_ctor_get(v___x_2137_, 4);
                    v_isSharedCheck_2150_ = (!lean_is_exclusive(v___x_2137_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v_unused_2151_ = lean_ctor_get(v___x_2137_, 0);
                        lean_dec(v_unused_2151_);
                        v___x_2143_ = v___x_2137_;
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2141_);
                        lean_inc(v_postponed_2140_);
                        lean_inc(v_zetaDeltaFVarIds_2139_);
                        lean_inc(v_cache_2138_);
                        lean_dec(v___x_2137_);
                        v___x_2143_ = lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2144_ == 0 {
                    lean_ctor_set(v___x_2143_, 0, v_snd_2136_);
                    v___x_2146_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2136_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_cache_2138_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_zetaDeltaFVarIds_2139_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_postponed_2140_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_diag_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2147_ = lean_st_ref_set(v___y_2128_, v___x_2146_);
                v___x_2148_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2148_, 0, v_fst_2135_);
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(
    mut v_e_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2155_: *mut LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2152_,
        v___y_2153_,
    );
    lean_dec(v___y_2153_);
    return v_res_2155_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
    mut v_e_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2156_,
        v___y_2158_,
    );
    return v___x_2162_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(
    mut v_e_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2169_: *mut LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
        v_e_2163_,
        v___y_2164_,
        v___y_2165_,
        v___y_2166_,
        v___y_2167_,
    );
    lean_dec(v___y_2167_);
    lean_dec_ref(v___y_2166_);
    lean_dec(v___y_2165_);
    lean_dec_ref(v___y_2164_);
    return v_res_2169_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__1() -> *mut LeanObject {
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    v___x_2172_ = lean_box(0);
    v___x_2173_ = lean_unsigned_to_nat(16);
    v___x_2174_ = lean_mk_array(v___x_2173_, v___x_2172_);
    return v___x_2174_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__2() -> *mut LeanObject {
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    v___x_2175_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1_once),
        _init_l_Lean_Meta_abstractMVars___closed__1,
    );
    v___x_2176_ = lean_unsigned_to_nat(0);
    v___x_2177_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    lean_ctor_set(v___x_2177_, 1, v___x_2175_);
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_abstractMVars(
    mut v_e_2178_: *mut LeanObject,
    mut v_levels_2179_: u8,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvars_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_unused_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2185_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
                        v_e_2178_, v_a_2181_,
                    );
                v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
                v_isSharedCheck_2247_ = (!lean_is_exclusive(v___x_2185_)) as u8;
                if v_isSharedCheck_2247_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2186_);
                    lean_dec(v___x_2185_);
                    v___x_2188_ = lean_box(0);
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2190_ = lean_st_ref_get(v_a_2181_);
                v___x_2191_ = lean_st_ref_get(v_a_2183_);
                v_mctx_2192_ = lean_ctor_get(v___x_2190_, 0);
                lean_inc_ref(v_mctx_2192_);
                lean_dec(v___x_2190_);
                v_lctx_2193_ = lean_ctor_get(v_a_2180_, 2);
                v_ngen_2194_ = lean_ctor_get(v___x_2191_, 2);
                lean_inc_ref(v_ngen_2194_);
                lean_dec(v___x_2191_);
                v___x_2195_ = lean_unsigned_to_nat(0);
                v___x_2196_ = l_Lean_Meta_abstractMVars___closed__0;
                v___x_2197_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2_once),
                    _init_l_Lean_Meta_abstractMVars___closed__2,
                );
                lean_inc_ref(v_lctx_2193_);
                v___x_2198_ = lean_alloc_ctor(0, 9, (1) as u32);
                lean_ctor_set(v___x_2198_, 0, v_ngen_2194_);
                lean_ctor_set(v___x_2198_, 1, v_lctx_2193_);
                lean_ctor_set(v___x_2198_, 2, v_mctx_2192_);
                lean_ctor_set(v___x_2198_, 3, v___x_2195_);
                lean_ctor_set(v___x_2198_, 4, v___x_2196_);
                lean_ctor_set(v___x_2198_, 5, v___x_2196_);
                lean_ctor_set(v___x_2198_, 6, v___x_2196_);
                lean_ctor_set(v___x_2198_, 7, v___x_2197_);
                lean_ctor_set(v___x_2198_, 8, v___x_2197_);
                lean_ctor_set_uint8(
                    v___x_2198_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    v_levels_2179_,
                );
                v___x_2199_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_2186_, v___x_2198_);
                v_fst_2200_ = lean_ctor_get(v___x_2199_, 0);
                lean_inc(v_fst_2200_);
                v_snd_2201_ = lean_ctor_get(v___x_2199_, 1);
                lean_inc(v_snd_2201_);
                lean_dec_ref(v___x_2199_);
                v___x_2202_ = lean_st_ref_take(v_a_2183_);
                v_ngen_2203_ = lean_ctor_get(v_snd_2201_, 0);
                lean_inc_ref(v_ngen_2203_);
                v_lctx_2204_ = lean_ctor_get(v_snd_2201_, 1);
                lean_inc_ref(v_lctx_2204_);
                v_mctx_2205_ = lean_ctor_get(v_snd_2201_, 2);
                lean_inc_ref(v_mctx_2205_);
                v_paramNames_2206_ = lean_ctor_get(v_snd_2201_, 4);
                lean_inc_ref(v_paramNames_2206_);
                v_fvars_2207_ = lean_ctor_get(v_snd_2201_, 5);
                lean_inc_ref(v_fvars_2207_);
                v_mvars_2208_ = lean_ctor_get(v_snd_2201_, 6);
                lean_inc_ref(v_mvars_2208_);
                lean_dec(v_snd_2201_);
                v_env_2209_ = lean_ctor_get(v___x_2202_, 0);
                v_nextMacroScope_2210_ = lean_ctor_get(v___x_2202_, 1);
                v_auxDeclNGen_2211_ = lean_ctor_get(v___x_2202_, 3);
                v_traceState_2212_ = lean_ctor_get(v___x_2202_, 4);
                v_cache_2213_ = lean_ctor_get(v___x_2202_, 5);
                v_messages_2214_ = lean_ctor_get(v___x_2202_, 6);
                v_infoState_2215_ = lean_ctor_get(v___x_2202_, 7);
                v_snapshotTasks_2216_ = lean_ctor_get(v___x_2202_, 8);
                v_isSharedCheck_2245_ = (!lean_is_exclusive(v___x_2202_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v_unused_2246_ = lean_ctor_get(v___x_2202_, 2);
                    lean_dec(v_unused_2246_);
                    v___x_2218_ = v___x_2202_;
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2216_);
                    lean_inc(v_infoState_2215_);
                    lean_inc(v_messages_2214_);
                    lean_inc(v_cache_2213_);
                    lean_inc(v_traceState_2212_);
                    lean_inc(v_auxDeclNGen_2211_);
                    lean_inc(v_nextMacroScope_2210_);
                    lean_inc(v_env_2209_);
                    lean_dec(v___x_2202_);
                    v___x_2218_ = lean_box(0);
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2219_ == 0 {
                    lean_ctor_set(v___x_2218_, 2, v_ngen_2203_);
                    v___x_2221_ = v___x_2218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_env_2209_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_nextMacroScope_2210_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_ngen_2203_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_auxDeclNGen_2211_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_traceState_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 5, v_cache_2213_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 6, v_messages_2214_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 7, v_infoState_2215_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 8, v_snapshotTasks_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2222_ = lean_st_ref_set(v_a_2183_, v___x_2221_);
                v___x_2223_ = lean_st_ref_take(v_a_2181_);
                v_cache_2224_ = lean_ctor_get(v___x_2223_, 1);
                v_zetaDeltaFVarIds_2225_ = lean_ctor_get(v___x_2223_, 2);
                v_postponed_2226_ = lean_ctor_get(v___x_2223_, 3);
                v_diag_2227_ = lean_ctor_get(v___x_2223_, 4);
                v_isSharedCheck_2242_ = (!lean_is_exclusive(v___x_2223_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v_unused_2243_ = lean_ctor_get(v___x_2223_, 0);
                    lean_dec(v_unused_2243_);
                    v___x_2229_ = v___x_2223_;
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_2227_);
                    lean_inc(v_postponed_2226_);
                    lean_inc(v_zetaDeltaFVarIds_2225_);
                    lean_inc(v_cache_2224_);
                    lean_dec(v___x_2223_);
                    v___x_2229_ = lean_box(0);
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2230_ == 0 {
                    lean_ctor_set(v___x_2229_, 0, v_mctx_2205_);
                    v___x_2232_ = v___x_2229_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_mctx_2205_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_cache_2224_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_zetaDeltaFVarIds_2225_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_postponed_2226_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_diag_2227_);
                    v___x_2232_ = v_reuseFailAlloc_2241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2233_ = lean_st_ref_set(v_a_2181_, v___x_2232_);
                v___x_2234_ = 1;
                v___x_2235_ = 0;
                v___x_2236_ = l_Lean_LocalContext_mkLambda(
                    v_lctx_2204_,
                    v_fvars_2207_,
                    v_fst_2200_,
                    v___x_2234_,
                    v___x_2235_,
                );
                lean_dec(v_fst_2200_);
                lean_dec_ref(v_fvars_2207_);
                v___x_2237_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2237_, 0, v_paramNames_2206_);
                lean_ctor_set(v___x_2237_, 1, v_mvars_2208_);
                lean_ctor_set(v___x_2237_, 2, v___x_2236_);
                if v_isShared_2189_ == 0 {
                    lean_ctor_set(v___x_2188_, 0, v___x_2237_);
                    v___x_2239_ = v___x_2188_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_abstractMVars___boxed(
    mut v_e_2248_: *mut LeanObject,
    mut v_levels_2249_: *mut LeanObject,
    mut v_a_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levels_boxed_2255_: u8 = 0;
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_levels_boxed_2255_ = (lean_unbox(v_levels_2249_) as u8);
    v_res_2256_ = l_Lean_Meta_abstractMVars(
        v_e_2248_,
        v_levels_boxed_2255_,
        v_a_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
    );
    lean_dec(v_a_2253_);
    lean_dec_ref(v_a_2252_);
    lean_dec(v_a_2251_);
    lean_dec_ref(v_a_2250_);
    return v_res_2256_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_bs_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2265_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2265_ == 0 {
                    v___x_2266_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2266_, 0, v_bs_2259_);
                    return v___x_2266_;
                } else {
                    v___x_2267_ = l_Lean_Meta_mkFreshLevelMVar(
                        v___y_2260_,
                        v___y_2261_,
                        v___y_2262_,
                        v___y_2263_,
                    );
                    if lean_obj_tag(v___x_2267_) == 0 {
                        v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
                        lean_inc(v_a_2268_);
                        lean_dec_ref_known(v___x_2267_, 1);
                        v___x_2269_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2270_ = lean_array_uset(v_bs_2259_, v_i_2258_, v___x_2269_);
                        v___x_2271_ = 1usize;
                        v___x_2272_ = lean_usize_add(v_i_2258_, v___x_2271_);
                        v___x_2273_ = lean_array_uset(v_bs_x27_2270_, v_i_2258_, v_a_2268_);
                        v_i_2258_ = v___x_2272_;
                        v_bs_2259_ = v___x_2273_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2259_);
                        v_a_2275_ = lean_ctor_get(v___x_2267_, 0);
                        v_isSharedCheck_2282_ = (!lean_is_exclusive(v___x_2267_)) as u8;
                        if v_isSharedCheck_2282_ == 0 {
                            v___x_2277_ = v___x_2267_;
                            v_isShared_2278_ = v_isSharedCheck_2282_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2275_);
                            lean_dec(v___x_2267_);
                            v___x_2277_ = lean_box(0);
                            v_isShared_2278_ = v_isSharedCheck_2282_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2278_ == 0 {
                    v___x_2280_ = v___x_2277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
                    v___x_2280_ = v_reuseFailAlloc_2281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(
    mut v_sz_2283_: *mut LeanObject,
    mut v_i_2284_: *mut LeanObject,
    mut v_bs_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = lean_unbox_usize(v_sz_2283_);
    lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = lean_unbox_usize(v_i_2284_);
    lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_2291_, v_i_boxed_2292_, v_bs_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    lean_dec(v___y_2289_);
    lean_dec_ref(v___y_2288_);
    lean_dec(v___y_2287_);
    lean_dec_ref(v___y_2286_);
    return v_res_2293_;
}
pub unsafe fn l_Lean_Meta_openAbstractMVarsResult(
    mut v_a_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
    mut v_a_2296_: *mut LeanObject,
    mut v_a_2297_: *mut LeanObject,
    mut v_a_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_paramNames_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_paramNames_2300_ = lean_ctor_get(v_a_2294_, 0);
                v_expr_2301_ = lean_ctor_get(v_a_2294_, 2);
                v_sz_2302_ = lean_array_size(v_paramNames_2300_);
                v___x_2303_ = 0usize;
                lean_inc_ref(v_paramNames_2300_);
                v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_2302_, v___x_2303_, v_paramNames_2300_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
                if lean_obj_tag(v___x_2304_) == 0 {
                    v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
                    lean_inc(v_a_2305_);
                    lean_dec_ref_known(v___x_2304_, 1);
                    lean_inc_ref(v_paramNames_2300_);
                    v___x_2306_ = l_Lean_Expr_instantiateLevelParamsArray(
                        v_expr_2301_,
                        v_paramNames_2300_,
                        v_a_2305_,
                    );
                    v___x_2307_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_2294_);
                    lean_dec_ref(v_a_2294_);
                    v___x_2308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                    v___x_2309_ = l_Lean_Meta_lambdaMetaTelescope(
                        v___x_2306_,
                        v___x_2308_,
                        v_a_2295_,
                        v_a_2296_,
                        v_a_2297_,
                        v_a_2298_,
                    );
                    lean_dec_ref_known(v___x_2308_, 1);
                    lean_dec_ref(v___x_2306_);
                    return v___x_2309_;
                } else {
                    lean_dec_ref(v_a_2294_);
                    v_a_2310_ = lean_ctor_get(v___x_2304_, 0);
                    v_isSharedCheck_2317_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2312_ = v___x_2304_;
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2310_);
                        lean_dec(v___x_2304_);
                        v___x_2312_ = lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2313_ == 0 {
                    v___x_2315_ = v___x_2312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_openAbstractMVarsResult___boxed(
    mut v_a_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
    mut v_a_2321_: *mut LeanObject,
    mut v_a_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2324_: *mut LeanObject = core::ptr::null_mut();
    v_res_2324_ =
        l_Lean_Meta_openAbstractMVarsResult(v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
    lean_dec(v_a_2322_);
    lean_dec_ref(v_a_2321_);
    lean_dec(v_a_2320_);
    lean_dec_ref(v_a_2319_);
    return v_res_2324_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_AbstractMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_AbstractMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_AbstractMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_AbstractMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_AbstractMVars(builtin);
}
