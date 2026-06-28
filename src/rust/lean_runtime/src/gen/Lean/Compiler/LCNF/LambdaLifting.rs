// Lean compiler output
// Module: Lean.Compiler.LCNF.LambdaLifting
// Imports: Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.AuxDeclCache
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::LCNF::AuxDeclCache::{
    initialize_Lean_Compiler_LCNF_AuxDeclCache, l_Lean_Compiler_LCNF_cacheAuxDecl___redArg,
    runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Code_size, l_Lean_Compiler_LCNF_Decl_inlineable___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::Closure::{
    initialize_Lean_Compiler_LCNF_Closure, l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed,
    l_Lean_Compiler_LCNF_Closure_run___redArg, runtime_initialize_Lean_Compiler_LCNF_Closure,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseDecl, l_Lean_Compiler_LCNF_eraseFunDecl___redArg,
    l_Lean_Compiler_LCNF_getPhase___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_Code_inferType, l_Lean_Compiler_LCNF_mkForallParams,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    l_Lean_Compiler_LCNF_Internalize_internalizeCode,
    l_Lean_Compiler_LCNF_Internalize_internalizeParam,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_addLetDecl;
use crate::r#gen::Lean::Compiler::LCNF::Level::{
    initialize_Lean_Compiler_LCNF_Level, l_Lean_Compiler_LCNF_Decl_setLevelParams,
    runtime_initialize_Lean_Compiler_LCNF_Level,
};
use crate::r#gen::Lean::Compiler::LCNF::MonadScope::{
    initialize_Lean_Compiler_LCNF_MonadScope, runtime_initialize_Lean_Compiler_LCNF_MonadScope,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    l_Lean_Compiler_LCNF_Decl_save, l_Lean_Compiler_LCNF_getDeclAt_x3f,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{l_Lean_FVarIdSet_insert, l_Lean_instBEqFVarId_beq};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::ReducibilityAttrs::l_Lean_isImplicitReducibleCore;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 108, 97, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0_value) as *mut LeanObject,12767607580449727887 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_lambdaLifting___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value: LeanStringObject<14> =
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
            108, 97, 109, 98, 100, 97, 76, 105, 102, 116, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_lambdaLifting___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value)
                as *mut LeanObject,
            14368744938553659294 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_lambdaLifting___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__0_value)
                as *mut LeanObject,
            257 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_lambdaLifting___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_lambdaLifting: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 101, 108, 97, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__0_value) as *mut LeanObject,780985648495343721 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value: LeanStringObject<19> =
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
            101, 97, 103, 101, 114, 76, 97, 109, 98, 100, 97, 76, 105, 102, 116, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value)
                as *mut LeanObject,
            16569119987899757434 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_eagerLambdaLifting: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1_value) as *mut LeanObject,7025002588753643236 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 97, 109, 98, 100, 97, 76, 105, 102, 116, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,8792104007360320962 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,18113694355690229155 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,17515471135450603758 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,8741750457908196044 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,8214822785481222413 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,13497181495734373348 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,10081422543683951597 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,11763816616693268312 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,4378412260064280946 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,3294462883915380147 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,5548176026338110088 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_lambdaLifting___closed__1_value) as *mut LeanObject,2559462443384452704 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(
    mut v_as_1787_: *mut LeanObject,
    mut v_i_1788_: usize,
    mut v_stop_1789_: usize,
    mut v___y_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: usize = 0;
    let mut v___x_1802_: usize = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_a_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1792_ = lean_usize_dec_eq(v_i_1788_, v_stop_1789_);
                if v___x_1792_ == 0 {
                    v___x_1793_ = lean_array_uget_borrowed(v_as_1787_, v_i_1788_);
                    v_type_1794_ = lean_ctor_get(v___x_1793_, 2);
                    lean_inc_ref(v_type_1794_);
                    v___x_1795_ =
                        l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_1794_, v___y_1790_);
                    if lean_obj_tag(v___x_1795_) == 0 {
                        v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
                        v_isSharedCheck_1812_ = (!lean_is_exclusive(v___x_1795_)) as u8;
                        if v_isSharedCheck_1812_ == 0 {
                            v___x_1798_ = v___x_1795_;
                            v_isShared_1799_ = v_isSharedCheck_1812_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1796_);
                            lean_dec(v___x_1795_);
                            v___x_1798_ = lean_box(0);
                            v_isShared_1799_ = v_isSharedCheck_1812_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1813_ = lean_ctor_get(v___x_1795_, 0);
                        v_isSharedCheck_1820_ = (!lean_is_exclusive(v___x_1795_)) as u8;
                        if v_isSharedCheck_1820_ == 0 {
                            v___x_1815_ = v___x_1795_;
                            v_isShared_1816_ = v_isSharedCheck_1820_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1813_);
                            lean_dec(v___x_1795_);
                            v___x_1815_ = lean_box(0);
                            v_isShared_1816_ = v_isSharedCheck_1820_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_1821_ = 0;
                    v___x_1822_ = lean_box((v___x_1821_) as usize);
                    v___x_1823_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1823_, 0, v___x_1822_);
                    return v___x_1823_;
                }
            }
            1 => {
                v___x_1800_ = 1;
                if lean_obj_tag(v_a_1796_) == 0 {
                    if v___x_1792_ == 0 {
                        lean_del_object(v___x_1798_);
                        v___x_1801_ = 1usize;
                        v___x_1802_ = lean_usize_add(v_i_1788_, v___x_1801_);
                        v_i_1788_ = v___x_1802_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1804_ = lean_box((v___x_1800_) as usize);
                        if v_isShared_1799_ == 0 {
                            lean_ctor_set(v___x_1798_, 0, v___x_1804_);
                            v___x_1806_ = v___x_1798_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
                            v___x_1806_ = v_reuseFailAlloc_1807_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_1796_, 1);
                    v___x_1808_ = lean_box((v___x_1800_) as usize);
                    if v_isShared_1799_ == 0 {
                        lean_ctor_set(v___x_1798_, 0, v___x_1808_);
                        v___x_1810_ = v___x_1798_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
                        v___x_1810_ = v_reuseFailAlloc_1811_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1806_;
            }
            3 => {
                return v___x_1810_;
            }
            4 => {
                if v_isShared_1816_ == 0 {
                    v___x_1818_ = v___x_1815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(
    mut v_as_1824_: *mut LeanObject,
    mut v_i_1825_: *mut LeanObject,
    mut v_stop_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1829_: usize = 0;
    let mut v_stop_boxed_1830_: usize = 0;
    let mut v_res_1831_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1829_ = lean_unbox_usize(v_i_1825_);
    lean_dec(v_i_1825_);
    v_stop_boxed_1830_ = lean_unbox_usize(v_stop_1826_);
    lean_dec(v_stop_1826_);
    v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_1824_, v_i_boxed_1829_, v_stop_boxed_1830_, v___y_1827_);
    lean_dec(v___y_1827_);
    lean_dec_ref(v_as_1824_);
    return v_res_1831_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(
    mut v_decl_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    v_params_1838_ = lean_ctor_get(v_decl_1832_, 2);
    v___x_1839_ = lean_unsigned_to_nat(0);
    v___x_1840_ = lean_array_get_size(v_params_1838_);
    v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
    if v___x_1841_ == 0 {
        let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
        v___x_1842_ = lean_box((v___x_1841_) as usize);
        v___x_1843_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1843_, 0, v___x_1842_);
        return v___x_1843_;
    } else {
        if v___x_1841_ == 0 {
            let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
            v___x_1844_ = lean_box((v___x_1841_) as usize);
            v___x_1845_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_1845_, 0, v___x_1844_);
            return v___x_1845_;
        } else {
            let mut v___x_1846_: usize = 0;
            let mut v___x_1847_: usize = 0;
            let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
            v___x_1846_ = 0usize;
            v___x_1847_ = lean_usize_of_nat(v___x_1840_);
            v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_params_1838_, v___x_1846_, v___x_1847_, v_a_1836_);
            return v___x_1848_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(
    mut v_decl_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(
        v_decl_1849_,
        v_a_1850_,
        v_a_1851_,
        v_a_1852_,
        v_a_1853_,
    );
    lean_dec(v_a_1853_);
    lean_dec_ref(v_a_1852_);
    lean_dec(v_a_1851_);
    lean_dec_ref(v_a_1850_);
    lean_dec_ref(v_decl_1849_);
    return v_res_1855_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(
    mut v_as_1856_: *mut LeanObject,
    mut v_i_1857_: usize,
    mut v_stop_1858_: usize,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(v_as_1856_, v_i_1857_, v_stop_1858_, v___y_1862_);
    return v___x_1864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(
    mut v_as_1865_: *mut LeanObject,
    mut v_i_1866_: *mut LeanObject,
    mut v_stop_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1873_: usize = 0;
    let mut v_stop_boxed_1874_: usize = 0;
    let mut v_res_1875_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1873_ = lean_unbox_usize(v_i_1866_);
    lean_dec(v_i_1866_);
    v_stop_boxed_1874_ = lean_unbox_usize(v_stop_1867_);
    lean_dec(v_stop_1867_);
    v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(v_as_1865_, v_i_boxed_1873_, v_stop_boxed_1874_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
    lean_dec(v___y_1871_);
    lean_dec_ref(v___y_1870_);
    lean_dec(v___y_1869_);
    lean_dec_ref(v___y_1868_);
    lean_dec_ref(v_as_1865_);
    return v_res_1875_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(
    mut v_decl_1876_: *mut LeanObject,
    mut v_a_1877_: *mut LeanObject,
    mut v_a_1878_: *mut LeanObject,
    mut v_a_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_liftInstParamOnly_1884_: u8 = 0;
    let mut v_minSize_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u8 = 0;
    v_value_1883_ = lean_ctor_get(v_decl_1876_, 4);
    v_liftInstParamOnly_1884_ = lean_ctor_get_uint8(
        v_a_1877_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_minSize_1885_ = lean_ctor_get(v_a_1877_, 2);
    v___x_1886_ = 0;
    v___x_1887_ = l_Lean_Compiler_LCNF_Code_size(v___x_1886_, v_value_1883_);
    v___x_1888_ = lean_nat_dec_lt(v___x_1887_, v_minSize_1885_);
    lean_dec(v___x_1887_);
    if v___x_1888_ == 0 {
        if v_liftInstParamOnly_1884_ == 0 {
            let mut v___x_1889_: u8 = 0;
            let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
            v___x_1889_ = 1;
            v___x_1890_ = lean_box((v___x_1889_) as usize);
            v___x_1891_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_1891_, 0, v___x_1890_);
            return v___x_1891_;
        } else {
            let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
            v___x_1892_ = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(
                v_decl_1876_,
                v_a_1878_,
                v_a_1879_,
                v_a_1880_,
                v_a_1881_,
            );
            return v___x_1892_;
        }
    } else {
        let mut v___x_1893_: u8 = 0;
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        v___x_1893_ = 0;
        v___x_1894_ = lean_box((v___x_1893_) as usize);
        v___x_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1895_, 0, v___x_1894_);
        return v___x_1895_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(
    mut v_decl_1896_: *mut LeanObject,
    mut v_a_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(
        v_decl_1896_,
        v_a_1897_,
        v_a_1898_,
        v_a_1899_,
        v_a_1900_,
        v_a_1901_,
    );
    lean_dec(v_a_1901_);
    lean_dec_ref(v_a_1900_);
    lean_dec(v_a_1899_);
    lean_dec_ref(v_a_1898_);
    lean_dec_ref(v_a_1897_);
    lean_dec_ref(v_decl_1896_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(
    mut v_decl_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_a_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(
        v_decl_1904_,
        v_a_1905_,
        v_a_1908_,
        v_a_1909_,
        v_a_1910_,
        v_a_1911_,
    );
    return v___x_1913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(
    mut v_decl_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
    mut v_a_1916_: *mut LeanObject,
    mut v_a_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(
        v_decl_1914_,
        v_a_1915_,
        v_a_1916_,
        v_a_1917_,
        v_a_1918_,
        v_a_1919_,
        v_a_1920_,
        v_a_1921_,
    );
    lean_dec(v_a_1921_);
    lean_dec_ref(v_a_1920_);
    lean_dec(v_a_1919_);
    lean_dec_ref(v_a_1918_);
    lean_dec(v_a_1917_);
    lean_dec(v_a_1916_);
    lean_dec_ref(v_a_1915_);
    lean_dec_ref(v_decl_1914_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(
    mut v_a_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainDecl_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suffix_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_a_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_reuseFailAlloc_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1930_ = lean_st_ref_take(v_a_1925_);
                v_decls_1931_ = lean_ctor_get(v___x_1930_, 0);
                v_nextIdx_1932_ = lean_ctor_get(v___x_1930_, 1);
                v_isSharedCheck_1977_ = (!lean_is_exclusive(v___x_1930_)) as u8;
                if v_isSharedCheck_1977_ == 0 {
                    v___x_1934_ = v___x_1930_;
                    v_isShared_1935_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_1932_);
                    lean_inc(v_decls_1931_);
                    lean_dec(v___x_1930_);
                    v___x_1934_ = lean_box(0);
                    v_isShared_1935_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1936_ = lean_unsigned_to_nat(1);
                v___x_1937_ = lean_nat_add(v_nextIdx_1932_, v___x_1936_);
                if v_isShared_1935_ == 0 {
                    lean_ctor_set(v___x_1934_, 1, v___x_1937_);
                    v___x_1939_ = v___x_1934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_decls_1931_);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1937_);
                    v___x_1939_ = v_reuseFailAlloc_1976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1940_ = lean_st_ref_set(v_a_1925_, v___x_1939_);
                v___x_1941_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_1926_);
                if lean_obj_tag(v___x_1941_) == 0 {
                    v_mainDecl_1942_ = lean_ctor_get(v_a_1924_, 1);
                    v_toSignature_1943_ = lean_ctor_get(v_mainDecl_1942_, 0);
                    v_a_1944_ = lean_ctor_get(v___x_1941_, 0);
                    lean_inc(v_a_1944_);
                    lean_dec_ref_known(v___x_1941_, 1);
                    v_suffix_1945_ = lean_ctor_get(v_a_1924_, 0);
                    v_name_1946_ = lean_ctor_get(v_toSignature_1943_, 0);
                    lean_inc(v_suffix_1945_);
                    v___x_1947_ = lean_name_append_index_after(v_suffix_1945_, v_nextIdx_1932_);
                    lean_inc(v_name_1946_);
                    v___x_1948_ = l_Lean_Name_append(v_name_1946_, v___x_1947_);
                    v___x_1949_ = (lean_unbox(v_a_1944_) as u8);
                    lean_dec(v_a_1944_);
                    lean_inc(v___x_1948_);
                    v___x_1950_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v___x_1948_,
                        v___x_1949_,
                        v_a_1927_,
                        v_a_1928_,
                    );
                    if lean_obj_tag(v___x_1950_) == 0 {
                        v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
                        v_isSharedCheck_1959_ = (!lean_is_exclusive(v___x_1950_)) as u8;
                        if v_isSharedCheck_1959_ == 0 {
                            v___x_1953_ = v___x_1950_;
                            v_isShared_1954_ = v_isSharedCheck_1959_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1951_);
                            lean_dec(v___x_1950_);
                            v___x_1953_ = lean_box(0);
                            v_isShared_1954_ = v_isSharedCheck_1959_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1948_);
                        v_a_1960_ = lean_ctor_get(v___x_1950_, 0);
                        v_isSharedCheck_1967_ = (!lean_is_exclusive(v___x_1950_)) as u8;
                        if v_isSharedCheck_1967_ == 0 {
                            v___x_1962_ = v___x_1950_;
                            v_isShared_1963_ = v_isSharedCheck_1967_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1960_);
                            lean_dec(v___x_1950_);
                            v___x_1962_ = lean_box(0);
                            v_isShared_1963_ = v_isSharedCheck_1967_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_nextIdx_1932_);
                    v_a_1968_ = lean_ctor_get(v___x_1941_, 0);
                    v_isSharedCheck_1975_ = (!lean_is_exclusive(v___x_1941_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1970_ = v___x_1941_;
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1968_);
                        lean_dec(v___x_1941_);
                        v___x_1970_ = lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_1951_) == 1 {
                    lean_dec_ref_known(v_a_1951_, 1);
                    lean_del_object(v___x_1953_);
                    lean_dec(v___x_1948_);
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1951_);
                    if v_isShared_1954_ == 0 {
                        lean_ctor_set(v___x_1953_, 0, v___x_1948_);
                        v___x_1957_ = v___x_1953_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1948_);
                        v___x_1957_ = v_reuseFailAlloc_1958_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1957_;
            }
            5 => {
                if v_isShared_1963_ == 0 {
                    v___x_1965_ = v___x_1962_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
                    v___x_1965_ = v_reuseFailAlloc_1966_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1965_;
            }
            7 => {
                if v_isShared_1971_ == 0 {
                    v___x_1973_ = v___x_1970_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(
    mut v_a_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1984_: *mut LeanObject = core::ptr::null_mut();
    v_res_1984_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(
        v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_,
    );
    lean_dec(v_a_1982_);
    lean_dec_ref(v_a_1981_);
    lean_dec_ref(v_a_1980_);
    lean_dec(v_a_1979_);
    lean_dec_ref(v_a_1978_);
    return v_res_1984_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
    mut v_a_1988_: *mut LeanObject,
    mut v_a_1989_: *mut LeanObject,
    mut v_a_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1993_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(
        v_a_1985_, v_a_1986_, v_a_1988_, v_a_1990_, v_a_1991_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(
    mut v_a_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_a_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
    mut v_a_2000_: *mut LeanObject,
    mut v_a_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2002_: *mut LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(
        v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_,
    );
    lean_dec(v_a_2000_);
    lean_dec_ref(v_a_1999_);
    lean_dec(v_a_1998_);
    lean_dec_ref(v_a_1997_);
    lean_dec(v_a_1996_);
    lean_dec(v_a_1995_);
    lean_dec_ref(v_a_1994_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(
    mut v_decl_2003_: *mut LeanObject,
    mut v_value_2004_: *mut LeanObject,
    mut v_a_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v_declNew_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_unused_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_2007_ = lean_ctor_get(v_decl_2003_, 0);
                v_binderName_2008_ = lean_ctor_get(v_decl_2003_, 1);
                v_type_2009_ = lean_ctor_get(v_decl_2003_, 3);
                v___x_2010_ = lean_st_ref_take(v_a_2005_);
                v_lctx_2011_ = lean_ctor_get(v___x_2010_, 0);
                v_nextIdx_2012_ = lean_ctor_get(v___x_2010_, 1);
                v_isSharedCheck_2041_ = (!lean_is_exclusive(v___x_2010_)) as u8;
                if v_isSharedCheck_2041_ == 0 {
                    v___x_2014_ = v___x_2010_;
                    v_isShared_2015_ = v_isSharedCheck_2041_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_2012_);
                    lean_inc(v_lctx_2011_);
                    lean_dec(v___x_2010_);
                    v___x_2014_ = lean_box(0);
                    v_isShared_2015_ = v_isSharedCheck_2041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2016_ = 0;
                lean_inc_ref(v_type_2009_);
                lean_inc(v_binderName_2008_);
                lean_inc(v_fvarId_2007_);
                v_declNew_2017_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v_declNew_2017_, 0, v_fvarId_2007_);
                lean_ctor_set(v_declNew_2017_, 1, v_binderName_2008_);
                lean_ctor_set(v_declNew_2017_, 2, v_type_2009_);
                lean_ctor_set(v_declNew_2017_, 3, v_value_2004_);
                lean_inc_ref(v_declNew_2017_);
                v___x_2018_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(
                    v___x_2016_,
                    v_lctx_2011_,
                    v_declNew_2017_,
                );
                if v_isShared_2015_ == 0 {
                    lean_ctor_set(v___x_2014_, 0, v___x_2018_);
                    v___x_2020_ = v___x_2014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2018_);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_nextIdx_2012_);
                    v___x_2020_ = v_reuseFailAlloc_2040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2021_ = lean_st_ref_set(v_a_2005_, v___x_2020_);
                v___x_2022_ = 1;
                v___x_2023_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                    v___x_2016_,
                    v_decl_2003_,
                    v___x_2022_,
                    v_a_2005_,
                );
                if lean_obj_tag(v___x_2023_) == 0 {
                    v_isSharedCheck_2030_ = (!lean_is_exclusive(v___x_2023_)) as u8;
                    if v_isSharedCheck_2030_ == 0 {
                        v_unused_2031_ = lean_ctor_get(v___x_2023_, 0);
                        lean_dec(v_unused_2031_);
                        v___x_2025_ = v___x_2023_;
                        v_isShared_2026_ = v_isSharedCheck_2030_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2023_);
                        v___x_2025_ = lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2030_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_declNew_2017_, 4);
                    v_a_2032_ = lean_ctor_get(v___x_2023_, 0);
                    v_isSharedCheck_2039_ = (!lean_is_exclusive(v___x_2023_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_2034_ = v___x_2023_;
                        v_isShared_2035_ = v_isSharedCheck_2039_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2032_);
                        lean_dec(v___x_2023_);
                        v___x_2034_ = lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2039_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2026_ == 0 {
                    lean_ctor_set(v___x_2025_, 0, v_declNew_2017_);
                    v___x_2028_ = v___x_2025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_declNew_2017_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2028_;
            }
            5 => {
                if v_isShared_2035_ == 0 {
                    v___x_2037_ = v___x_2034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
                    v___x_2037_ = v_reuseFailAlloc_2038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg___boxed(
    mut v_decl_2042_: *mut LeanObject,
    mut v_value_2043_: *mut LeanObject,
    mut v_a_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(
        v_decl_2042_,
        v_value_2043_,
        v_a_2044_,
    );
    lean_dec(v_a_2044_);
    lean_dec_ref(v_decl_2042_);
    return v_res_2046_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(
    mut v_decl_2047_: *mut LeanObject,
    mut v_value_2048_: *mut LeanObject,
    mut v_a_2049_: *mut LeanObject,
    mut v_a_2050_: *mut LeanObject,
    mut v_a_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
    mut v_a_2054_: *mut LeanObject,
    mut v_a_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(
        v_decl_2047_,
        v_value_2048_,
        v_a_2053_,
    );
    return v___x_2057_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___boxed(
    mut v_decl_2058_: *mut LeanObject,
    mut v_value_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2068_: *mut LeanObject = core::ptr::null_mut();
    v_res_2068_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl(
        v_decl_2058_,
        v_value_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
    );
    lean_dec(v_a_2066_);
    lean_dec_ref(v_a_2065_);
    lean_dec(v_a_2064_);
    lean_dec_ref(v_a_2063_);
    lean_dec(v_a_2062_);
    lean_dec(v_a_2061_);
    lean_dec_ref(v_a_2060_);
    lean_dec_ref(v_decl_2058_);
    return v_res_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(
    mut v_sz_2069_: usize,
    mut v_i_2070_: usize,
    mut v_bs_2071_: *mut LeanObject,
    mut v___y_2072_: u8,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v_v_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: usize = 0;
    let mut v___x_2088_: usize = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2079_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
                if v___x_2079_ == 0 {
                    v___x_2080_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2080_, 0, v_bs_2071_);
                    return v___x_2080_;
                } else {
                    v___x_2081_ = 0;
                    v_v_2082_ = lean_array_uget_borrowed(v_bs_2071_, v_i_2070_);
                    lean_inc(v_v_2082_);
                    v___x_2083_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                        v___x_2081_,
                        v_v_2082_,
                        v___y_2072_,
                        v___y_2073_,
                        v___y_2074_,
                        v___y_2075_,
                        v___y_2076_,
                        v___y_2077_,
                    );
                    if lean_obj_tag(v___x_2083_) == 0 {
                        v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
                        lean_inc(v_a_2084_);
                        lean_dec_ref_known(v___x_2083_, 1);
                        v___x_2085_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2086_ = lean_array_uset(v_bs_2071_, v_i_2070_, v___x_2085_);
                        v___x_2087_ = 1usize;
                        v___x_2088_ = lean_usize_add(v_i_2070_, v___x_2087_);
                        v___x_2089_ = lean_array_uset(v_bs_x27_2086_, v_i_2070_, v_a_2084_);
                        v_i_2070_ = v___x_2088_;
                        v_bs_2071_ = v___x_2089_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2071_);
                        v_a_2091_ = lean_ctor_get(v___x_2083_, 0);
                        v_isSharedCheck_2098_ = (!lean_is_exclusive(v___x_2083_)) as u8;
                        if v_isSharedCheck_2098_ == 0 {
                            v___x_2093_ = v___x_2083_;
                            v_isShared_2094_ = v_isSharedCheck_2098_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2091_);
                            lean_dec(v___x_2083_);
                            v___x_2093_ = lean_box(0);
                            v_isShared_2094_ = v_isSharedCheck_2098_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2094_ == 0 {
                    v___x_2096_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
                    v___x_2096_ = v_reuseFailAlloc_2097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(
    mut v_sz_2099_: *mut LeanObject,
    mut v_i_2100_: *mut LeanObject,
    mut v_bs_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2109_: usize = 0;
    let mut v_i_boxed_2110_: usize = 0;
    let mut v___y_2273__boxed_2111_: u8 = 0;
    let mut v_res_2112_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2109_ = lean_unbox_usize(v_sz_2099_);
    lean_dec(v_sz_2099_);
    v_i_boxed_2110_ = lean_unbox_usize(v_i_2100_);
    lean_dec(v_i_2100_);
    v___y_2273__boxed_2111_ = (lean_unbox(v___y_2102_) as u8);
    v_res_2112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_boxed_2109_, v_i_boxed_2110_, v_bs_2101_, v___y_2273__boxed_2111_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
    lean_dec(v___y_2107_);
    lean_dec_ref(v___y_2106_);
    lean_dec(v___y_2105_);
    lean_dec_ref(v___y_2104_);
    lean_dec(v___y_2103_);
    return v_res_2112_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(
    mut v_closure_2113_: *mut LeanObject,
    mut v_decl_2114_: *mut LeanObject,
    mut v_nameNew_2115_: *mut LeanObject,
    mut v_safe_2116_: u8,
    mut v_inlineAttr_x3f_2117_: *mut LeanObject,
    mut v_a_2118_: u8,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2125_: usize = 0;
    let mut v___x_2126_: usize = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2131_: usize = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: u8 = 0;
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut v_a_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2125_ = lean_array_size(v_closure_2113_);
                v___x_2126_ = 0usize;
                v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_2125_, v___x_2126_, v_closure_2113_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
                if lean_obj_tag(v___x_2127_) == 0 {
                    v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
                    lean_inc(v_a_2128_);
                    lean_dec_ref_known(v___x_2127_, 1);
                    v_params_2129_ = lean_ctor_get(v_decl_2114_, 2);
                    lean_inc_ref(v_params_2129_);
                    v_value_2130_ = lean_ctor_get(v_decl_2114_, 4);
                    lean_inc_ref(v_value_2130_);
                    lean_dec_ref(v_decl_2114_);
                    v_sz_2131_ = lean_array_size(v_params_2129_);
                    v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(v_sz_2131_, v___x_2126_, v_params_2129_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
                    if lean_obj_tag(v___x_2132_) == 0 {
                        v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
                        lean_inc(v_a_2133_);
                        lean_dec_ref_known(v___x_2132_, 1);
                        v___x_2134_ = 0;
                        v___x_2135_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                            v___x_2134_,
                            v_value_2130_,
                            v_a_2118_,
                            v_a_2119_,
                            v_a_2120_,
                            v_a_2121_,
                            v_a_2122_,
                            v_a_2123_,
                        );
                        if lean_obj_tag(v___x_2135_) == 0 {
                            v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
                            lean_inc_n(v_a_2136_, 2);
                            lean_dec_ref_known(v___x_2135_, 1);
                            v___x_2137_ = l_Lean_Compiler_LCNF_Code_inferType(
                                v___x_2134_,
                                v_a_2136_,
                                v_a_2120_,
                                v_a_2121_,
                                v_a_2122_,
                                v_a_2123_,
                            );
                            if lean_obj_tag(v___x_2137_) == 0 {
                                v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
                                lean_inc(v_a_2138_);
                                lean_dec_ref_known(v___x_2137_, 1);
                                v___x_2139_ = l_Array_append___redArg(v_a_2128_, v_a_2133_);
                                lean_dec(v_a_2133_);
                                lean_inc_ref(v___x_2139_);
                                v___x_2140_ = l_Lean_Compiler_LCNF_mkForallParams(
                                    v___x_2134_,
                                    v___x_2139_,
                                    v_a_2138_,
                                    v_a_2120_,
                                    v_a_2121_,
                                    v_a_2122_,
                                    v_a_2123_,
                                );
                                lean_dec(v_a_2138_);
                                if lean_obj_tag(v___x_2140_) == 0 {
                                    v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
                                    v_isSharedCheck_2154_ = (!lean_is_exclusive(v___x_2140_)) as u8;
                                    if v_isSharedCheck_2154_ == 0 {
                                        v___x_2143_ = v___x_2140_;
                                        v_isShared_2144_ = v_isSharedCheck_2154_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2141_);
                                        lean_dec(v___x_2140_);
                                        v___x_2143_ = lean_box(0);
                                        v_isShared_2144_ = v_isSharedCheck_2154_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_2139_);
                                    lean_dec(v_a_2136_);
                                    lean_dec(v_inlineAttr_x3f_2117_);
                                    lean_dec(v_nameNew_2115_);
                                    v_a_2155_ = lean_ctor_get(v___x_2140_, 0);
                                    v_isSharedCheck_2162_ = (!lean_is_exclusive(v___x_2140_)) as u8;
                                    if v_isSharedCheck_2162_ == 0 {
                                        v___x_2157_ = v___x_2140_;
                                        v_isShared_2158_ = v_isSharedCheck_2162_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2155_);
                                        lean_dec(v___x_2140_);
                                        v___x_2157_ = lean_box(0);
                                        v_isShared_2158_ = v_isSharedCheck_2162_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2136_);
                                lean_dec(v_a_2133_);
                                lean_dec(v_a_2128_);
                                lean_dec(v_inlineAttr_x3f_2117_);
                                lean_dec(v_nameNew_2115_);
                                v_a_2163_ = lean_ctor_get(v___x_2137_, 0);
                                v_isSharedCheck_2170_ = (!lean_is_exclusive(v___x_2137_)) as u8;
                                if v_isSharedCheck_2170_ == 0 {
                                    v___x_2165_ = v___x_2137_;
                                    v_isShared_2166_ = v_isSharedCheck_2170_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2163_);
                                    lean_dec(v___x_2137_);
                                    v___x_2165_ = lean_box(0);
                                    v_isShared_2166_ = v_isSharedCheck_2170_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2133_);
                            lean_dec(v_a_2128_);
                            lean_dec(v_inlineAttr_x3f_2117_);
                            lean_dec(v_nameNew_2115_);
                            v_a_2171_ = lean_ctor_get(v___x_2135_, 0);
                            v_isSharedCheck_2178_ = (!lean_is_exclusive(v___x_2135_)) as u8;
                            if v_isSharedCheck_2178_ == 0 {
                                v___x_2173_ = v___x_2135_;
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2171_);
                                lean_dec(v___x_2135_);
                                v___x_2173_ = lean_box(0);
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_value_2130_);
                        lean_dec(v_a_2128_);
                        lean_dec(v_inlineAttr_x3f_2117_);
                        lean_dec(v_nameNew_2115_);
                        v_a_2179_ = lean_ctor_get(v___x_2132_, 0);
                        v_isSharedCheck_2186_ = (!lean_is_exclusive(v___x_2132_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2181_ = v___x_2132_;
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2179_);
                            lean_dec(v___x_2132_);
                            v___x_2181_ = lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_inlineAttr_x3f_2117_);
                    lean_dec(v_nameNew_2115_);
                    lean_dec_ref(v_decl_2114_);
                    v_a_2187_ = lean_ctor_get(v___x_2127_, 0);
                    v_isSharedCheck_2194_ = (!lean_is_exclusive(v___x_2127_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v___x_2127_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2187_);
                        lean_dec(v___x_2127_);
                        v___x_2189_ = lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2145_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2145_, 0, v_a_2136_);
                v___x_2146_ = lean_box(0);
                v___x_2147_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_2147_, 0, v_nameNew_2115_);
                lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                lean_ctor_set(v___x_2147_, 2, v_a_2141_);
                lean_ctor_set(v___x_2147_, 3, v___x_2139_);
                lean_ctor_set_uint8(
                    v___x_2147_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_safe_2116_,
                );
                v___x_2148_ = 0;
                v___x_2149_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2149_, 0, v___x_2147_);
                lean_ctor_set(v___x_2149_, 1, v___x_2145_);
                lean_ctor_set(v___x_2149_, 2, v_inlineAttr_x3f_2117_);
                lean_ctor_set_uint8(
                    v___x_2149_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2148_,
                );
                v___x_2150_ = l_Lean_Compiler_LCNF_Decl_setLevelParams(v___x_2149_);
                if v_isShared_2144_ == 0 {
                    lean_ctor_set(v___x_2143_, 0, v___x_2150_);
                    v___x_2152_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
                    v___x_2152_ = v_reuseFailAlloc_2153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2152_;
            }
            3 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2160_;
            }
            5 => {
                if v_isShared_2166_ == 0 {
                    v___x_2168_ = v___x_2165_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
                    v___x_2168_ = v_reuseFailAlloc_2169_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2168_;
            }
            7 => {
                if v_isShared_2174_ == 0 {
                    v___x_2176_ = v___x_2173_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2176_;
            }
            9 => {
                if v_isShared_2182_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2184_;
            }
            11 => {
                if v_isShared_2190_ == 0 {
                    v___x_2192_ = v___x_2189_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(
    mut v_closure_2195_: *mut LeanObject,
    mut v_decl_2196_: *mut LeanObject,
    mut v_nameNew_2197_: *mut LeanObject,
    mut v_safe_2198_: *mut LeanObject,
    mut v_inlineAttr_x3f_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safe_boxed_2207_: u8 = 0;
    let mut v_a_boxed_2208_: u8 = 0;
    let mut v_res_2209_: *mut LeanObject = core::ptr::null_mut();
    v_safe_boxed_2207_ = (lean_unbox(v_safe_2198_) as u8);
    v_a_boxed_2208_ = (lean_unbox(v_a_2200_) as u8);
    v_res_2209_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_2195_, v_decl_2196_, v_nameNew_2197_, v_safe_boxed_2207_, v_inlineAttr_x3f_2199_, v_a_boxed_2208_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
    lean_dec(v_a_2205_);
    lean_dec_ref(v_a_2204_);
    lean_dec(v_a_2203_);
    lean_dec_ref(v_a_2202_);
    lean_dec(v_a_2201_);
    return v_res_2209_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(
    mut v_a_2210_: *mut LeanObject,
    mut v_a_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2210_) == 0 {
                    v___x_2212_ = l_List_reverse___redArg(v_a_2211_);
                    return v___x_2212_;
                } else {
                    v_head_2213_ = lean_ctor_get(v_a_2210_, 0);
                    v_tail_2214_ = lean_ctor_get(v_a_2210_, 1);
                    v_isSharedCheck_2223_ = (!lean_is_exclusive(v_a_2210_)) as u8;
                    if v_isSharedCheck_2223_ == 0 {
                        v___x_2216_ = v_a_2210_;
                        v_isShared_2217_ = v_isSharedCheck_2223_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2214_);
                        lean_inc(v_head_2213_);
                        lean_dec(v_a_2210_);
                        v___x_2216_ = lean_box(0);
                        v_isShared_2217_ = v_isSharedCheck_2223_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2218_ = l_Lean_mkLevelParam(v_head_2213_);
                if v_isShared_2217_ == 0 {
                    lean_ctor_set(v___x_2216_, 1, v_a_2211_);
                    lean_ctor_set(v___x_2216_, 0, v___x_2218_);
                    v___x_2220_ = v___x_2216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2218_);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2211_);
                    v___x_2220_ = v_reuseFailAlloc_2222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2210_ = v_tail_2214_;
                v_a_2211_ = v___x_2220_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(
    mut v_sz_2224_: usize,
    mut v_i_2225_: usize,
    mut v_bs_2226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2227_: u8 = 0;
    let mut v_v_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2227_ = lean_usize_dec_lt(v_i_2225_, v_sz_2224_);
                if v___x_2227_ == 0 {
                    return v_bs_2226_;
                } else {
                    v_v_2228_ = lean_array_uget_borrowed(v_bs_2226_, v_i_2225_);
                    v_fvarId_2229_ = lean_ctor_get(v_v_2228_, 0);
                    lean_inc(v_fvarId_2229_);
                    v___x_2230_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2231_ = lean_array_uset(v_bs_2226_, v_i_2225_, v___x_2230_);
                    v___x_2232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2232_, 0, v_fvarId_2229_);
                    v___x_2233_ = 1usize;
                    v___x_2234_ = lean_usize_add(v_i_2225_, v___x_2233_);
                    v___x_2235_ = lean_array_uset(v_bs_x27_2231_, v_i_2225_, v___x_2232_);
                    v_i_2225_ = v___x_2234_;
                    v_bs_2226_ = v___x_2235_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(
    mut v_sz_2237_: *mut LeanObject,
    mut v_i_2238_: *mut LeanObject,
    mut v_bs_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2240_: usize = 0;
    let mut v_i_boxed_2241_: usize = 0;
    let mut v_res_2242_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2240_ = lean_unbox_usize(v_sz_2237_);
    lean_dec(v_sz_2237_);
    v_i_boxed_2241_ = lean_unbox_usize(v_i_2238_);
    lean_dec(v_i_2238_);
    v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_boxed_2240_, v_i_boxed_2241_, v_bs_2239_);
    return v_res_2242_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2243_ = lean_box(0);
    v___x_2244_ = lean_unsigned_to_nat(16);
    v___x_2245_ = lean_mk_array(v___x_2244_, v___x_2243_);
    return v___x_2245_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    v___x_2246_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0,
    );
    v___x_2247_ = lean_unsigned_to_nat(0);
    v___x_2248_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2248_, 0, v___x_2247_);
    lean_ctor_set(v___x_2248_, 1, v___x_2246_);
    return v___x_2248_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(
    mut v_closure_2249_: *mut LeanObject,
    mut v_decl_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
    mut v_a_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclName_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2262_: usize = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: u8 = 0;
    let mut v___y_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v_unused_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_declName_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineAttr_x3f_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainDecl_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_safe_2337_: u8 = 0;
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2347_: u8 = 0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_inheritInlineAttrs_2352_: u8 = 0;
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainDecl_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineAttr_x3f_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2322_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(
                    v_a_2251_, v_a_2252_, v_a_2253_, v_a_2255_, v_a_2256_,
                );
                if lean_obj_tag(v___x_2322_) == 0 {
                    v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
                    lean_inc(v_a_2323_);
                    lean_dec_ref_known(v___x_2322_, 1);
                    v_inheritInlineAttrs_2352_ = lean_ctor_get_uint8(
                        v_a_2251_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    if v_inheritInlineAttrs_2352_ == 0 {
                        v___x_2353_ = lean_box(0);
                        v_inlineAttr_x3f_2325_ = v___x_2353_;
                        v___y_2326_ = v_a_2251_;
                        v___y_2327_ = v_a_2252_;
                        v___y_2328_ = v_a_2253_;
                        v___y_2329_ = v_a_2254_;
                        v___y_2330_ = v_a_2255_;
                        v___y_2331_ = v_a_2256_;
                        state = 11;
                        continue;
                    } else {
                        v_mainDecl_2354_ = lean_ctor_get(v_a_2251_, 1);
                        v_inlineAttr_x3f_2355_ = lean_ctor_get(v_mainDecl_2354_, 2);
                        v_inlineAttr_x3f_2325_ = v_inlineAttr_x3f_2355_;
                        v___y_2326_ = v_a_2251_;
                        v___y_2327_ = v_a_2252_;
                        v___y_2328_ = v_a_2253_;
                        v___y_2329_ = v_a_2254_;
                        v___y_2330_ = v_a_2255_;
                        v___y_2331_ = v_a_2256_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_2250_);
                    lean_dec_ref(v_closure_2249_);
                    v_a_2356_ = lean_ctor_get(v___x_2322_, 0);
                    v_isSharedCheck_2363_ = (!lean_is_exclusive(v___x_2322_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v___x_2322_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2356_);
                        lean_dec(v___x_2322_);
                        v___x_2358_ = lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2262_ = lean_array_size(v_closure_2249_);
                v___x_2263_ = 0usize;
                v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(v_sz_2262_, v___x_2263_, v_closure_2249_);
                v___x_2265_ = lean_alloc_ctor(3, 3, (0) as u32);
                lean_ctor_set(v___x_2265_, 0, v_auxDeclName_2260_);
                lean_ctor_set(v___x_2265_, 1, v___y_2259_);
                lean_ctor_set(v___x_2265_, 2, v___x_2264_);
                v___x_2266_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(
                    v_decl_2250_,
                    v___x_2265_,
                    v___y_2261_,
                );
                lean_dec_ref(v_decl_2250_);
                return v___x_2266_;
            }
            2 => {
                v_toSignature_2276_ = lean_ctor_get(v_a_2275_, 0);
                lean_inc_ref(v_a_2275_);
                v___x_2277_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(
                    v___y_2271_,
                    v_a_2275_,
                    v___y_2268_,
                    v___y_2274_,
                );
                if lean_obj_tag(v___x_2277_) == 0 {
                    v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
                    lean_inc(v_a_2278_);
                    lean_dec_ref_known(v___x_2277_, 1);
                    v_name_2279_ = lean_ctor_get(v_toSignature_2276_, 0);
                    v_levelParams_2280_ = lean_ctor_get(v_toSignature_2276_, 1);
                    v___x_2281_ = lean_box(0);
                    lean_inc(v_levelParams_2280_);
                    v___x_2282_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(v_levelParams_2280_, v___x_2281_);
                    if lean_obj_tag(v_a_2278_) == 0 {
                        lean_inc(v_name_2279_);
                        lean_inc_ref(v_a_2275_);
                        v___x_2283_ = l_Lean_Compiler_LCNF_Decl_save(
                            v___y_2271_,
                            v_a_2275_,
                            v___y_2272_,
                            v___y_2269_,
                            v___y_2268_,
                            v___y_2274_,
                        );
                        if lean_obj_tag(v___x_2283_) == 0 {
                            lean_dec_ref_known(v___x_2283_, 1);
                            v___x_2284_ = lean_st_ref_take(v___y_2270_);
                            v_decls_2285_ = lean_ctor_get(v___x_2284_, 0);
                            v_isSharedCheck_2294_ = (!lean_is_exclusive(v___x_2284_)) as u8;
                            if v_isSharedCheck_2294_ == 0 {
                                v_unused_2295_ = lean_ctor_get(v___x_2284_, 1);
                                lean_dec(v_unused_2295_);
                                v___x_2287_ = v___x_2284_;
                                v_isShared_2288_ = v_isSharedCheck_2294_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_decls_2285_);
                                lean_dec(v___x_2284_);
                                v___x_2287_ = lean_box(0);
                                v_isShared_2288_ = v_isSharedCheck_2294_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_2282_);
                            lean_dec(v_name_2279_);
                            lean_dec_ref(v_a_2275_);
                            lean_dec(v___y_2273_);
                            lean_dec_ref(v_decl_2250_);
                            lean_dec_ref(v_closure_2249_);
                            v_a_2296_ = lean_ctor_get(v___x_2283_, 0);
                            v_isSharedCheck_2303_ = (!lean_is_exclusive(v___x_2283_)) as u8;
                            if v_isSharedCheck_2303_ == 0 {
                                v___x_2298_ = v___x_2283_;
                                v_isShared_2299_ = v_isSharedCheck_2303_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2296_);
                                lean_dec(v___x_2283_);
                                v___x_2298_ = lean_box(0);
                                v_isShared_2299_ = v_isSharedCheck_2303_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_2273_);
                        v_declName_2304_ = lean_ctor_get(v_a_2278_, 0);
                        lean_inc(v_declName_2304_);
                        lean_dec_ref_known(v_a_2278_, 1);
                        v___x_2305_ = l_Lean_Compiler_LCNF_eraseDecl(
                            v___y_2271_,
                            v_a_2275_,
                            v___y_2272_,
                            v___y_2269_,
                            v___y_2268_,
                            v___y_2274_,
                        );
                        if lean_obj_tag(v___x_2305_) == 0 {
                            lean_dec_ref_known(v___x_2305_, 1);
                            v___y_2259_ = v___x_2282_;
                            v_auxDeclName_2260_ = v_declName_2304_;
                            v___y_2261_ = v___y_2269_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_declName_2304_);
                            lean_dec(v___x_2282_);
                            lean_dec_ref(v_decl_2250_);
                            lean_dec_ref(v_closure_2249_);
                            v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
                            v_isSharedCheck_2313_ = (!lean_is_exclusive(v___x_2305_)) as u8;
                            if v_isSharedCheck_2313_ == 0 {
                                v___x_2308_ = v___x_2305_;
                                v_isShared_2309_ = v_isSharedCheck_2313_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2306_);
                                lean_dec(v___x_2305_);
                                v___x_2308_ = lean_box(0);
                                v_isShared_2309_ = v_isSharedCheck_2313_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_a_2275_);
                    lean_dec(v___y_2273_);
                    lean_dec_ref(v_decl_2250_);
                    lean_dec_ref(v_closure_2249_);
                    v_a_2314_ = lean_ctor_get(v___x_2277_, 0);
                    v_isSharedCheck_2321_ = (!lean_is_exclusive(v___x_2277_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2277_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2314_);
                        lean_dec(v___x_2277_);
                        v___x_2316_ = lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2289_ = lean_array_push(v_decls_2285_, v_a_2275_);
                if v_isShared_2288_ == 0 {
                    lean_ctor_set(v___x_2287_, 1, v___y_2273_);
                    lean_ctor_set(v___x_2287_, 0, v___x_2289_);
                    v___x_2291_ = v___x_2287_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2289_);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___y_2273_);
                    v___x_2291_ = v_reuseFailAlloc_2293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2292_ = lean_st_ref_set(v___y_2270_, v___x_2291_);
                v___y_2259_ = v___x_2282_;
                v_auxDeclName_2260_ = v_name_2279_;
                v___y_2261_ = v___y_2269_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2299_ == 0 {
                    v___x_2301_ = v___x_2298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
                    v___x_2301_ = v_reuseFailAlloc_2302_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2301_;
            }
            7 => {
                if v_isShared_2309_ == 0 {
                    v___x_2311_ = v___x_2308_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
                    v___x_2311_ = v_reuseFailAlloc_2312_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2311_;
            }
            9 => {
                if v_isShared_2317_ == 0 {
                    v___x_2319_ = v___x_2316_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2319_;
            }
            11 => {
                v___x_2332_ = lean_unsigned_to_nat(0);
                v___x_2333_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1,
                );
                v___x_2334_ = lean_st_mk_ref(v___x_2333_);
                v_mainDecl_2335_ = lean_ctor_get(v___y_2326_, 1);
                v_toSignature_2336_ = lean_ctor_get(v_mainDecl_2335_, 0);
                v_safe_2337_ = lean_ctor_get_uint8(
                    v_toSignature_2336_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v___x_2338_ = 0;
                v___x_2339_ = 0;
                lean_inc(v_inlineAttr_x3f_2325_);
                lean_inc_ref(v_decl_2250_);
                lean_inc_ref(v_closure_2249_);
                v___x_2340_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(v_closure_2249_, v_decl_2250_, v_a_2323_, v_safe_2337_, v_inlineAttr_x3f_2325_, v___x_2339_, v___x_2334_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
                if lean_obj_tag(v___x_2340_) == 0 {
                    v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
                    lean_inc(v_a_2341_);
                    lean_dec_ref_known(v___x_2340_, 1);
                    v___x_2342_ = lean_st_ref_get(v___x_2334_);
                    lean_dec(v___x_2334_);
                    lean_dec(v___x_2342_);
                    v___y_2268_ = v___y_2330_;
                    v___y_2269_ = v___y_2329_;
                    v___y_2270_ = v___y_2327_;
                    v___y_2271_ = v___x_2338_;
                    v___y_2272_ = v___y_2328_;
                    v___y_2273_ = v___x_2332_;
                    v___y_2274_ = v___y_2331_;
                    v_a_2275_ = v_a_2341_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2334_);
                    if lean_obj_tag(v___x_2340_) == 0 {
                        v_a_2343_ = lean_ctor_get(v___x_2340_, 0);
                        lean_inc(v_a_2343_);
                        lean_dec_ref_known(v___x_2340_, 1);
                        v___y_2268_ = v___y_2330_;
                        v___y_2269_ = v___y_2329_;
                        v___y_2270_ = v___y_2327_;
                        v___y_2271_ = v___x_2338_;
                        v___y_2272_ = v___y_2328_;
                        v___y_2273_ = v___x_2332_;
                        v___y_2274_ = v___y_2331_;
                        v_a_2275_ = v_a_2343_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_decl_2250_);
                        lean_dec_ref(v_closure_2249_);
                        v_a_2344_ = lean_ctor_get(v___x_2340_, 0);
                        v_isSharedCheck_2351_ = (!lean_is_exclusive(v___x_2340_)) as u8;
                        if v_isSharedCheck_2351_ == 0 {
                            v___x_2346_ = v___x_2340_;
                            v_isShared_2347_ = v_isSharedCheck_2351_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2344_);
                            lean_dec(v___x_2340_);
                            v___x_2346_ = lean_box(0);
                            v_isShared_2347_ = v_isSharedCheck_2351_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_2347_ == 0 {
                    v___x_2349_ = v___x_2346_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
                    v___x_2349_ = v_reuseFailAlloc_2350_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2349_;
            }
            14 => {
                if v_isShared_2359_ == 0 {
                    v___x_2361_ = v___x_2358_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(
    mut v_closure_2364_: *mut LeanObject,
    mut v_decl_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2373_: *mut LeanObject = core::ptr::null_mut();
    v_res_2373_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(
        v_closure_2364_,
        v_decl_2365_,
        v_a_2366_,
        v_a_2367_,
        v_a_2368_,
        v_a_2369_,
        v_a_2370_,
        v_a_2371_,
    );
    lean_dec(v_a_2371_);
    lean_dec_ref(v_a_2370_);
    lean_dec(v_a_2369_);
    lean_dec_ref(v_a_2368_);
    lean_dec(v_a_2367_);
    lean_dec_ref(v_a_2366_);
    return v_res_2373_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(
    mut v_closure_2374_: *mut LeanObject,
    mut v_decl_2375_: *mut LeanObject,
    mut v_a_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_a_2378_: *mut LeanObject,
    mut v_a_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(
        v_closure_2374_,
        v_decl_2375_,
        v_a_2376_,
        v_a_2377_,
        v_a_2379_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(
    mut v_closure_2385_: *mut LeanObject,
    mut v_decl_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
    mut v_a_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(
        v_closure_2385_,
        v_decl_2386_,
        v_a_2387_,
        v_a_2388_,
        v_a_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
        v_a_2393_,
    );
    lean_dec(v_a_2393_);
    lean_dec_ref(v_a_2392_);
    lean_dec(v_a_2391_);
    lean_dec_ref(v_a_2390_);
    lean_dec(v_a_2389_);
    lean_dec(v_a_2388_);
    lean_dec_ref(v_a_2387_);
    return v_res_2395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(
    mut v_as_2398_: *mut LeanObject,
    mut v_sz_2399_: usize,
    mut v_i_2400_: usize,
    mut v_b_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v_array_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v_a_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v_fvarId_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: usize = 0;
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut v_unused_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut v_unused_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2403_ = lean_usize_dec_lt(v_i_2400_, v_sz_2399_);
                if v___x_2403_ == 0 {
                    v___x_2404_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2404_, 0, v_b_2401_);
                    return v___x_2404_;
                } else {
                    v_snd_2405_ = lean_ctor_get(v_b_2401_, 1);
                    v_isSharedCheck_2457_ = (!lean_is_exclusive(v_b_2401_)) as u8;
                    if v_isSharedCheck_2457_ == 0 {
                        v_unused_2458_ = lean_ctor_get(v_b_2401_, 0);
                        lean_dec(v_unused_2458_);
                        v___x_2407_ = v_b_2401_;
                        v_isShared_2408_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2405_);
                        lean_dec(v_b_2401_);
                        v___x_2407_ = lean_box(0);
                        v_isShared_2408_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_2409_ = lean_ctor_get(v_snd_2405_, 0);
                v_start_2410_ = lean_ctor_get(v_snd_2405_, 1);
                v_stop_2411_ = lean_ctor_get(v_snd_2405_, 2);
                v___x_2412_ = lean_box(0);
                v___x_2413_ = lean_nat_dec_lt(v_start_2410_, v_stop_2411_);
                if v___x_2413_ == 0 {
                    if v_isShared_2408_ == 0 {
                        lean_ctor_set(v___x_2407_, 0, v___x_2412_);
                        v___x_2415_ = v___x_2407_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2412_);
                        lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_snd_2405_);
                        v___x_2415_ = v_reuseFailAlloc_2417_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_2411_);
                    lean_inc(v_start_2410_);
                    lean_inc_ref(v_array_2409_);
                    v_isSharedCheck_2453_ = (!lean_is_exclusive(v_snd_2405_)) as u8;
                    if v_isSharedCheck_2453_ == 0 {
                        v_unused_2454_ = lean_ctor_get(v_snd_2405_, 2);
                        lean_dec(v_unused_2454_);
                        v_unused_2455_ = lean_ctor_get(v_snd_2405_, 1);
                        lean_dec(v_unused_2455_);
                        v_unused_2456_ = lean_ctor_get(v_snd_2405_, 0);
                        lean_dec(v_unused_2456_);
                        v___x_2419_ = v_snd_2405_;
                        v_isShared_2420_ = v_isSharedCheck_2453_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_snd_2405_);
                        v___x_2419_ = lean_box(0);
                        v_isShared_2420_ = v_isSharedCheck_2453_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2416_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2416_, 0, v___x_2415_);
                return v___x_2416_;
            }
            3 => {
                v_a_2421_ = lean_array_uget(v_as_2398_, v_i_2400_);
                v___x_2422_ = lean_array_fget(v_array_2409_, v_start_2410_);
                v___x_2423_ = lean_unsigned_to_nat(1);
                v___x_2424_ = lean_nat_add(v_start_2410_, v___x_2423_);
                lean_dec(v_start_2410_);
                if v_isShared_2420_ == 0 {
                    lean_ctor_set(v___x_2419_, 1, v___x_2424_);
                    v___x_2426_ = v___x_2419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_array_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2424_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_stop_2411_);
                    v___x_2426_ = v_reuseFailAlloc_2452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if lean_obj_tag(v_a_2421_) == 1 {
                    v_fvarId_2427_ = lean_ctor_get(v_a_2421_, 0);
                    v_isSharedCheck_2446_ = (!lean_is_exclusive(v_a_2421_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2429_ = v_a_2421_;
                        v_isShared_2430_ = v_isSharedCheck_2446_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_fvarId_2427_);
                        lean_dec(v_a_2421_);
                        v___x_2429_ = lean_box(0);
                        v_isShared_2430_ = v_isSharedCheck_2446_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2422_);
                    lean_dec(v_a_2421_);
                    v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0;
                    if v_isShared_2408_ == 0 {
                        lean_ctor_set(v___x_2407_, 1, v___x_2426_);
                        lean_ctor_set(v___x_2407_, 0, v___x_2447_);
                        v___x_2449_ = v___x_2407_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2447_);
                        lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2426_);
                        v___x_2449_ = v_reuseFailAlloc_2451_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_fvarId_2431_ = lean_ctor_get(v___x_2422_, 0);
                lean_inc(v_fvarId_2431_);
                lean_dec(v___x_2422_);
                v___x_2432_ = l_Lean_instBEqFVarId_beq(v_fvarId_2427_, v_fvarId_2431_);
                lean_dec(v_fvarId_2431_);
                lean_dec(v_fvarId_2427_);
                if v___x_2432_ == 0 {
                    v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___closed__0;
                    if v_isShared_2408_ == 0 {
                        lean_ctor_set(v___x_2407_, 1, v___x_2426_);
                        lean_ctor_set(v___x_2407_, 0, v___x_2433_);
                        v___x_2435_ = v___x_2407_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2433_);
                        lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2426_);
                        v___x_2435_ = v_reuseFailAlloc_2439_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2429_);
                    if v_isShared_2408_ == 0 {
                        lean_ctor_set(v___x_2407_, 1, v___x_2426_);
                        lean_ctor_set(v___x_2407_, 0, v___x_2412_);
                        v___x_2441_ = v___x_2407_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2412_);
                        lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2426_);
                        v___x_2441_ = v_reuseFailAlloc_2445_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2430_ == 0 {
                    lean_ctor_set_tag(v___x_2429_, 0);
                    lean_ctor_set(v___x_2429_, 0, v___x_2435_);
                    v___x_2437_ = v___x_2429_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
                    v___x_2437_ = v_reuseFailAlloc_2438_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2437_;
            }
            8 => {
                v___x_2442_ = 1usize;
                v___x_2443_ = lean_usize_add(v_i_2400_, v___x_2442_);
                v_i_2400_ = v___x_2443_;
                v_b_2401_ = v___x_2441_;
                state = 0;
                continue;
            }
            9 => {
                v___x_2450_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                return v___x_2450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg___boxed(
    mut v_as_2459_: *mut LeanObject,
    mut v_sz_2460_: *mut LeanObject,
    mut v_i_2461_: *mut LeanObject,
    mut v_b_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2464_: usize = 0;
    let mut v_i_boxed_2465_: usize = 0;
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2464_ = lean_unbox_usize(v_sz_2460_);
    lean_dec(v_sz_2460_);
    v_i_boxed_2465_ = lean_unbox_usize(v_i_2461_);
    lean_dec(v_i_2461_);
    v_res_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_2459_, v_sz_boxed_2464_, v_i_boxed_2465_, v_b_2462_);
    lean_dec_ref(v_as_2459_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(
    mut v_decl_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
    mut v_a_2474_: *mut LeanObject,
    mut v_a_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowEtaContraction_2481_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v_params_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v_fvarId_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v_fst_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2553_: u8 = 0;
    let mut v_a_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_reuseFailAlloc_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_unused_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_a_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_a_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_unused_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_allowEtaContraction_2481_ = lean_ctor_get_uint8(
                    v_a_2470_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                if v_allowEtaContraction_2481_ == 0 {
                    lean_dec_ref(v_decl_2469_);
                    v___x_2482_ = lean_box(0);
                    v___x_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                    return v___x_2483_;
                } else {
                    v_value_2484_ = lean_ctor_get(v_decl_2469_, 4);
                    lean_inc_ref(v_value_2484_);
                    if lean_obj_tag(v_value_2484_) == 0 {
                        v_decl_2485_ = lean_ctor_get(v_value_2484_, 0);
                        lean_inc_ref(v_decl_2485_);
                        v_value_2486_ = lean_ctor_get(v_decl_2485_, 3);
                        lean_inc(v_value_2486_);
                        if lean_obj_tag(v_value_2486_) == 3 {
                            v_k_2487_ = lean_ctor_get(v_value_2484_, 1);
                            v_isSharedCheck_2602_ = (!lean_is_exclusive(v_value_2484_)) as u8;
                            if v_isSharedCheck_2602_ == 0 {
                                v_unused_2603_ = lean_ctor_get(v_value_2484_, 0);
                                lean_dec(v_unused_2603_);
                                v___x_2489_ = v_value_2484_;
                                v_isShared_2490_ = v_isSharedCheck_2602_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_k_2487_);
                                lean_dec(v_value_2484_);
                                v___x_2489_ = lean_box(0);
                                v_isShared_2490_ = v_isSharedCheck_2602_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_value_2486_);
                            lean_dec_ref_known(v_value_2484_, 2);
                            lean_dec_ref(v_decl_2485_);
                            lean_dec_ref(v_decl_2469_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_value_2484_);
                        lean_dec_ref(v_decl_2469_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2479_ = lean_box(0);
                v___x_2480_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                return v___x_2480_;
            }
            2 => {
                if lean_obj_tag(v_k_2487_) == 5 {
                    v_params_2491_ = lean_ctor_get(v_decl_2469_, 2);
                    v_fvarId_2492_ = lean_ctor_get(v_decl_2485_, 0);
                    lean_inc(v_fvarId_2492_);
                    lean_dec_ref(v_decl_2485_);
                    v_declName_2493_ = lean_ctor_get(v_value_2486_, 0);
                    v_us_2494_ = lean_ctor_get(v_value_2486_, 1);
                    v_args_2495_ = lean_ctor_get(v_value_2486_, 2);
                    v_isSharedCheck_2601_ = (!lean_is_exclusive(v_value_2486_)) as u8;
                    if v_isSharedCheck_2601_ == 0 {
                        v___x_2497_ = v_value_2486_;
                        v_isShared_2498_ = v_isSharedCheck_2601_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_args_2495_);
                        lean_inc(v_us_2494_);
                        lean_inc(v_declName_2493_);
                        lean_dec(v_value_2486_);
                        v___x_2497_ = lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2601_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2489_);
                    lean_dec_ref_known(v_value_2486_, 3);
                    lean_dec_ref(v_k_2487_);
                    lean_dec_ref(v_decl_2485_);
                    lean_dec_ref(v_decl_2469_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_fvarId_2499_ = lean_ctor_get(v_k_2487_, 0);
                v_isSharedCheck_2600_ = (!lean_is_exclusive(v_k_2487_)) as u8;
                if v_isSharedCheck_2600_ == 0 {
                    v___x_2501_ = v_k_2487_;
                    v_isShared_2502_ = v_isSharedCheck_2600_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_fvarId_2499_);
                    lean_dec(v_k_2487_);
                    v___x_2501_ = lean_box(0);
                    v_isShared_2502_ = v_isSharedCheck_2600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2503_ = l_Lean_instBEqFVarId_beq(v_fvarId_2492_, v_fvarId_2499_);
                lean_dec(v_fvarId_2499_);
                lean_dec(v_fvarId_2492_);
                if v___x_2503_ == 0 {
                    lean_del_object(v___x_2497_);
                    lean_dec_ref(v_args_2495_);
                    lean_dec(v_us_2494_);
                    lean_dec(v_declName_2493_);
                    lean_del_object(v___x_2489_);
                    lean_dec_ref(v_decl_2469_);
                    v___x_2504_ = lean_box(0);
                    if v_isShared_2502_ == 0 {
                        lean_ctor_set_tag(v___x_2501_, 0);
                        lean_ctor_set(v___x_2501_, 0, v___x_2504_);
                        v___x_2506_ = v___x_2501_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
                        v___x_2506_ = v_reuseFailAlloc_2507_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2508_ = lean_array_get_size(v_args_2495_);
                    v___x_2509_ = lean_array_get_size(v_params_2491_);
                    v___x_2510_ = lean_nat_dec_eq(v___x_2508_, v___x_2509_);
                    if v___x_2510_ == 0 {
                        lean_del_object(v___x_2497_);
                        lean_dec_ref(v_args_2495_);
                        lean_dec(v_us_2494_);
                        lean_dec(v_declName_2493_);
                        lean_del_object(v___x_2489_);
                        lean_dec_ref(v_decl_2469_);
                        v___x_2511_ = lean_box(0);
                        if v_isShared_2502_ == 0 {
                            lean_ctor_set_tag(v___x_2501_, 0);
                            lean_ctor_set(v___x_2501_, 0, v___x_2511_);
                            v___x_2513_ = v___x_2501_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
                            v___x_2513_ = v_reuseFailAlloc_2514_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2501_);
                        v___x_2515_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2473_);
                        if lean_obj_tag(v___x_2515_) == 0 {
                            v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
                            lean_inc(v_a_2516_);
                            lean_dec_ref_known(v___x_2515_, 1);
                            v___x_2517_ = (lean_unbox(v_a_2516_) as u8);
                            lean_dec(v_a_2516_);
                            lean_inc(v_declName_2493_);
                            v___x_2518_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                                v_declName_2493_,
                                v___x_2517_,
                                v_a_2475_,
                                v_a_2476_,
                            );
                            if lean_obj_tag(v___x_2518_) == 0 {
                                v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
                                v_isSharedCheck_2583_ = (!lean_is_exclusive(v___x_2518_)) as u8;
                                if v_isSharedCheck_2583_ == 0 {
                                    v___x_2521_ = v___x_2518_;
                                    v_isShared_2522_ = v_isSharedCheck_2583_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2519_);
                                    lean_dec(v___x_2518_);
                                    v___x_2521_ = lean_box(0);
                                    v_isShared_2522_ = v_isSharedCheck_2583_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_2497_);
                                lean_dec_ref(v_args_2495_);
                                lean_dec(v_us_2494_);
                                lean_dec(v_declName_2493_);
                                lean_del_object(v___x_2489_);
                                lean_dec_ref(v_decl_2469_);
                                v_a_2584_ = lean_ctor_get(v___x_2518_, 0);
                                v_isSharedCheck_2591_ = (!lean_is_exclusive(v___x_2518_)) as u8;
                                if v_isSharedCheck_2591_ == 0 {
                                    v___x_2586_ = v___x_2518_;
                                    v_isShared_2587_ = v_isSharedCheck_2591_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_a_2584_);
                                    lean_dec(v___x_2518_);
                                    v___x_2586_ = lean_box(0);
                                    v_isShared_2587_ = v_isSharedCheck_2591_;
                                    state = 21;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_2497_);
                            lean_dec_ref(v_args_2495_);
                            lean_dec(v_us_2494_);
                            lean_dec(v_declName_2493_);
                            lean_del_object(v___x_2489_);
                            lean_dec_ref(v_decl_2469_);
                            v_a_2592_ = lean_ctor_get(v___x_2515_, 0);
                            v_isSharedCheck_2599_ = (!lean_is_exclusive(v___x_2515_)) as u8;
                            if v_isSharedCheck_2599_ == 0 {
                                v___x_2594_ = v___x_2515_;
                                v_isShared_2595_ = v_isSharedCheck_2599_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_2592_);
                                lean_dec(v___x_2515_);
                                v___x_2594_ = lean_box(0);
                                v_isShared_2595_ = v_isSharedCheck_2599_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                return v___x_2506_;
            }
            6 => {
                return v___x_2513_;
            }
            7 => {
                if lean_obj_tag(v_a_2519_) == 1 {
                    lean_del_object(v___x_2521_);
                    v_isSharedCheck_2577_ = (!lean_is_exclusive(v_a_2519_)) as u8;
                    if v_isSharedCheck_2577_ == 0 {
                        v_unused_2578_ = lean_ctor_get(v_a_2519_, 0);
                        lean_dec(v_unused_2578_);
                        v___x_2524_ = v_a_2519_;
                        v_isShared_2525_ = v_isSharedCheck_2577_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_a_2519_);
                        v___x_2524_ = lean_box(0);
                        v_isShared_2525_ = v_isSharedCheck_2577_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2519_);
                    lean_del_object(v___x_2497_);
                    lean_dec_ref(v_args_2495_);
                    lean_dec(v_us_2494_);
                    lean_dec(v_declName_2493_);
                    lean_del_object(v___x_2489_);
                    lean_dec_ref(v_decl_2469_);
                    v___x_2579_ = lean_box(0);
                    if v_isShared_2522_ == 0 {
                        lean_ctor_set(v___x_2521_, 0, v___x_2579_);
                        v___x_2581_ = v___x_2521_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
                        v___x_2581_ = v_reuseFailAlloc_2582_;
                        state = 20;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2526_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_params_2491_);
                v___x_2527_ = l_Array_toSubarray___redArg(v_params_2491_, v___x_2526_, v___x_2509_);
                v___x_2528_ = lean_box(0);
                if v_isShared_2490_ == 0 {
                    lean_ctor_set(v___x_2489_, 1, v___x_2527_);
                    lean_ctor_set(v___x_2489_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2489_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2527_);
                    v___x_2530_ = v_reuseFailAlloc_2576_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_sz_2531_ = lean_array_size(v_args_2495_);
                v___x_2532_ = 0usize;
                v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_args_2495_, v_sz_2531_, v___x_2532_, v___x_2530_);
                lean_dec_ref(v_args_2495_);
                if lean_obj_tag(v___x_2533_) == 0 {
                    v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
                    v_isSharedCheck_2567_ = (!lean_is_exclusive(v___x_2533_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2536_ = v___x_2533_;
                        v_isShared_2537_ = v_isSharedCheck_2567_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2534_);
                        lean_dec(v___x_2533_);
                        v___x_2536_ = lean_box(0);
                        v_isShared_2537_ = v_isSharedCheck_2567_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2524_);
                    lean_del_object(v___x_2497_);
                    lean_dec(v_us_2494_);
                    lean_dec(v_declName_2493_);
                    lean_dec_ref(v_decl_2469_);
                    v_a_2568_ = lean_ctor_get(v___x_2533_, 0);
                    v_isSharedCheck_2575_ = (!lean_is_exclusive(v___x_2533_)) as u8;
                    if v_isSharedCheck_2575_ == 0 {
                        v___x_2570_ = v___x_2533_;
                        v_isShared_2571_ = v_isSharedCheck_2575_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2568_);
                        lean_dec(v___x_2533_);
                        v___x_2570_ = lean_box(0);
                        v_isShared_2571_ = v_isSharedCheck_2575_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v_fst_2538_ = lean_ctor_get(v_a_2534_, 0);
                lean_inc(v_fst_2538_);
                lean_dec(v_a_2534_);
                if lean_obj_tag(v_fst_2538_) == 0 {
                    lean_del_object(v___x_2536_);
                    v___x_2539_ =
                        l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___closed__0;
                    if v_isShared_2498_ == 0 {
                        lean_ctor_set(v___x_2497_, 2, v___x_2539_);
                        v___x_2541_ = v___x_2497_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2562_ = lean_alloc_ctor(3, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_declName_2493_);
                        lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_us_2494_);
                        lean_ctor_set(v_reuseFailAlloc_2562_, 2, v___x_2539_);
                        v___x_2541_ = v_reuseFailAlloc_2562_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2524_);
                    lean_del_object(v___x_2497_);
                    lean_dec(v_us_2494_);
                    lean_dec(v_declName_2493_);
                    lean_dec_ref(v_decl_2469_);
                    v_val_2563_ = lean_ctor_get(v_fst_2538_, 0);
                    lean_inc(v_val_2563_);
                    lean_dec_ref_known(v_fst_2538_, 1);
                    if v_isShared_2537_ == 0 {
                        lean_ctor_set(v___x_2536_, 0, v_val_2563_);
                        v___x_2565_ = v___x_2536_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_val_2563_);
                        v___x_2565_ = v_reuseFailAlloc_2566_;
                        state = 17;
                        continue;
                    }
                }
            }
            11 => {
                v___x_2542_ = l_Lean_Compiler_LCNF_LambdaLifting_replaceFunDecl___redArg(
                    v_decl_2469_,
                    v___x_2541_,
                    v_a_2474_,
                );
                lean_dec_ref(v_decl_2469_);
                if lean_obj_tag(v___x_2542_) == 0 {
                    v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
                    v_isSharedCheck_2553_ = (!lean_is_exclusive(v___x_2542_)) as u8;
                    if v_isSharedCheck_2553_ == 0 {
                        v___x_2545_ = v___x_2542_;
                        v_isShared_2546_ = v_isSharedCheck_2553_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2543_);
                        lean_dec(v___x_2542_);
                        v___x_2545_ = lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2553_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2524_);
                    v_a_2554_ = lean_ctor_get(v___x_2542_, 0);
                    v_isSharedCheck_2561_ = (!lean_is_exclusive(v___x_2542_)) as u8;
                    if v_isSharedCheck_2561_ == 0 {
                        v___x_2556_ = v___x_2542_;
                        v_isShared_2557_ = v_isSharedCheck_2561_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2554_);
                        lean_dec(v___x_2542_);
                        v___x_2556_ = lean_box(0);
                        v_isShared_2557_ = v_isSharedCheck_2561_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2525_ == 0 {
                    lean_ctor_set(v___x_2524_, 0, v_a_2543_);
                    v___x_2548_ = v___x_2524_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2543_);
                    v___x_2548_ = v_reuseFailAlloc_2552_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2546_ == 0 {
                    lean_ctor_set(v___x_2545_, 0, v___x_2548_);
                    v___x_2550_ = v___x_2545_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
                    v___x_2550_ = v_reuseFailAlloc_2551_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2550_;
            }
            15 => {
                if v_isShared_2557_ == 0 {
                    v___x_2559_ = v___x_2556_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
                    v___x_2559_ = v_reuseFailAlloc_2560_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2559_;
            }
            17 => {
                return v___x_2565_;
            }
            18 => {
                if v_isShared_2571_ == 0 {
                    v___x_2573_ = v___x_2570_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2573_;
            }
            20 => {
                return v___x_2581_;
            }
            21 => {
                if v_isShared_2587_ == 0 {
                    v___x_2589_ = v___x_2586_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2589_;
            }
            23 => {
                if v_isShared_2595_ == 0 {
                    v___x_2597_ = v___x_2594_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f___boxed(
    mut v_decl_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2613_: *mut LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(
        v_decl_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
        v_a_2608_,
        v_a_2609_,
        v_a_2610_,
        v_a_2611_,
    );
    lean_dec(v_a_2611_);
    lean_dec_ref(v_a_2610_);
    lean_dec(v_a_2609_);
    lean_dec_ref(v_a_2608_);
    lean_dec(v_a_2607_);
    lean_dec(v_a_2606_);
    lean_dec_ref(v_a_2605_);
    return v_res_2613_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(
    mut v_as_2614_: *mut LeanObject,
    mut v_sz_2615_: usize,
    mut v_i_2616_: usize,
    mut v_b_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___redArg(v_as_2614_, v_sz_2615_, v_i_2616_, v_b_2617_);
    return v___x_2626_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0___boxed(
    mut v_as_2627_: *mut LeanObject,
    mut v_sz_2628_: *mut LeanObject,
    mut v_i_2629_: *mut LeanObject,
    mut v_b_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2639_: usize = 0;
    let mut v_i_boxed_2640_: usize = 0;
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2639_ = lean_unbox_usize(v_sz_2628_);
    lean_dec(v_sz_2628_);
    v_i_boxed_2640_ = lean_unbox_usize(v_i_2629_);
    lean_dec(v_i_2629_);
    v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f_spec__0(v_as_2627_, v_sz_boxed_2639_, v_i_boxed_2640_, v_b_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
    lean_dec(v___y_2637_);
    lean_dec_ref(v___y_2636_);
    lean_dec(v___y_2635_);
    lean_dec_ref(v___y_2634_);
    lean_dec(v___y_2633_);
    lean_dec(v___y_2632_);
    lean_dec_ref(v___y_2631_);
    lean_dec_ref(v_as_2627_);
    return v_res_2641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(
    mut v_as_2642_: *mut LeanObject,
    mut v_i_2643_: usize,
    mut v_stop_2644_: usize,
    mut v_b_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2646_ = lean_usize_dec_eq(v_i_2643_, v_stop_2644_);
                if v___x_2646_ == 0 {
                    v___x_2647_ = lean_array_uget_borrowed(v_as_2642_, v_i_2643_);
                    v_fvarId_2648_ = lean_ctor_get(v___x_2647_, 0);
                    lean_inc(v_fvarId_2648_);
                    v___x_2649_ = l_Lean_FVarIdSet_insert(v_b_2645_, v_fvarId_2648_);
                    v___x_2650_ = 1usize;
                    v___x_2651_ = lean_usize_add(v_i_2643_, v___x_2650_);
                    v_i_2643_ = v___x_2651_;
                    v_b_2645_ = v___x_2649_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2645_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(
    mut v_as_2653_: *mut LeanObject,
    mut v_i_2654_: *mut LeanObject,
    mut v_stop_2655_: *mut LeanObject,
    mut v_b_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2657_: usize = 0;
    let mut v_stop_boxed_2658_: usize = 0;
    let mut v_res_2659_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2657_ = lean_unbox_usize(v_i_2654_);
    lean_dec(v_i_2654_);
    v_stop_boxed_2658_ = lean_unbox_usize(v_stop_2655_);
    lean_dec(v_stop_2655_);
    v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_as_2653_, v_i_boxed_2657_, v_stop_boxed_2658_, v_b_2656_);
    lean_dec_ref(v_as_2653_);
    return v_res_2659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(
    mut v_k_2660_: *mut LeanObject,
    mut v_t_2661_: *mut LeanObject,
) -> u8 {
    let mut v_k_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: u8 = 0;
    let mut v___x_2667_: u8 = 0;
    let mut v___x_2669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2661_) == 0 {
                    v_k_2662_ = lean_ctor_get(v_t_2661_, 1);
                    v_l_2663_ = lean_ctor_get(v_t_2661_, 3);
                    v_r_2664_ = lean_ctor_get(v_t_2661_, 4);
                    v___x_2665_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2660_, v_k_2662_);
                    match v___x_2665_ {
                        0 => {
                            v_t_2661_ = v_l_2663_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2667_ = 1;
                            return v___x_2667_;
                        }
                        _ => {
                            v_t_2661_ = v_r_2664_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2669_ = 0;
                    return v___x_2669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg___boxed(
    mut v_k_2670_: *mut LeanObject,
    mut v_t_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: u8 = 0;
    let mut v_r_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_2670_, v_t_2671_);
    lean_dec(v_t_2671_);
    lean_dec(v_k_2670_);
    v_r_2673_ = lean_box((v_res_2672_) as usize);
    return v_r_2673_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(
    mut v_a_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> u8 {
    let mut v___x_2676_: u8 = 0;
    v___x_2676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v___y_2675_, v_a_2674_);
    return v___x_2676_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(
    mut v_a_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2679_: u8 = 0;
    let mut v_r_2680_: *mut LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(v_a_2677_, v___y_2678_);
    lean_dec(v___y_2678_);
    lean_dec(v_a_2677_);
    v_r_2680_ = lean_box((v_res_2679_) as usize);
    return v_r_2680_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(
    mut v_a_2681_: u8,
    mut v_x_2682_: *mut LeanObject,
) -> u8 {
    return v_a_2681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(
    mut v_a_2683_: *mut LeanObject,
    mut v_x_2684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_14210__boxed_2685_: u8 = 0;
    let mut v_res_2686_: u8 = 0;
    let mut v_r_2687_: *mut LeanObject = core::ptr::null_mut();
    v_a_14210__boxed_2685_ = (lean_unbox(v_a_2683_) as u8);
    v_res_2686_ =
        l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(v_a_14210__boxed_2685_, v_x_2684_);
    lean_dec(v_x_2684_);
    v_r_2687_ = lean_box((v_res_2686_) as usize);
    return v_r_2687_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(
    mut v_i_2688_: *mut LeanObject,
    mut v_as_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: u8 = 0;
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v___x_2733_: u8 = 0;
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v___x_2744_: usize = 0;
    let mut v___x_2745_: usize = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2765_: u8 = 0;
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v_code_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2698_ = lean_array_get_size(v_as_2689_);
                v___x_2699_ = lean_nat_dec_lt(v_i_2688_, v___x_2698_);
                if v___x_2699_ == 0 {
                    lean_dec(v_i_2688_);
                    v___x_2700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2700_, 0, v_as_2689_);
                    return v___x_2700_;
                } else {
                    v_a_2701_ = lean_array_fget_borrowed(v_as_2689_, v_i_2688_);
                    if lean_obj_tag(v_a_2701_) == 0 {
                        v_params_2717_ = lean_ctor_get(v_a_2701_, 1);
                        v_code_2718_ = lean_ctor_get(v_a_2701_, 2);
                        v___x_2719_ = lean_unsigned_to_nat(0);
                        v___x_2720_ = lean_array_get_size(v_params_2717_);
                        v___x_2721_ = lean_nat_dec_lt(v___x_2719_, v___x_2720_);
                        if v___x_2721_ == 0 {
                            lean_inc_ref(v_code_2718_);
                            v___x_2722_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                v_code_2718_,
                                v___y_2690_,
                                v___y_2691_,
                                v___y_2692_,
                                v___y_2693_,
                                v___y_2694_,
                                v___y_2695_,
                                v___y_2696_,
                            );
                            if lean_obj_tag(v___x_2722_) == 0 {
                                v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
                                lean_inc(v_a_2723_);
                                lean_dec_ref_known(v___x_2722_, 1);
                                lean_inc_ref(v_a_2701_);
                                v___x_2724_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2701_, v_a_2723_);
                                v_a_2703_ = v___x_2724_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_as_2689_);
                                lean_dec(v_i_2688_);
                                v_a_2725_ = lean_ctor_get(v___x_2722_, 0);
                                v_isSharedCheck_2732_ = (!lean_is_exclusive(v___x_2722_)) as u8;
                                if v_isSharedCheck_2732_ == 0 {
                                    v___x_2727_ = v___x_2722_;
                                    v_isShared_2728_ = v_isSharedCheck_2732_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2725_);
                                    lean_dec(v___x_2722_);
                                    v___x_2727_ = lean_box(0);
                                    v_isShared_2728_ = v_isSharedCheck_2732_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2733_ = lean_nat_dec_le(v___x_2720_, v___x_2720_);
                            if v___x_2733_ == 0 {
                                if v___x_2721_ == 0 {
                                    lean_inc_ref(v_code_2718_);
                                    v___x_2734_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                        v_code_2718_,
                                        v___y_2690_,
                                        v___y_2691_,
                                        v___y_2692_,
                                        v___y_2693_,
                                        v___y_2694_,
                                        v___y_2695_,
                                        v___y_2696_,
                                    );
                                    if lean_obj_tag(v___x_2734_) == 0 {
                                        v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
                                        lean_inc(v_a_2735_);
                                        lean_dec_ref_known(v___x_2734_, 1);
                                        v_a_2715_ = v_a_2735_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_as_2689_);
                                        lean_dec(v_i_2688_);
                                        v_a_2736_ = lean_ctor_get(v___x_2734_, 0);
                                        v_isSharedCheck_2743_ =
                                            (!lean_is_exclusive(v___x_2734_)) as u8;
                                        if v_isSharedCheck_2743_ == 0 {
                                            v___x_2738_ = v___x_2734_;
                                            v_isShared_2739_ = v_isSharedCheck_2743_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2736_);
                                            lean_dec(v___x_2734_);
                                            v___x_2738_ = lean_box(0);
                                            v_isShared_2739_ = v_isSharedCheck_2743_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_2744_ = 0usize;
                                    v___x_2745_ = lean_usize_of_nat(v___x_2720_);
                                    lean_inc(v___y_2692_);
                                    v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_2717_, v___x_2744_, v___x_2745_, v___y_2692_);
                                    lean_inc_ref(v_code_2718_);
                                    v___x_2747_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                        v_code_2718_,
                                        v___y_2690_,
                                        v___y_2691_,
                                        v___x_2746_,
                                        v___y_2693_,
                                        v___y_2694_,
                                        v___y_2695_,
                                        v___y_2696_,
                                    );
                                    lean_dec(v___x_2746_);
                                    if lean_obj_tag(v___x_2747_) == 0 {
                                        v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
                                        lean_inc(v_a_2748_);
                                        lean_dec_ref_known(v___x_2747_, 1);
                                        v_a_2715_ = v_a_2748_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_as_2689_);
                                        lean_dec(v_i_2688_);
                                        v_a_2749_ = lean_ctor_get(v___x_2747_, 0);
                                        v_isSharedCheck_2756_ =
                                            (!lean_is_exclusive(v___x_2747_)) as u8;
                                        if v_isSharedCheck_2756_ == 0 {
                                            v___x_2751_ = v___x_2747_;
                                            v_isShared_2752_ = v_isSharedCheck_2756_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2749_);
                                            lean_dec(v___x_2747_);
                                            v___x_2751_ = lean_box(0);
                                            v_isShared_2752_ = v_isSharedCheck_2756_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2757_ = 0usize;
                                v___x_2758_ = lean_usize_of_nat(v___x_2720_);
                                lean_inc(v___y_2692_);
                                v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_2717_, v___x_2757_, v___x_2758_, v___y_2692_);
                                lean_inc_ref(v_code_2718_);
                                v___x_2760_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                    v_code_2718_,
                                    v___y_2690_,
                                    v___y_2691_,
                                    v___x_2759_,
                                    v___y_2693_,
                                    v___y_2694_,
                                    v___y_2695_,
                                    v___y_2696_,
                                );
                                lean_dec(v___x_2759_);
                                if lean_obj_tag(v___x_2760_) == 0 {
                                    v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
                                    lean_inc(v_a_2761_);
                                    lean_dec_ref_known(v___x_2760_, 1);
                                    v_a_2715_ = v_a_2761_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec_ref(v_as_2689_);
                                    lean_dec(v_i_2688_);
                                    v_a_2762_ = lean_ctor_get(v___x_2760_, 0);
                                    v_isSharedCheck_2769_ = (!lean_is_exclusive(v___x_2760_)) as u8;
                                    if v_isSharedCheck_2769_ == 0 {
                                        v___x_2764_ = v___x_2760_;
                                        v_isShared_2765_ = v_isSharedCheck_2769_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2762_);
                                        lean_dec(v___x_2760_);
                                        v___x_2764_ = lean_box(0);
                                        v_isShared_2765_ = v_isSharedCheck_2769_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v_code_2770_ = lean_ctor_get(v_a_2701_, 0);
                        lean_inc_ref(v_code_2770_);
                        v___x_2771_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                            v_code_2770_,
                            v___y_2690_,
                            v___y_2691_,
                            v___y_2692_,
                            v___y_2693_,
                            v___y_2694_,
                            v___y_2695_,
                            v___y_2696_,
                        );
                        if lean_obj_tag(v___x_2771_) == 0 {
                            v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
                            lean_inc(v_a_2772_);
                            lean_dec_ref_known(v___x_2771_, 1);
                            lean_inc_ref(v_a_2701_);
                            v___x_2773_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2701_, v_a_2772_);
                            v_a_2703_ = v___x_2773_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_as_2689_);
                            lean_dec(v_i_2688_);
                            v_a_2774_ = lean_ctor_get(v___x_2771_, 0);
                            v_isSharedCheck_2781_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                            if v_isSharedCheck_2781_ == 0 {
                                v___x_2776_ = v___x_2771_;
                                v_isShared_2777_ = v_isSharedCheck_2781_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_2774_);
                                lean_dec(v___x_2771_);
                                v___x_2776_ = lean_box(0);
                                v_isShared_2777_ = v_isSharedCheck_2781_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2704_ = lean_ptr_addr(v_a_2701_);
                v___x_2705_ = lean_ptr_addr(v_a_2703_);
                v___x_2706_ = lean_usize_dec_eq(v___x_2704_, v___x_2705_);
                if v___x_2706_ == 0 {
                    v___x_2707_ = lean_unsigned_to_nat(1);
                    v___x_2708_ = lean_nat_add(v_i_2688_, v___x_2707_);
                    v___x_2709_ = lean_array_fset(v_as_2689_, v_i_2688_, v_a_2703_);
                    lean_dec(v_i_2688_);
                    v_i_2688_ = v___x_2708_;
                    v_as_2689_ = v___x_2709_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_2703_);
                    v___x_2711_ = lean_unsigned_to_nat(1);
                    v___x_2712_ = lean_nat_add(v_i_2688_, v___x_2711_);
                    lean_dec(v_i_2688_);
                    v_i_2688_ = v___x_2712_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                lean_inc(v_a_2701_);
                v___x_2716_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2701_, v_a_2715_);
                v_a_2703_ = v___x_2716_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2728_ == 0 {
                    v___x_2730_ = v___x_2727_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
                    v___x_2730_ = v_reuseFailAlloc_2731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2730_;
            }
            5 => {
                if v_isShared_2739_ == 0 {
                    v___x_2741_ = v___x_2738_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
                    v___x_2741_ = v_reuseFailAlloc_2742_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2741_;
            }
            7 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2754_;
            }
            9 => {
                if v_isShared_2765_ == 0 {
                    v___x_2767_ = v___x_2764_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
                    v___x_2767_ = v_reuseFailAlloc_2768_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2767_;
            }
            11 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
    mut v_code_2782_: *mut LeanObject,
    mut v_a_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
    mut v_a_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
    mut v_a_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___y_2801_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2811_: u8 = 0;
    let mut v_unused_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: u8 = 0;
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_decl_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declNew_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v_fvarId_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v___y_2859_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_unused_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: usize = 0;
    let mut v___x_2876_: usize = 0;
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: usize = 0;
    let mut v___x_2880_: u8 = 0;
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v_a_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2913_: u8 = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_a_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2925_: u8 = 0;
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_decl_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___y_2946_: u8 = 0;
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: usize = 0;
    let mut v___x_2966_: usize = 0;
    let mut v___x_2967_: u8 = 0;
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_cases_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2990_: u8 = 0;
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut v___x_2993_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3006_: u8 = 0;
    let mut v_unused_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_a_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2782_) {
                0 => {
                    v_decl_2791_ = lean_ctor_get(v_code_2782_, 0);
                    v_k_2792_ = lean_ctor_get(v_code_2782_, 1);
                    v_fvarId_2793_ = lean_ctor_get(v_decl_2791_, 0);
                    lean_inc(v_fvarId_2793_);
                    lean_inc(v_a_2785_);
                    v___x_2794_ = l_Lean_FVarIdSet_insert(v_a_2785_, v_fvarId_2793_);
                    lean_inc_ref(v_k_2792_);
                    v___x_2795_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                        v_k_2792_,
                        v_a_2783_,
                        v_a_2784_,
                        v___x_2794_,
                        v_a_2786_,
                        v_a_2787_,
                        v_a_2788_,
                        v_a_2789_,
                    );
                    lean_dec(v___x_2794_);
                    if lean_obj_tag(v___x_2795_) == 0 {
                        v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
                        v_isSharedCheck_2822_ = (!lean_is_exclusive(v___x_2795_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2798_ = v___x_2795_;
                            v_isShared_2799_ = v_isSharedCheck_2822_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2796_);
                            lean_dec(v___x_2795_);
                            v___x_2798_ = lean_box(0);
                            v_isShared_2799_ = v_isSharedCheck_2822_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_2782_, 2);
                        return v___x_2795_;
                    }
                }
                1 => {
                    v_decl_2823_ = lean_ctor_get(v_code_2782_, 0);
                    v_k_2824_ = lean_ctor_get(v_code_2782_, 1);
                    lean_inc_ref(v_decl_2823_);
                    v___x_2846_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(
                        v_decl_2823_,
                        v_a_2783_,
                        v_a_2784_,
                        v_a_2785_,
                        v_a_2786_,
                        v_a_2787_,
                        v_a_2788_,
                        v_a_2789_,
                    );
                    if lean_obj_tag(v___x_2846_) == 0 {
                        v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
                        lean_inc(v_a_2847_);
                        lean_dec_ref_known(v___x_2846_, 1);
                        v___x_2848_ = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(
                            v_a_2847_, v_a_2783_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_,
                        );
                        if lean_obj_tag(v___x_2848_) == 0 {
                            v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
                            lean_inc(v_a_2849_);
                            lean_dec_ref_known(v___x_2848_, 1);
                            v___x_2850_ = (lean_unbox(v_a_2849_) as u8);
                            if v___x_2850_ == 0 {
                                lean_dec(v_a_2849_);
                                v_fvarId_2851_ = lean_ctor_get(v_a_2847_, 0);
                                lean_inc(v_fvarId_2851_);
                                lean_inc(v_a_2785_);
                                v___x_2852_ = l_Lean_FVarIdSet_insert(v_a_2785_, v_fvarId_2851_);
                                lean_inc_ref(v_k_2824_);
                                v___x_2853_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                    v_k_2824_,
                                    v_a_2783_,
                                    v_a_2784_,
                                    v___x_2852_,
                                    v_a_2786_,
                                    v_a_2787_,
                                    v_a_2788_,
                                    v_a_2789_,
                                );
                                lean_dec(v___x_2852_);
                                if lean_obj_tag(v___x_2853_) == 0 {
                                    v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
                                    v_isSharedCheck_2881_ = (!lean_is_exclusive(v___x_2853_)) as u8;
                                    if v_isSharedCheck_2881_ == 0 {
                                        v___x_2856_ = v___x_2853_;
                                        v_isShared_2857_ = v_isSharedCheck_2881_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2854_);
                                        lean_dec(v___x_2853_);
                                        v___x_2856_ = lean_box(0);
                                        v_isShared_2857_ = v_isSharedCheck_2881_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_2847_);
                                    lean_dec_ref_known(v_code_2782_, 2);
                                    return v___x_2853_;
                                }
                            } else {
                                lean_inc_ref(v_k_2824_);
                                lean_dec_ref_known(v_code_2782_, 2);
                                lean_inc(v_a_2847_);
                                v___x_2882_ =
                                    l_Lean_Compiler_LCNF_LambdaLifting_etaContractibleDecl_x3f(
                                        v_a_2847_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_,
                                        v_a_2787_, v_a_2788_, v_a_2789_,
                                    );
                                if lean_obj_tag(v___x_2882_) == 0 {
                                    v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
                                    lean_inc(v_a_2883_);
                                    lean_dec_ref_known(v___x_2882_, 1);
                                    if lean_obj_tag(v_a_2883_) == 1 {
                                        lean_dec(v_a_2849_);
                                        lean_dec(v_a_2847_);
                                        v_val_2884_ = lean_ctor_get(v_a_2883_, 0);
                                        lean_inc(v_val_2884_);
                                        lean_dec_ref_known(v_a_2883_, 1);
                                        v_declNew_2826_ = v_val_2884_;
                                        v___y_2827_ = v_a_2783_;
                                        v___y_2828_ = v_a_2784_;
                                        v___y_2829_ = v_a_2785_;
                                        v___y_2830_ = v_a_2786_;
                                        v___y_2831_ = v_a_2787_;
                                        v___y_2832_ = v_a_2788_;
                                        v___y_2833_ = v_a_2789_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec(v_a_2883_);
                                        lean_inc(v_a_2785_);
                                        v___f_2885_ = lean_alloc_closure(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                                        lean_closure_set(v___f_2885_, 0, v_a_2785_);
                                        v___f_2886_ = lean_alloc_closure(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                                        lean_closure_set(v___f_2886_, 0, v_a_2849_);
                                        lean_inc(v_a_2847_);
                                        v___x_2887_ = lean_alloc_closure(
                                            l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed
                                                as *mut core::ffi::c_void,
                                            8,
                                            1,
                                        );
                                        lean_closure_set(v___x_2887_, 0, v_a_2847_);
                                        v___x_2888_ = l_Lean_Compiler_LCNF_Closure_run___redArg(
                                            v___x_2887_,
                                            v___f_2885_,
                                            v___f_2886_,
                                            v_a_2786_,
                                            v_a_2787_,
                                            v_a_2788_,
                                            v_a_2789_,
                                        );
                                        if lean_obj_tag(v___x_2888_) == 0 {
                                            v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
                                            lean_inc(v_a_2889_);
                                            lean_dec_ref_known(v___x_2888_, 1);
                                            v_snd_2890_ = lean_ctor_get(v_a_2889_, 1);
                                            lean_inc(v_snd_2890_);
                                            lean_dec(v_a_2889_);
                                            v_fst_2891_ = lean_ctor_get(v_snd_2890_, 0);
                                            lean_inc(v_fst_2891_);
                                            lean_dec(v_snd_2890_);
                                            v___x_2892_ = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(v_fst_2891_, v_a_2847_, v_a_2783_, v_a_2784_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
                                            if lean_obj_tag(v___x_2892_) == 0 {
                                                v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
                                                lean_inc(v_a_2893_);
                                                lean_dec_ref_known(v___x_2892_, 1);
                                                v_declNew_2826_ = v_a_2893_;
                                                v___y_2827_ = v_a_2783_;
                                                v___y_2828_ = v_a_2784_;
                                                v___y_2829_ = v_a_2785_;
                                                v___y_2830_ = v_a_2786_;
                                                v___y_2831_ = v_a_2787_;
                                                v___y_2832_ = v_a_2788_;
                                                v___y_2833_ = v_a_2789_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_dec_ref(v_k_2824_);
                                                v_a_2894_ = lean_ctor_get(v___x_2892_, 0);
                                                v_isSharedCheck_2901_ =
                                                    (!lean_is_exclusive(v___x_2892_)) as u8;
                                                if v_isSharedCheck_2901_ == 0 {
                                                    v___x_2896_ = v___x_2892_;
                                                    v_isShared_2897_ = v_isSharedCheck_2901_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2894_);
                                                    lean_dec(v___x_2892_);
                                                    v___x_2896_ = lean_box(0);
                                                    v_isShared_2897_ = v_isSharedCheck_2901_;
                                                    state = 16;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_2847_);
                                            lean_dec_ref(v_k_2824_);
                                            v_a_2902_ = lean_ctor_get(v___x_2888_, 0);
                                            v_isSharedCheck_2909_ =
                                                (!lean_is_exclusive(v___x_2888_)) as u8;
                                            if v_isSharedCheck_2909_ == 0 {
                                                v___x_2904_ = v___x_2888_;
                                                v_isShared_2905_ = v_isSharedCheck_2909_;
                                                state = 18;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2902_);
                                                lean_dec(v___x_2888_);
                                                v___x_2904_ = lean_box(0);
                                                v_isShared_2905_ = v_isSharedCheck_2909_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2849_);
                                    lean_dec(v_a_2847_);
                                    lean_dec_ref(v_k_2824_);
                                    v_a_2910_ = lean_ctor_get(v___x_2882_, 0);
                                    v_isSharedCheck_2917_ = (!lean_is_exclusive(v___x_2882_)) as u8;
                                    if v_isSharedCheck_2917_ == 0 {
                                        v___x_2912_ = v___x_2882_;
                                        v_isShared_2913_ = v_isSharedCheck_2917_;
                                        state = 20;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2910_);
                                        lean_dec(v___x_2882_);
                                        v___x_2912_ = lean_box(0);
                                        v_isShared_2913_ = v_isSharedCheck_2917_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_2847_);
                            lean_dec_ref_known(v_code_2782_, 2);
                            v_a_2918_ = lean_ctor_get(v___x_2848_, 0);
                            v_isSharedCheck_2925_ = (!lean_is_exclusive(v___x_2848_)) as u8;
                            if v_isSharedCheck_2925_ == 0 {
                                v___x_2920_ = v___x_2848_;
                                v_isShared_2921_ = v_isSharedCheck_2925_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_2918_);
                                lean_dec(v___x_2848_);
                                v___x_2920_ = lean_box(0);
                                v_isShared_2921_ = v_isSharedCheck_2925_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_2782_, 2);
                        v_a_2926_ = lean_ctor_get(v___x_2846_, 0);
                        v_isSharedCheck_2933_ = (!lean_is_exclusive(v___x_2846_)) as u8;
                        if v_isSharedCheck_2933_ == 0 {
                            v___x_2928_ = v___x_2846_;
                            v_isShared_2929_ = v_isSharedCheck_2933_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_2926_);
                            lean_dec(v___x_2846_);
                            v___x_2928_ = lean_box(0);
                            v_isShared_2929_ = v_isSharedCheck_2933_;
                            state = 24;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_2934_ = lean_ctor_get(v_code_2782_, 0);
                    v_k_2935_ = lean_ctor_get(v_code_2782_, 1);
                    lean_inc_ref(v_decl_2934_);
                    v___x_2936_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(
                        v_decl_2934_,
                        v_a_2783_,
                        v_a_2784_,
                        v_a_2785_,
                        v_a_2786_,
                        v_a_2787_,
                        v_a_2788_,
                        v_a_2789_,
                    );
                    if lean_obj_tag(v___x_2936_) == 0 {
                        v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
                        lean_inc(v_a_2937_);
                        lean_dec_ref_known(v___x_2936_, 1);
                        v_fvarId_2938_ = lean_ctor_get(v_a_2937_, 0);
                        lean_inc(v_fvarId_2938_);
                        lean_inc(v_a_2785_);
                        v___x_2939_ = l_Lean_FVarIdSet_insert(v_a_2785_, v_fvarId_2938_);
                        lean_inc_ref(v_k_2935_);
                        v___x_2940_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                            v_k_2935_,
                            v_a_2783_,
                            v_a_2784_,
                            v___x_2939_,
                            v_a_2786_,
                            v_a_2787_,
                            v_a_2788_,
                            v_a_2789_,
                        );
                        lean_dec(v___x_2939_);
                        if lean_obj_tag(v___x_2940_) == 0 {
                            v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
                            v_isSharedCheck_2968_ = (!lean_is_exclusive(v___x_2940_)) as u8;
                            if v_isSharedCheck_2968_ == 0 {
                                v___x_2943_ = v___x_2940_;
                                v_isShared_2944_ = v_isSharedCheck_2968_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_2941_);
                                lean_dec(v___x_2940_);
                                v___x_2943_ = lean_box(0);
                                v_isShared_2944_ = v_isSharedCheck_2968_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2937_);
                            lean_dec_ref_known(v_code_2782_, 2);
                            return v___x_2940_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_2782_, 2);
                        v_a_2969_ = lean_ctor_get(v___x_2936_, 0);
                        v_isSharedCheck_2976_ = (!lean_is_exclusive(v___x_2936_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2971_ = v___x_2936_;
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 32;
                            continue;
                        } else {
                            lean_inc(v_a_2969_);
                            lean_dec(v___x_2936_);
                            v___x_2971_ = lean_box(0);
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 32;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_2977_ = lean_ctor_get(v_code_2782_, 0);
                    lean_inc_ref(v_cases_2977_);
                    v_typeName_2978_ = lean_ctor_get(v_cases_2977_, 0);
                    v_resultType_2979_ = lean_ctor_get(v_cases_2977_, 1);
                    v_discr_2980_ = lean_ctor_get(v_cases_2977_, 2);
                    v_alts_2981_ = lean_ctor_get(v_cases_2977_, 3);
                    v_isSharedCheck_3020_ = (!lean_is_exclusive(v_cases_2977_)) as u8;
                    if v_isSharedCheck_3020_ == 0 {
                        v___x_2983_ = v_cases_2977_;
                        v_isShared_2984_ = v_isSharedCheck_3020_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_alts_2981_);
                        lean_inc(v_discr_2980_);
                        lean_inc(v_resultType_2979_);
                        lean_inc(v_typeName_2978_);
                        lean_dec(v_cases_2977_);
                        v___x_2983_ = lean_box(0);
                        v_isShared_2984_ = v_isSharedCheck_3020_;
                        state = 34;
                        continue;
                    }
                }
                _ => {
                    v___x_3021_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3021_, 0, v_code_2782_);
                    return v___x_3021_;
                }
            },
            1 => {
                v___x_2817_ = lean_ptr_addr(v_k_2792_);
                v___x_2818_ = lean_ptr_addr(v_a_2796_);
                v___x_2819_ = lean_usize_dec_eq(v___x_2817_, v___x_2818_);
                if v___x_2819_ == 0 {
                    v___y_2801_ = v___x_2819_;
                    state = 2;
                    continue;
                } else {
                    v___x_2820_ = lean_ptr_addr(v_decl_2791_);
                    v___x_2821_ = lean_usize_dec_eq(v___x_2820_, v___x_2820_);
                    v___y_2801_ = v___x_2821_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_2801_ == 0 {
                    lean_inc_ref(v_decl_2791_);
                    v_isSharedCheck_2811_ = (!lean_is_exclusive(v_code_2782_)) as u8;
                    if v_isSharedCheck_2811_ == 0 {
                        v_unused_2812_ = lean_ctor_get(v_code_2782_, 1);
                        lean_dec(v_unused_2812_);
                        v_unused_2813_ = lean_ctor_get(v_code_2782_, 0);
                        lean_dec(v_unused_2813_);
                        v___x_2803_ = v_code_2782_;
                        v_isShared_2804_ = v_isSharedCheck_2811_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_code_2782_);
                        v___x_2803_ = lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2811_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2796_);
                    if v_isShared_2799_ == 0 {
                        lean_ctor_set(v___x_2798_, 0, v_code_2782_);
                        v___x_2815_ = v___x_2798_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_code_2782_);
                        v___x_2815_ = v_reuseFailAlloc_2816_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2804_ == 0 {
                    lean_ctor_set(v___x_2803_, 1, v_a_2796_);
                    v___x_2806_ = v___x_2803_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_decl_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_a_2796_);
                    v___x_2806_ = v_reuseFailAlloc_2810_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2799_ == 0 {
                    lean_ctor_set(v___x_2798_, 0, v___x_2806_);
                    v___x_2808_ = v___x_2798_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
                    v___x_2808_ = v_reuseFailAlloc_2809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2808_;
            }
            6 => {
                return v___x_2815_;
            }
            7 => {
                v_fvarId_2834_ = lean_ctor_get(v_declNew_2826_, 0);
                lean_inc(v_fvarId_2834_);
                lean_inc(v___y_2829_);
                v___x_2835_ = l_Lean_FVarIdSet_insert(v___y_2829_, v_fvarId_2834_);
                v___x_2836_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                    v_k_2824_,
                    v___y_2827_,
                    v___y_2828_,
                    v___x_2835_,
                    v___y_2830_,
                    v___y_2831_,
                    v___y_2832_,
                    v___y_2833_,
                );
                lean_dec(v___x_2835_);
                if lean_obj_tag(v___x_2836_) == 0 {
                    v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
                    v_isSharedCheck_2845_ = (!lean_is_exclusive(v___x_2836_)) as u8;
                    if v_isSharedCheck_2845_ == 0 {
                        v___x_2839_ = v___x_2836_;
                        v_isShared_2840_ = v_isSharedCheck_2845_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2837_);
                        lean_dec(v___x_2836_);
                        v___x_2839_ = lean_box(0);
                        v_isShared_2840_ = v_isSharedCheck_2845_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_declNew_2826_);
                    return v___x_2836_;
                }
            }
            8 => {
                v___x_2841_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2841_, 0, v_declNew_2826_);
                lean_ctor_set(v___x_2841_, 1, v_a_2837_);
                if v_isShared_2840_ == 0 {
                    lean_ctor_set(v___x_2839_, 0, v___x_2841_);
                    v___x_2843_ = v___x_2839_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
                    v___x_2843_ = v_reuseFailAlloc_2844_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2843_;
            }
            10 => {
                v___x_2875_ = lean_ptr_addr(v_k_2824_);
                v___x_2876_ = lean_ptr_addr(v_a_2854_);
                v___x_2877_ = lean_usize_dec_eq(v___x_2875_, v___x_2876_);
                if v___x_2877_ == 0 {
                    v___y_2859_ = v___x_2877_;
                    state = 11;
                    continue;
                } else {
                    v___x_2878_ = lean_ptr_addr(v_decl_2823_);
                    v___x_2879_ = lean_ptr_addr(v_a_2847_);
                    v___x_2880_ = lean_usize_dec_eq(v___x_2878_, v___x_2879_);
                    v___y_2859_ = v___x_2880_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v___y_2859_ == 0 {
                    v_isSharedCheck_2869_ = (!lean_is_exclusive(v_code_2782_)) as u8;
                    if v_isSharedCheck_2869_ == 0 {
                        v_unused_2870_ = lean_ctor_get(v_code_2782_, 1);
                        lean_dec(v_unused_2870_);
                        v_unused_2871_ = lean_ctor_get(v_code_2782_, 0);
                        lean_dec(v_unused_2871_);
                        v___x_2861_ = v_code_2782_;
                        v_isShared_2862_ = v_isSharedCheck_2869_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec(v_code_2782_);
                        v___x_2861_ = lean_box(0);
                        v_isShared_2862_ = v_isSharedCheck_2869_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2854_);
                    lean_dec(v_a_2847_);
                    if v_isShared_2857_ == 0 {
                        lean_ctor_set(v___x_2856_, 0, v_code_2782_);
                        v___x_2873_ = v___x_2856_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_code_2782_);
                        v___x_2873_ = v_reuseFailAlloc_2874_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2862_ == 0 {
                    lean_ctor_set(v___x_2861_, 1, v_a_2854_);
                    lean_ctor_set(v___x_2861_, 0, v_a_2847_);
                    v___x_2864_ = v___x_2861_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2847_);
                    lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_a_2854_);
                    v___x_2864_ = v_reuseFailAlloc_2868_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2857_ == 0 {
                    lean_ctor_set(v___x_2856_, 0, v___x_2864_);
                    v___x_2866_ = v___x_2856_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2866_;
            }
            15 => {
                return v___x_2873_;
            }
            16 => {
                if v_isShared_2897_ == 0 {
                    v___x_2899_ = v___x_2896_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2899_;
            }
            18 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2907_;
            }
            20 => {
                if v_isShared_2913_ == 0 {
                    v___x_2915_ = v___x_2912_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
                    v___x_2915_ = v_reuseFailAlloc_2916_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2915_;
            }
            22 => {
                if v_isShared_2921_ == 0 {
                    v___x_2923_ = v___x_2920_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
                    v___x_2923_ = v_reuseFailAlloc_2924_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2923_;
            }
            24 => {
                if v_isShared_2929_ == 0 {
                    v___x_2931_ = v___x_2928_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2931_;
            }
            26 => {
                v___x_2962_ = lean_ptr_addr(v_k_2935_);
                v___x_2963_ = lean_ptr_addr(v_a_2941_);
                v___x_2964_ = lean_usize_dec_eq(v___x_2962_, v___x_2963_);
                if v___x_2964_ == 0 {
                    v___y_2946_ = v___x_2964_;
                    state = 27;
                    continue;
                } else {
                    v___x_2965_ = lean_ptr_addr(v_decl_2934_);
                    v___x_2966_ = lean_ptr_addr(v_a_2937_);
                    v___x_2967_ = lean_usize_dec_eq(v___x_2965_, v___x_2966_);
                    v___y_2946_ = v___x_2967_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v___y_2946_ == 0 {
                    v_isSharedCheck_2956_ = (!lean_is_exclusive(v_code_2782_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v_unused_2957_ = lean_ctor_get(v_code_2782_, 1);
                        lean_dec(v_unused_2957_);
                        v_unused_2958_ = lean_ctor_get(v_code_2782_, 0);
                        lean_dec(v_unused_2958_);
                        v___x_2948_ = v_code_2782_;
                        v_isShared_2949_ = v_isSharedCheck_2956_;
                        state = 28;
                        continue;
                    } else {
                        lean_dec(v_code_2782_);
                        v___x_2948_ = lean_box(0);
                        v_isShared_2949_ = v_isSharedCheck_2956_;
                        state = 28;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2941_);
                    lean_dec(v_a_2937_);
                    if v_isShared_2944_ == 0 {
                        lean_ctor_set(v___x_2943_, 0, v_code_2782_);
                        v___x_2960_ = v___x_2943_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_code_2782_);
                        v___x_2960_ = v_reuseFailAlloc_2961_;
                        state = 31;
                        continue;
                    }
                }
            }
            28 => {
                if v_isShared_2949_ == 0 {
                    lean_ctor_set(v___x_2948_, 1, v_a_2941_);
                    lean_ctor_set(v___x_2948_, 0, v_a_2937_);
                    v___x_2951_ = v___x_2948_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_a_2941_);
                    v___x_2951_ = v_reuseFailAlloc_2955_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_2944_ == 0 {
                    lean_ctor_set(v___x_2943_, 0, v___x_2951_);
                    v___x_2953_ = v___x_2943_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2953_;
            }
            31 => {
                return v___x_2960_;
            }
            32 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2974_;
            }
            34 => {
                v___x_2985_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_2981_);
                v___x_2986_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v___x_2985_, v_alts_2981_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
                if lean_obj_tag(v___x_2986_) == 0 {
                    v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
                    v_isSharedCheck_3011_ = (!lean_is_exclusive(v___x_2986_)) as u8;
                    if v_isSharedCheck_3011_ == 0 {
                        v___x_2989_ = v___x_2986_;
                        v_isShared_2990_ = v_isSharedCheck_3011_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_2987_);
                        lean_dec(v___x_2986_);
                        v___x_2989_ = lean_box(0);
                        v_isShared_2990_ = v_isSharedCheck_3011_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2983_);
                    lean_dec_ref(v_alts_2981_);
                    lean_dec(v_discr_2980_);
                    lean_dec_ref(v_resultType_2979_);
                    lean_dec(v_typeName_2978_);
                    lean_dec_ref_known(v_code_2782_, 1);
                    v_a_3012_ = lean_ctor_get(v___x_2986_, 0);
                    v_isSharedCheck_3019_ = (!lean_is_exclusive(v___x_2986_)) as u8;
                    if v_isSharedCheck_3019_ == 0 {
                        v___x_3014_ = v___x_2986_;
                        v_isShared_3015_ = v_isSharedCheck_3019_;
                        state = 41;
                        continue;
                    } else {
                        lean_inc(v_a_3012_);
                        lean_dec(v___x_2986_);
                        v___x_3014_ = lean_box(0);
                        v_isShared_3015_ = v_isSharedCheck_3019_;
                        state = 41;
                        continue;
                    }
                }
            }
            35 => {
                v___x_2991_ = lean_ptr_addr(v_alts_2981_);
                lean_dec_ref(v_alts_2981_);
                v___x_2992_ = lean_ptr_addr(v_a_2987_);
                v___x_2993_ = lean_usize_dec_eq(v___x_2991_, v___x_2992_);
                if v___x_2993_ == 0 {
                    v_isSharedCheck_3006_ = (!lean_is_exclusive(v_code_2782_)) as u8;
                    if v_isSharedCheck_3006_ == 0 {
                        v_unused_3007_ = lean_ctor_get(v_code_2782_, 0);
                        lean_dec(v_unused_3007_);
                        v___x_2995_ = v_code_2782_;
                        v_isShared_2996_ = v_isSharedCheck_3006_;
                        state = 36;
                        continue;
                    } else {
                        lean_dec(v_code_2782_);
                        v___x_2995_ = lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3006_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2987_);
                    lean_del_object(v___x_2983_);
                    lean_dec(v_discr_2980_);
                    lean_dec_ref(v_resultType_2979_);
                    lean_dec(v_typeName_2978_);
                    if v_isShared_2990_ == 0 {
                        lean_ctor_set(v___x_2989_, 0, v_code_2782_);
                        v___x_3009_ = v___x_2989_;
                        state = 40;
                        continue;
                    } else {
                        v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_code_2782_);
                        v___x_3009_ = v_reuseFailAlloc_3010_;
                        state = 40;
                        continue;
                    }
                }
            }
            36 => {
                if v_isShared_2984_ == 0 {
                    lean_ctor_set(v___x_2983_, 3, v_a_2987_);
                    v___x_2998_ = v___x_2983_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_typeName_2978_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_resultType_2979_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_discr_2980_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_a_2987_);
                    v___x_2998_ = v_reuseFailAlloc_3005_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2996_ == 0 {
                    lean_ctor_set(v___x_2995_, 0, v___x_2998_);
                    v___x_3000_ = v___x_2995_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2998_);
                    v___x_3000_ = v_reuseFailAlloc_3004_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_2990_ == 0 {
                    lean_ctor_set(v___x_2989_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2989_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
                    v___x_3002_ = v_reuseFailAlloc_3003_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3002_;
            }
            40 => {
                return v___x_3009_;
            }
            41 => {
                if v_isShared_3015_ == 0 {
                    v___x_3017_ = v___x_3014_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(
    mut v_funDecl_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
    mut v_a_3029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v___y_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3042_: u8 = 0;
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: usize = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: usize = 0;
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_3031_ = lean_ctor_get(v_funDecl_3022_, 2);
                lean_inc_ref(v_params_3031_);
                v_type_3032_ = lean_ctor_get(v_funDecl_3022_, 3);
                lean_inc_ref(v_type_3032_);
                v_value_3033_ = lean_ctor_get(v_funDecl_3022_, 4);
                v___x_3034_ = 0;
                v___x_3047_ = lean_unsigned_to_nat(0);
                v___x_3048_ = lean_array_get_size(v_params_3031_);
                v___x_3049_ = lean_nat_dec_lt(v___x_3047_, v___x_3048_);
                if v___x_3049_ == 0 {
                    lean_inc_ref(v_value_3033_);
                    v___x_3050_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                        v_value_3033_,
                        v_a_3023_,
                        v_a_3024_,
                        v_a_3025_,
                        v_a_3026_,
                        v_a_3027_,
                        v_a_3028_,
                        v_a_3029_,
                    );
                    v___y_3036_ = v___x_3050_;
                    state = 1;
                    continue;
                } else {
                    v___x_3051_ = lean_nat_dec_le(v___x_3048_, v___x_3048_);
                    if v___x_3051_ == 0 {
                        if v___x_3049_ == 0 {
                            lean_inc_ref(v_value_3033_);
                            v___x_3052_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                v_value_3033_,
                                v_a_3023_,
                                v_a_3024_,
                                v_a_3025_,
                                v_a_3026_,
                                v_a_3027_,
                                v_a_3028_,
                                v_a_3029_,
                            );
                            v___y_3036_ = v___x_3052_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3053_ = 0usize;
                            v___x_3054_ = lean_usize_of_nat(v___x_3048_);
                            lean_inc(v_a_3025_);
                            v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_3031_, v___x_3053_, v___x_3054_, v_a_3025_);
                            lean_inc_ref(v_value_3033_);
                            v___x_3056_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                                v_value_3033_,
                                v_a_3023_,
                                v_a_3024_,
                                v___x_3055_,
                                v_a_3026_,
                                v_a_3027_,
                                v_a_3028_,
                                v_a_3029_,
                            );
                            lean_dec(v___x_3055_);
                            v___y_3036_ = v___x_3056_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3057_ = 0usize;
                        v___x_3058_ = lean_usize_of_nat(v___x_3048_);
                        lean_inc(v_a_3025_);
                        v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_3031_, v___x_3057_, v___x_3058_, v_a_3025_);
                        lean_inc_ref(v_value_3033_);
                        v___x_3060_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
                            v_value_3033_,
                            v_a_3023_,
                            v_a_3024_,
                            v___x_3059_,
                            v_a_3026_,
                            v_a_3027_,
                            v_a_3028_,
                            v_a_3029_,
                        );
                        lean_dec(v___x_3059_);
                        v___y_3036_ = v___x_3060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3036_) == 0 {
                    v_a_3037_ = lean_ctor_get(v___y_3036_, 0);
                    lean_inc(v_a_3037_);
                    lean_dec_ref_known(v___y_3036_, 1);
                    v___x_3038_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3034_, v_funDecl_3022_, v_type_3032_, v_params_3031_, v_a_3037_, v_a_3027_);
                    return v___x_3038_;
                } else {
                    lean_dec_ref(v_type_3032_);
                    lean_dec_ref(v_params_3031_);
                    lean_dec_ref(v_funDecl_3022_);
                    v_a_3039_ = lean_ctor_get(v___y_3036_, 0);
                    v_isSharedCheck_3046_ = (!lean_is_exclusive(v___y_3036_)) as u8;
                    if v_isSharedCheck_3046_ == 0 {
                        v___x_3041_ = v___y_3036_;
                        v_isShared_3042_ = v_isSharedCheck_3046_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3039_);
                        lean_dec(v___y_3036_);
                        v___x_3041_ = lean_box(0);
                        v_isShared_3042_ = v_isSharedCheck_3046_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3042_ == 0 {
                    v___x_3044_ = v___x_3041_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
                    v___x_3044_ = v_reuseFailAlloc_3045_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl___boxed(
    mut v_funDecl_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3070_: *mut LeanObject = core::ptr::null_mut();
    v_res_3070_ = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(
        v_funDecl_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
        v_a_3066_,
        v_a_3067_,
        v_a_3068_,
    );
    lean_dec(v_a_3068_);
    lean_dec_ref(v_a_3067_);
    lean_dec(v_a_3066_);
    lean_dec_ref(v_a_3065_);
    lean_dec(v_a_3064_);
    lean_dec(v_a_3063_);
    lean_dec_ref(v_a_3062_);
    return v_res_3070_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3___boxed(
    mut v_i_3071_: *mut LeanObject,
    mut v_as_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3081_: *mut LeanObject = core::ptr::null_mut();
    v_res_3081_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__3(v_i_3071_, v_as_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
    lean_dec(v___y_3079_);
    lean_dec_ref(v___y_3078_);
    lean_dec(v___y_3077_);
    lean_dec_ref(v___y_3076_);
    lean_dec(v___y_3075_);
    lean_dec(v___y_3074_);
    lean_dec_ref(v___y_3073_);
    return v_res_3081_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_visitCode___boxed(
    mut v_code_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3091_: *mut LeanObject = core::ptr::null_mut();
    v_res_3091_ = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(
        v_code_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
        v_a_3087_,
        v_a_3088_,
        v_a_3089_,
    );
    lean_dec(v_a_3089_);
    lean_dec_ref(v_a_3088_);
    lean_dec(v_a_3087_);
    lean_dec_ref(v_a_3086_);
    lean_dec(v_a_3085_);
    lean_dec(v_a_3084_);
    lean_dec_ref(v_a_3083_);
    return v_res_3091_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(
    mut v_00_u03b2_3092_: *mut LeanObject,
    mut v_k_3093_: *mut LeanObject,
    mut v_t_3094_: *mut LeanObject,
) -> u8 {
    let mut v___x_3095_: u8 = 0;
    v___x_3095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___redArg(v_k_3093_, v_t_3094_);
    return v___x_3095_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2___boxed(
    mut v_00_u03b2_3096_: *mut LeanObject,
    mut v_k_3097_: *mut LeanObject,
    mut v_t_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3099_: u8 = 0;
    let mut v_r_3100_: *mut LeanObject = core::ptr::null_mut();
    v_res_3099_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__2(v_00_u03b2_3096_, v_k_3097_, v_t_3098_);
    lean_dec(v_t_3098_);
    lean_dec(v_k_3097_);
    v_r_3100_ = lean_box((v_res_3099_) as usize);
    return v_r_3100_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(
    mut v_f_3101_: *mut LeanObject,
    mut v_v_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_3102_) == 0 {
                    v_code_3111_ = lean_ctor_get(v_v_3102_, 0);
                    v_isSharedCheck_3135_ = (!lean_is_exclusive(v_v_3102_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3113_ = v_v_3102_;
                        v_isShared_3114_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_3111_);
                        lean_dec(v_v_3102_);
                        v___x_3113_ = lean_box(0);
                        v_isShared_3114_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_3101_);
                    v___x_3136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3136_, 0, v_v_3102_);
                    return v___x_3136_;
                }
            }
            1 => {
                lean_inc(v___y_3109_);
                lean_inc_ref(v___y_3108_);
                lean_inc(v___y_3107_);
                lean_inc_ref(v___y_3106_);
                lean_inc(v___y_3105_);
                lean_inc(v___y_3104_);
                lean_inc_ref(v___y_3103_);
                v___x_3115_ = lean_apply_9(
                    v_f_3101_,
                    v_code_3111_,
                    v___y_3103_,
                    v___y_3104_,
                    v___y_3105_,
                    v___y_3106_,
                    v___y_3107_,
                    v___y_3108_,
                    v___y_3109_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3126_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3126_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3116_);
                        lean_dec(v___x_3115_);
                        v___x_3118_ = lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3126_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3113_);
                    v_a_3127_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3134_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3134_ == 0 {
                        v___x_3129_ = v___x_3115_;
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3127_);
                        lean_dec(v___x_3115_);
                        v___x_3129_ = lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3114_ == 0 {
                    lean_ctor_set(v___x_3113_, 0, v_a_3116_);
                    v___x_3121_ = v___x_3113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3116_);
                    v___x_3121_ = v_reuseFailAlloc_3125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3119_ == 0 {
                    lean_ctor_set(v___x_3118_, 0, v___x_3121_);
                    v___x_3123_ = v___x_3118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3123_;
            }
            5 => {
                if v_isShared_3130_ == 0 {
                    v___x_3132_ = v___x_3129_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg___boxed(
    mut v_f_3137_: *mut LeanObject,
    mut v_v_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_3137_, v_v_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
    lean_dec(v___y_3145_);
    lean_dec_ref(v___y_3144_);
    lean_dec(v___y_3143_);
    lean_dec_ref(v___y_3142_);
    lean_dec(v___y_3141_);
    lean_dec(v___y_3140_);
    lean_dec_ref(v___y_3139_);
    return v_res_3147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(
    mut v_pu_3148_: u8,
    mut v_f_3149_: *mut LeanObject,
    mut v_v_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    v___x_3159_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v_f_3149_, v_v_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
    return v___x_3159_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___boxed(
    mut v_pu_3160_: *mut LeanObject,
    mut v_f_3161_: *mut LeanObject,
    mut v_v_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3171_: u8 = 0;
    let mut v_res_3172_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3171_ = (lean_unbox(v_pu_3160_) as u8);
    v_res_3172_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0(v_pu_boxed_3171_, v_f_3161_, v_v_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
    lean_dec(v___y_3169_);
    lean_dec_ref(v___y_3168_);
    lean_dec(v___y_3167_);
    lean_dec_ref(v___y_3166_);
    lean_dec(v___y_3165_);
    lean_dec(v___y_3164_);
    lean_dec_ref(v___y_3163_);
    return v_res_3172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_main(
    mut v_decl_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
    mut v_a_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_3185_: u8 = 0;
    let mut v_inlineAttr_x3f_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___y_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut v_params_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: usize = 0;
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: usize = 0;
    let mut v___x_3224_: usize = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_3183_ = lean_ctor_get(v_decl_3174_, 0);
                v_value_3184_ = lean_ctor_get(v_decl_3174_, 1);
                v_recursive_3185_ = lean_ctor_get_uint8(
                    v_decl_3174_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_3186_ = lean_ctor_get(v_decl_3174_, 2);
                v_isSharedCheck_3227_ = (!lean_is_exclusive(v_decl_3174_)) as u8;
                if v_isSharedCheck_3227_ == 0 {
                    v___x_3188_ = v_decl_3174_;
                    v_isShared_3189_ = v_isSharedCheck_3227_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_3186_);
                    lean_inc(v_value_3184_);
                    lean_inc(v_toSignature_3183_);
                    lean_dec(v_decl_3174_);
                    v___x_3188_ = lean_box(0);
                    v_isShared_3189_ = v_isSharedCheck_3227_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_params_3211_ = lean_ctor_get(v_toSignature_3183_, 3);
                v___x_3212_ = l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0;
                v___x_3213_ = lean_unsigned_to_nat(0);
                v___x_3214_ = lean_array_get_size(v_params_3211_);
                v___x_3215_ = lean_nat_dec_lt(v___x_3213_, v___x_3214_);
                if v___x_3215_ == 0 {
                    v___x_3216_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_3212_, v_value_3184_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
                    v___y_3191_ = v___x_3216_;
                    state = 2;
                    continue;
                } else {
                    v___x_3217_ = lean_nat_dec_le(v___x_3214_, v___x_3214_);
                    if v___x_3217_ == 0 {
                        if v___x_3215_ == 0 {
                            v___x_3218_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_3212_, v_value_3184_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
                            v___y_3191_ = v___x_3218_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3219_ = 0usize;
                            v___x_3220_ = lean_usize_of_nat(v___x_3214_);
                            lean_inc(v_a_3177_);
                            v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_3211_, v___x_3219_, v___x_3220_, v_a_3177_);
                            v___x_3222_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_3212_, v_value_3184_, v_a_3175_, v_a_3176_, v___x_3221_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
                            lean_dec(v___x_3221_);
                            v___y_3191_ = v___x_3222_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3223_ = 0usize;
                        v___x_3224_ = lean_usize_of_nat(v___x_3214_);
                        lean_inc(v_a_3177_);
                        v___x_3225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(v_params_3211_, v___x_3223_, v___x_3224_, v_a_3177_);
                        v___x_3226_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_LambdaLifting_main_spec__0___redArg(v___x_3212_, v_value_3184_, v_a_3175_, v_a_3176_, v___x_3225_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
                        lean_dec(v___x_3225_);
                        v___y_3191_ = v___x_3226_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v___y_3191_) == 0 {
                    v_a_3192_ = lean_ctor_get(v___y_3191_, 0);
                    v_isSharedCheck_3202_ = (!lean_is_exclusive(v___y_3191_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3194_ = v___y_3191_;
                        v_isShared_3195_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3192_);
                        lean_dec(v___y_3191_);
                        v___x_3194_ = lean_box(0);
                        v_isShared_3195_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3188_);
                    lean_dec(v_inlineAttr_x3f_3186_);
                    lean_dec_ref(v_toSignature_3183_);
                    v_a_3203_ = lean_ctor_get(v___y_3191_, 0);
                    v_isSharedCheck_3210_ = (!lean_is_exclusive(v___y_3191_)) as u8;
                    if v_isSharedCheck_3210_ == 0 {
                        v___x_3205_ = v___y_3191_;
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3203_);
                        lean_dec(v___y_3191_);
                        v___x_3205_ = lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3189_ == 0 {
                    lean_ctor_set(v___x_3188_, 1, v_a_3192_);
                    v___x_3197_ = v___x_3188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_toSignature_3183_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_a_3192_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_inlineAttr_x3f_3186_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3201_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_3185_,
                    );
                    v___x_3197_ = v_reuseFailAlloc_3201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 0, v___x_3197_);
                    v___x_3199_ = v___x_3194_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
                    v___x_3199_ = v_reuseFailAlloc_3200_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3199_;
            }
            6 => {
                if v_isShared_3206_ == 0 {
                    v___x_3208_ = v___x_3205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
                    v___x_3208_ = v_reuseFailAlloc_3209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LambdaLifting_main___boxed(
    mut v_decl_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
    mut v_a_3231_: *mut LeanObject,
    mut v_a_3232_: *mut LeanObject,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3237_: *mut LeanObject = core::ptr::null_mut();
    v_res_3237_ = l_Lean_Compiler_LCNF_LambdaLifting_main(
        v_decl_3228_,
        v_a_3229_,
        v_a_3230_,
        v_a_3231_,
        v_a_3232_,
        v_a_3233_,
        v_a_3234_,
        v_a_3235_,
    );
    lean_dec(v_a_3235_);
    lean_dec_ref(v_a_3234_);
    lean_dec(v_a_3233_);
    lean_dec_ref(v_a_3232_);
    lean_dec(v_a_3231_);
    lean_dec(v_a_3230_);
    lean_dec_ref(v_a_3229_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_lambdaLifting(
    mut v_decl_3243_: *mut LeanObject,
    mut v_liftInstParamOnly_3244_: u8,
    mut v_allowEtaContraction_3245_: u8,
    mut v_suffix_3246_: *mut LeanObject,
    mut v_inheritInlineAttrs_3247_: u8,
    mut v_minSize_3248_: *mut LeanObject,
    mut v_a_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
    mut v_a_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_a_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3254_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1;
                v___x_3255_ = lean_st_mk_ref(v___x_3254_);
                v___x_3256_ = lean_box(1);
                lean_inc_ref(v_decl_3243_);
                v_ctx_3257_ = lean_alloc_ctor(0, 3, (3) as u32);
                lean_ctor_set(v_ctx_3257_, 0, v_suffix_3246_);
                lean_ctor_set(v_ctx_3257_, 1, v_decl_3243_);
                lean_ctor_set(v_ctx_3257_, 2, v_minSize_3248_);
                lean_ctor_set_uint8(
                    v_ctx_3257_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_liftInstParamOnly_3244_,
                );
                lean_ctor_set_uint8(
                    v_ctx_3257_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_inheritInlineAttrs_3247_,
                );
                lean_ctor_set_uint8(
                    v_ctx_3257_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v_allowEtaContraction_3245_,
                );
                v___x_3258_ = l_Lean_Compiler_LCNF_LambdaLifting_main(
                    v_decl_3243_,
                    v_ctx_3257_,
                    v___x_3255_,
                    v___x_3256_,
                    v_a_3249_,
                    v_a_3250_,
                    v_a_3251_,
                    v_a_3252_,
                );
                lean_dec_ref_known(v_ctx_3257_, 3);
                if lean_obj_tag(v___x_3258_) == 0 {
                    v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
                    v_isSharedCheck_3269_ = (!lean_is_exclusive(v___x_3258_)) as u8;
                    if v_isSharedCheck_3269_ == 0 {
                        v___x_3261_ = v___x_3258_;
                        v_isShared_3262_ = v_isSharedCheck_3269_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3259_);
                        lean_dec(v___x_3258_);
                        v___x_3261_ = lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3269_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3255_);
                    v_a_3270_ = lean_ctor_get(v___x_3258_, 0);
                    v_isSharedCheck_3277_ = (!lean_is_exclusive(v___x_3258_)) as u8;
                    if v_isSharedCheck_3277_ == 0 {
                        v___x_3272_ = v___x_3258_;
                        v_isShared_3273_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3270_);
                        lean_dec(v___x_3258_);
                        v___x_3272_ = lean_box(0);
                        v_isShared_3273_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3263_ = lean_st_ref_get(v___x_3255_);
                lean_dec(v___x_3255_);
                v_decls_3264_ = lean_ctor_get(v___x_3263_, 0);
                lean_inc_ref(v_decls_3264_);
                lean_dec(v___x_3263_);
                v___x_3265_ = lean_array_push(v_decls_3264_, v_a_3259_);
                if v_isShared_3262_ == 0 {
                    lean_ctor_set(v___x_3261_, 0, v___x_3265_);
                    v___x_3267_ = v___x_3261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
                    v___x_3267_ = v_reuseFailAlloc_3268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3267_;
            }
            3 => {
                if v_isShared_3273_ == 0 {
                    v___x_3275_ = v___x_3272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
                    v___x_3275_ = v_reuseFailAlloc_3276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(
    mut v_decl_3278_: *mut LeanObject,
    mut v_liftInstParamOnly_3279_: *mut LeanObject,
    mut v_allowEtaContraction_3280_: *mut LeanObject,
    mut v_suffix_3281_: *mut LeanObject,
    mut v_inheritInlineAttrs_3282_: *mut LeanObject,
    mut v_minSize_3283_: *mut LeanObject,
    mut v_a_3284_: *mut LeanObject,
    mut v_a_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftInstParamOnly_boxed_3289_: u8 = 0;
    let mut v_allowEtaContraction_boxed_3290_: u8 = 0;
    let mut v_inheritInlineAttrs_boxed_3291_: u8 = 0;
    let mut v_res_3292_: *mut LeanObject = core::ptr::null_mut();
    v_liftInstParamOnly_boxed_3289_ = (lean_unbox(v_liftInstParamOnly_3279_) as u8);
    v_allowEtaContraction_boxed_3290_ = (lean_unbox(v_allowEtaContraction_3280_) as u8);
    v_inheritInlineAttrs_boxed_3291_ = (lean_unbox(v_inheritInlineAttrs_3282_) as u8);
    v_res_3292_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(
        v_decl_3278_,
        v_liftInstParamOnly_boxed_3289_,
        v_allowEtaContraction_boxed_3290_,
        v_suffix_3281_,
        v_inheritInlineAttrs_boxed_3291_,
        v_minSize_3283_,
        v_a_3284_,
        v_a_3285_,
        v_a_3286_,
        v_a_3287_,
    );
    lean_dec(v_a_3287_);
    lean_dec_ref(v_a_3286_);
    lean_dec(v_a_3285_);
    lean_dec_ref(v_a_3284_);
    return v_res_3292_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(
    mut v_as_3296_: *mut LeanObject,
    mut v_i_3297_: usize,
    mut v_stop_3298_: usize,
    mut v_b_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: usize = 0;
    let mut v___x_3308_: usize = 0;
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3310_ = lean_usize_dec_eq(v_i_3297_, v_stop_3298_);
                if v___x_3310_ == 0 {
                    v___x_3311_ = lean_unsigned_to_nat(0);
                    v___x_3312_ = lean_array_uget_borrowed(v_as_3296_, v_i_3297_);
                    v___x_3313_ = 1;
                    v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1;
                    lean_inc(v___x_3312_);
                    v___x_3315_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(
                        v___x_3312_,
                        v___x_3310_,
                        v___x_3313_,
                        v___x_3314_,
                        v___x_3310_,
                        v___x_3311_,
                        v___y_3300_,
                        v___y_3301_,
                        v___y_3302_,
                        v___y_3303_,
                    );
                    if lean_obj_tag(v___x_3315_) == 0 {
                        v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
                        lean_inc(v_a_3316_);
                        lean_dec_ref_known(v___x_3315_, 1);
                        v___x_3317_ = l_Array_append___redArg(v_b_3299_, v_a_3316_);
                        lean_dec(v_a_3316_);
                        v_a_3306_ = v___x_3317_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_3299_);
                        if lean_obj_tag(v___x_3315_) == 0 {
                            v_a_3318_ = lean_ctor_get(v___x_3315_, 0);
                            lean_inc(v_a_3318_);
                            lean_dec_ref_known(v___x_3315_, 1);
                            v_a_3306_ = v_a_3318_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_3315_;
                        }
                    }
                } else {
                    v___x_3319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3319_, 0, v_b_3299_);
                    return v___x_3319_;
                }
            }
            1 => {
                v___x_3307_ = 1usize;
                v___x_3308_ = lean_usize_add(v_i_3297_, v___x_3307_);
                v_i_3297_ = v___x_3308_;
                v_b_3299_ = v_a_3306_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(
    mut v_as_3320_: *mut LeanObject,
    mut v_i_3321_: *mut LeanObject,
    mut v_stop_3322_: *mut LeanObject,
    mut v_b_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3329_: usize = 0;
    let mut v_stop_boxed_3330_: usize = 0;
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3329_ = lean_unbox_usize(v_i_3321_);
    lean_dec(v_i_3321_);
    v_stop_boxed_3330_ = lean_unbox_usize(v_stop_3322_);
    lean_dec(v_stop_3322_);
    v_res_3331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_as_3320_, v_i_boxed_3329_, v_stop_boxed_3330_, v_b_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    lean_dec(v___y_3325_);
    lean_dec_ref(v___y_3324_);
    lean_dec_ref(v_as_3320_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_Compiler_LCNF_lambdaLifting___lam__0(
    mut v___x_3332_: *mut LeanObject,
    mut v_decls_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    v___x_3339_ = lean_mk_empty_array_with_capacity(v___x_3332_);
    v___x_3340_ = lean_array_get_size(v_decls_3333_);
    v___x_3341_ = lean_nat_dec_lt(v___x_3332_, v___x_3340_);
    if v___x_3341_ == 0 {
        let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
        v___x_3342_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3342_, 0, v___x_3339_);
        return v___x_3342_;
    } else {
        let mut v___x_3343_: u8 = 0;
        v___x_3343_ = lean_nat_dec_le(v___x_3340_, v___x_3340_);
        if v___x_3343_ == 0 {
            if v___x_3341_ == 0 {
                let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
                v___x_3344_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3344_, 0, v___x_3339_);
                return v___x_3344_;
            } else {
                let mut v___x_3345_: usize = 0;
                let mut v___x_3346_: usize = 0;
                let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
                v___x_3345_ = 0usize;
                v___x_3346_ = lean_usize_of_nat(v___x_3340_);
                v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_3333_, v___x_3345_, v___x_3346_, v___x_3339_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
                return v___x_3347_;
            }
        } else {
            let mut v___x_3348_: usize = 0;
            let mut v___x_3349_: usize = 0;
            let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
            v___x_3348_ = 0usize;
            v___x_3349_ = lean_usize_of_nat(v___x_3340_);
            v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_lambdaLifting_spec__0(v_decls_3333_, v___x_3348_, v___x_3349_, v___x_3339_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
            return v___x_3350_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(
    mut v___x_3351_: *mut LeanObject,
    mut v_decls_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3358_: *mut LeanObject = core::ptr::null_mut();
    v_res_3358_ = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(
        v___x_3351_,
        v_decls_3352_,
        v___y_3353_,
        v___y_3354_,
        v___y_3355_,
        v___y_3356_,
    );
    lean_dec(v___y_3356_);
    lean_dec_ref(v___y_3355_);
    lean_dec(v___y_3354_);
    lean_dec_ref(v___y_3353_);
    lean_dec_ref(v_decls_3352_);
    lean_dec(v___x_3351_);
    return v_res_3358_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(
    mut v_declName_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3374_ = lean_st_ref_get(v___y_3372_);
    v_env_3375_ = lean_ctor_get(v___x_3374_, 0);
    lean_inc_ref(v_env_3375_);
    lean_dec(v___x_3374_);
    v___x_3376_ = l_Lean_isImplicitReducibleCore(v_env_3375_, v_declName_3371_);
    v___x_3377_ = lean_box((v___x_3376_) as usize);
    v___x_3378_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3378_, 0, v___x_3377_);
    return v___x_3378_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg___boxed(
    mut v_declName_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3382_: *mut LeanObject = core::ptr::null_mut();
    v_res_3382_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(
            v_declName_3379_,
            v___y_3380_,
        );
    lean_dec(v___y_3380_);
    return v_res_3382_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(
    mut v_declName_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    v___x_3389_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(
            v_declName_3383_,
            v___y_3387_,
        );
    return v___x_3389_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(
    mut v_declName_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3396_: *mut LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(
        v_declName_3390_,
        v___y_3391_,
        v___y_3392_,
        v___y_3393_,
        v___y_3394_,
    );
    lean_dec(v___y_3394_);
    lean_dec_ref(v___y_3393_);
    lean_dec(v___y_3392_);
    lean_dec_ref(v___y_3391_);
    return v_res_3396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(
    mut v_as_3400_: *mut LeanObject,
    mut v_i_3401_: usize,
    mut v_stop_3402_: usize,
    mut v_b_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: usize = 0;
    let mut v___x_3412_: usize = 0;
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: u8 = 0;
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: u8 = 0;
    let mut v_a_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3435_: u8 = 0;
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3414_ = lean_usize_dec_eq(v_i_3401_, v_stop_3402_);
                if v___x_3414_ == 0 {
                    v___x_3415_ = lean_array_uget_borrowed(v_as_3400_, v_i_3401_);
                    v_toSignature_3416_ = lean_ctor_get(v___x_3415_, 0);
                    v_name_3417_ = lean_ctor_get(v_toSignature_3416_, 0);
                    lean_inc(v_name_3417_);
                    v___x_3418_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___redArg(v_name_3417_, v___y_3407_);
                    if lean_obj_tag(v___x_3418_) == 0 {
                        v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
                        lean_inc(v_a_3419_);
                        lean_dec_ref_known(v___x_3418_, 1);
                        v___x_3420_ = lean_unsigned_to_nat(0);
                        v___x_3430_ = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(v___x_3415_);
                        if v___x_3430_ == 0 {
                            v___x_3431_ = (lean_unbox(v_a_3419_) as u8);
                            lean_dec(v_a_3419_);
                            v___y_3422_ = v___x_3431_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_a_3419_);
                            v___y_3422_ = v___x_3430_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3403_);
                        v_a_3432_ = lean_ctor_get(v___x_3418_, 0);
                        v_isSharedCheck_3439_ = (!lean_is_exclusive(v___x_3418_)) as u8;
                        if v_isSharedCheck_3439_ == 0 {
                            v___x_3434_ = v___x_3418_;
                            v_isShared_3435_ = v_isSharedCheck_3439_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3432_);
                            lean_dec(v___x_3418_);
                            v___x_3434_ = lean_box(0);
                            v_isShared_3435_ = v_isSharedCheck_3439_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3440_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3440_, 0, v_b_3403_);
                    return v___x_3440_;
                }
            }
            1 => {
                v___x_3411_ = 1usize;
                v___x_3412_ = lean_usize_add(v_i_3401_, v___x_3411_);
                v_i_3401_ = v___x_3412_;
                v_b_3403_ = v_a_3410_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3422_ == 0 {
                    v___x_3423_ = 1;
                    v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___closed__1;
                    lean_inc(v___x_3415_);
                    v___x_3425_ = l_Lean_Compiler_LCNF_Decl_lambdaLifting(
                        v___x_3415_,
                        v___x_3423_,
                        v___x_3414_,
                        v___x_3424_,
                        v___x_3414_,
                        v___x_3420_,
                        v___y_3404_,
                        v___y_3405_,
                        v___y_3406_,
                        v___y_3407_,
                    );
                    if lean_obj_tag(v___x_3425_) == 0 {
                        v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
                        lean_inc(v_a_3426_);
                        lean_dec_ref_known(v___x_3425_, 1);
                        v___x_3427_ = l_Array_append___redArg(v_b_3403_, v_a_3426_);
                        lean_dec(v_a_3426_);
                        v_a_3410_ = v___x_3427_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_3403_);
                        if lean_obj_tag(v___x_3425_) == 0 {
                            v_a_3428_ = lean_ctor_get(v___x_3425_, 0);
                            lean_inc(v_a_3428_);
                            lean_dec_ref_known(v___x_3425_, 1);
                            v_a_3410_ = v_a_3428_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_3425_;
                        }
                    }
                } else {
                    lean_inc(v___x_3415_);
                    v___x_3429_ = lean_array_push(v_b_3403_, v___x_3415_);
                    v_a_3410_ = v___x_3429_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3435_ == 0 {
                    v___x_3437_ = v___x_3434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1___boxed(
    mut v_as_3441_: *mut LeanObject,
    mut v_i_3442_: *mut LeanObject,
    mut v_stop_3443_: *mut LeanObject,
    mut v_b_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3450_: usize = 0;
    let mut v_stop_boxed_3451_: usize = 0;
    let mut v_res_3452_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3450_ = lean_unbox_usize(v_i_3442_);
    lean_dec(v_i_3442_);
    v_stop_boxed_3451_ = lean_unbox_usize(v_stop_3443_);
    lean_dec(v_stop_3443_);
    v_res_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_as_3441_, v_i_boxed_3450_, v_stop_boxed_3451_, v_b_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
    lean_dec(v___y_3448_);
    lean_dec_ref(v___y_3447_);
    lean_dec(v___y_3446_);
    lean_dec_ref(v___y_3445_);
    lean_dec_ref(v_as_3441_);
    return v_res_3452_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(
    mut v___x_3453_: *mut LeanObject,
    mut v_decls_3454_: *mut LeanObject,
    mut v___y_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: u8 = 0;
    v___x_3460_ = lean_mk_empty_array_with_capacity(v___x_3453_);
    v___x_3461_ = lean_array_get_size(v_decls_3454_);
    v___x_3462_ = lean_nat_dec_lt(v___x_3453_, v___x_3461_);
    if v___x_3462_ == 0 {
        let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
        v___x_3463_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3463_, 0, v___x_3460_);
        return v___x_3463_;
    } else {
        let mut v___x_3464_: u8 = 0;
        v___x_3464_ = lean_nat_dec_le(v___x_3461_, v___x_3461_);
        if v___x_3464_ == 0 {
            if v___x_3462_ == 0 {
                let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
                v___x_3465_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3465_, 0, v___x_3460_);
                return v___x_3465_;
            } else {
                let mut v___x_3466_: usize = 0;
                let mut v___x_3467_: usize = 0;
                let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
                v___x_3466_ = 0usize;
                v___x_3467_ = lean_usize_of_nat(v___x_3461_);
                v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_3454_, v___x_3466_, v___x_3467_, v___x_3460_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
                return v___x_3468_;
            }
        } else {
            let mut v___x_3469_: usize = 0;
            let mut v___x_3470_: usize = 0;
            let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
            v___x_3469_ = 0usize;
            v___x_3470_ = lean_usize_of_nat(v___x_3461_);
            v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eagerLambdaLifting_spec__1(v_decls_3454_, v___x_3469_, v___x_3470_, v___x_3460_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
            return v___x_3471_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(
    mut v___x_3472_: *mut LeanObject,
    mut v_decls_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3479_: *mut LeanObject = core::ptr::null_mut();
    v_res_3479_ = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(
        v___x_3472_,
        v_decls_3473_,
        v___y_3474_,
        v___y_3475_,
        v___y_3476_,
        v___y_3477_,
    );
    lean_dec(v___y_3477_);
    lean_dec_ref(v___y_3476_);
    lean_dec(v___y_3475_);
    lean_dec_ref(v___y_3474_);
    lean_dec_ref(v_decls_3473_);
    lean_dec(v___x_3472_);
    return v_res_3479_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = lean_unsigned_to_nat(4205464346);
    v___x_3548_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
    v___x_3549_ = l_Lean_Name_num___override(v___x_3548_, v___x_3547_);
    return v___x_3549_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    v___x_3551_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
    v___x_3552_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
    v___x_3553_ = l_Lean_Name_str___override(v___x_3552_, v___x_3551_);
    return v___x_3553_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
    v___x_3556_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
    v___x_3557_ = l_Lean_Name_str___override(v___x_3556_, v___x_3555_);
    return v___x_3557_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v___x_3558_ = lean_unsigned_to_nat(2);
    v___x_3559_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
    v___x_3560_ = l_Lean_Name_num___override(v___x_3559_, v___x_3558_);
    return v___x_3560_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    v___x_3565_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
    v___x_3566_ = 1;
    v___x_3567_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_);
    v___x_3568_ = l_Lean_registerTraceClass(v___x_3565_, v___x_3566_, v___x_3567_);
    if lean_obj_tag(v___x_3568_) == 0 {
        let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3568_, 1);
        v___x_3569_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_;
        v___x_3570_ = l_Lean_registerTraceClass(v___x_3569_, v___x_3566_, v___x_3567_);
        return v___x_3570_;
    } else {
        return v___x_3568_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2____boxed(
    mut v_a_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3572_: *mut LeanObject = core::ptr::null_mut();
    v_res_3572_ = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
    return v_res_3572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_LambdaLifting_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_LambdaLifting_4205464346____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_LambdaLifting(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
}
