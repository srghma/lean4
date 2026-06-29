// Lean compiler output
// Module: Lean.MonadEnv
// Imports: Init.Control.Do Lean.Elab.Exception Lean.Log Lean.AuxRecursor Lean.Compiler.Old
use crate::ffi::{lean_array_get, lean_has_compile_error, lean_nat_dec_eq, lean_panic_fn_borrowed};
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_mapTR_loop___redArg};
use crate::r#gen::Init::Data::List::Control::l_List_allM___redArg;
use crate::r#gen::Init::Prelude::{
    l_instInhabitedOfMonad___redArg, l_instMonadExceptOfMonadExceptOf___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::{
    initialize_Lean_AuxRecursor, runtime_initialize_Lean_AuxRecursor,
};
use crate::r#gen::Lean::Compiler::Old::{
    initialize_Lean_Compiler_Old, runtime_initialize_Lean_Compiler_Old,
};
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numTypeFormers;
use crate::r#gen::Lean::Elab::Exception::{
    initialize_Lean_Elab_Exception, l_Lean_Elab_throwAbortCommand___redArg,
    runtime_initialize_Lean_Elab_Exception,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_allImportedModuleNames,
    l_Lean_Environment_contains, l_Lean_Environment_evalConst___redArg,
    l_Lean_Environment_evalConstCheck___redArg, l_Lean_Environment_find_x3f,
    l_Lean_Environment_findAsync_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_unlockAsync,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_ofExcept___redArg, l_Lean_throwError___redArg, l_Lean_throwUnknownConstant___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_isProp, l_Lean_mkConst};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{initialize_Lean_Log, runtime_initialize_Lean_Log};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
pub static l_Lean_withEnv___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_withEnv___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withEnv___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withEnv___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value:
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
    m_fun: l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_withoutModifyingEnv_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
    };
static mut l_Lean_isInductiveCore_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__1_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 105, 115, 73, 110, 100, 117, 99, 116, 105, 118, 101, 67, 111,
            114, 101, 63, 0,
        ],
    };
static mut l_Lean_isInductiveCore_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_isInductiveCore_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_isInductiveCore_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isInductiveCore_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 68, 101, 102, 110, 63, 0],
};
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isRec_x3f___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0],
};
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isRec_x3f___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value:
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
    m_fun: l_Lean_mkLevelParam as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value:
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105,
        111, 110, 0,
    ],
};
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value:
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105,
        118, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_evalConst___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_stringToMessageData as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_evalConst___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_evalConst___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_setEnv___redArg___lam__0(
    mut v_env_1353_: *mut crate::leanh::LeanObject,
    mut v_x_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_env_1353_);
    return v_env_1353_;
}
pub unsafe fn l_Lean_setEnv___redArg___lam__0___boxed(
    mut v_env_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1357_ = l_Lean_setEnv___redArg___lam__0(v_env_1355_, v_x_1356_);
    crate::leanh::lean_dec_ref(v_x_1356_);
    crate::leanh::lean_dec_ref(v_env_1355_);
    return v_res_1357_;
}
pub unsafe fn l_Lean_setEnv___redArg(
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_env_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_1360_ = crate::leanh::lean_ctor_get(v_inst_1358_, 1);
    crate::leanh::lean_inc(v_modifyEnv_1360_);
    crate::leanh::lean_dec_ref(v_inst_1358_);
    v___f_1361_ = crate::leanh::lean_alloc_closure(
        l_Lean_setEnv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1361_, 0, v_env_1359_);
    v___x_1362_ = crate::leanh::lean_apply_1(v_modifyEnv_1360_, v___f_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lean_setEnv(
    mut v_m_1363_: *mut crate::leanh::LeanObject,
    mut v_inst_1364_: *mut crate::leanh::LeanObject,
    mut v_env_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_setEnv___redArg(v_inst_1364_, v_env_1365_);
    return v___x_1366_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0(
    mut v_x_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1368_ = crate::leanh::lean_ctor_get(v_x_1367_, 0);
    crate::leanh::lean_inc(v_fst_1368_);
    return v_fst_1368_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0___boxed(
    mut v_x_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_withEnv___redArg___lam__0(v_x_1369_);
    crate::leanh::lean_dec_ref(v_x_1369_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1(
    mut v_x_1371_: *mut crate::leanh::LeanObject,
    mut v_____r_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1371_);
    return v_x_1371_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1___boxed(
    mut v_x_1373_: *mut crate::leanh::LeanObject,
    mut v_____r_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_withEnv___redArg___lam__1(v_x_1373_, v_____r_1374_);
    crate::leanh::lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2(
    mut v___x_1376_: *mut crate::leanh::LeanObject,
    mut v_x_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_1376_);
    return v___x_1376_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2___boxed(
    mut v___x_1378_: *mut crate::leanh::LeanObject,
    mut v_x_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1380_ = l_Lean_withEnv___redArg___lam__2(v___x_1378_, v_x_1379_);
    crate::leanh::lean_dec(v_x_1379_);
    crate::leanh::lean_dec(v___x_1378_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__3(
    mut v_toFunctor_1381_: *mut crate::leanh::LeanObject,
    mut v_inst_1382_: *mut crate::leanh::LeanObject,
    mut v_env_1383_: *mut crate::leanh::LeanObject,
    mut v_toBind_1384_: *mut crate::leanh::LeanObject,
    mut v___f_1385_: *mut crate::leanh::LeanObject,
    mut v_inst_1386_: *mut crate::leanh::LeanObject,
    mut v___f_1387_: *mut crate::leanh::LeanObject,
    mut v_saved_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1389_ = crate::leanh::lean_ctor_get(v_toFunctor_1381_, 0);
    crate::leanh::lean_inc(v_map_1389_);
    crate::leanh::lean_dec_ref(v_toFunctor_1381_);
    crate::leanh::lean_inc_ref(v_inst_1382_);
    v___x_1390_ = l_Lean_setEnv___redArg(v_inst_1382_, v_env_1383_);
    v___x_1391_ = crate::leanh::lean_apply_4(
        v_toBind_1384_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1390_,
        v___f_1385_,
    );
    v___x_1392_ = l_Lean_setEnv___redArg(v_inst_1382_, v_saved_1388_);
    v___f_1393_ = crate::leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1393_, 0, v___x_1392_);
    v_y_1394_ = crate::leanh::lean_apply_4(
        v_inst_1386_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1391_,
        v___f_1393_,
    );
    v___x_1395_ = crate::leanh::lean_apply_4(
        v_map_1389_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1387_,
        v_y_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Lean_withEnv___redArg(
    mut v_inst_1397_: *mut crate::leanh::LeanObject,
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_inst_1399_: *mut crate::leanh::LeanObject,
    mut v_env_1400_: *mut crate::leanh::LeanObject,
    mut v_x_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1402_ = crate::leanh::lean_ctor_get(v_inst_1397_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1402_);
    v_toBind_1403_ = crate::leanh::lean_ctor_get(v_inst_1397_, 1);
    crate::leanh::lean_inc_n(v_toBind_1403_, 2);
    crate::leanh::lean_dec_ref(v_inst_1397_);
    v_getEnv_1404_ = crate::leanh::lean_ctor_get(v_inst_1399_, 0);
    crate::leanh::lean_inc(v_getEnv_1404_);
    v_toFunctor_1405_ = crate::leanh::lean_ctor_get(v_toApplicative_1402_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1405_);
    crate::leanh::lean_dec_ref(v_toApplicative_1402_);
    v___f_1406_ = l_Lean_withEnv___redArg___closed__0;
    v___f_1407_ = crate::leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1407_, 0, v_x_1401_);
    v___f_1408_ = crate::leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1408_, 0, v_toFunctor_1405_);
    crate::leanh::lean_closure_set(v___f_1408_, 1, v_inst_1399_);
    crate::leanh::lean_closure_set(v___f_1408_, 2, v_env_1400_);
    crate::leanh::lean_closure_set(v___f_1408_, 3, v_toBind_1403_);
    crate::leanh::lean_closure_set(v___f_1408_, 4, v___f_1407_);
    crate::leanh::lean_closure_set(v___f_1408_, 5, v_inst_1398_);
    crate::leanh::lean_closure_set(v___f_1408_, 6, v___f_1406_);
    v___x_1409_ = crate::leanh::lean_apply_4(
        v_toBind_1403_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1404_,
        v___f_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lean_withEnv(
    mut v_m_1410_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1411_: *mut crate::leanh::LeanObject,
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
    mut v_inst_1413_: *mut crate::leanh::LeanObject,
    mut v_inst_1414_: *mut crate::leanh::LeanObject,
    mut v_env_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_withEnv___redArg(
        v_inst_1412_,
        v_inst_1413_,
        v_inst_1414_,
        v_env_1415_,
        v_x_1416_,
    );
    return v___x_1417_;
}
pub unsafe fn l_Lean_isInductiveCore(
    mut v_env_1418_: *mut crate::leanh::LeanObject,
    mut v_declName_1419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = 0;
    v___x_1421_ = l_Lean_Environment_findAsync_x3f(v_env_1418_, v_declName_1419_, v___x_1420_);
    if crate::leanh::lean_obj_tag(v___x_1421_) == 1 {
        let mut v_val_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_1423_: u8 = 0;
        v_val_1422_ = crate::leanh::lean_ctor_get(v___x_1421_, 0);
        crate::leanh::lean_inc(v_val_1422_);
        crate::leanh::lean_dec_ref_known(v___x_1421_, 1);
        v_kind_1423_ = crate::leanh::lean_ctor_get_uint8(
            v_val_1422_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        crate::leanh::lean_dec(v_val_1422_);
        if v_kind_1423_ == 5 {
            let mut v___x_1424_: u8 = 0;
            v___x_1424_ = 1;
            return v___x_1424_;
        } else {
            return v___x_1420_;
        }
    } else {
        crate::leanh::lean_dec(v___x_1421_);
        return v___x_1420_;
    }
}
pub unsafe fn l_Lean_isInductiveCore___boxed(
    mut v_env_1425_: *mut crate::leanh::LeanObject,
    mut v_declName_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_isInductiveCore(v_env_1425_, v_declName_1426_);
    v_r_1428_ = crate::leanh::lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Lean_isInductive___redArg___lam__0(
    mut v_declName_1429_: *mut crate::leanh::LeanObject,
    mut v_toPure_1430_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Lean_isInductiveCore(v_____do__lift_1431_, v_declName_1429_);
    v___x_1433_ = crate::leanh::lean_box((v___x_1432_) as usize);
    v___x_1434_ =
        crate::leanh::lean_apply_2(v_toPure_1430_, crate::leanh::lean_box(0), v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Lean_isInductive___redArg(
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_inst_1436_: *mut crate::leanh::LeanObject,
    mut v_declName_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1438_ = crate::leanh::lean_ctor_get(v_inst_1435_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1438_);
    v_toBind_1439_ = crate::leanh::lean_ctor_get(v_inst_1435_, 1);
    crate::leanh::lean_inc(v_toBind_1439_);
    crate::leanh::lean_dec_ref(v_inst_1435_);
    v_getEnv_1440_ = crate::leanh::lean_ctor_get(v_inst_1436_, 0);
    crate::leanh::lean_inc(v_getEnv_1440_);
    crate::leanh::lean_dec_ref(v_inst_1436_);
    v_toPure_1441_ = crate::leanh::lean_ctor_get(v_toApplicative_1438_, 1);
    crate::leanh::lean_inc(v_toPure_1441_);
    crate::leanh::lean_dec_ref(v_toApplicative_1438_);
    v___f_1442_ = crate::leanh::lean_alloc_closure(
        l_Lean_isInductive___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1442_, 0, v_declName_1437_);
    crate::leanh::lean_closure_set(v___f_1442_, 1, v_toPure_1441_);
    v___x_1443_ = crate::leanh::lean_apply_4(
        v_toBind_1439_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1440_,
        v___f_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l_Lean_isInductive(
    mut v_m_1444_: *mut crate::leanh::LeanObject,
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
    mut v_declName_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_isInductive___redArg(v_inst_1445_, v_inst_1446_, v_declName_1447_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_isRecCore(
    mut v_env_1449_: *mut crate::leanh::LeanObject,
    mut v_declName_1450_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = 0;
    v___x_1452_ = l_Lean_Environment_findAsync_x3f(v_env_1449_, v_declName_1450_, v___x_1451_);
    if crate::leanh::lean_obj_tag(v___x_1452_) == 1 {
        let mut v_val_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_1454_: u8 = 0;
        v_val_1453_ = crate::leanh::lean_ctor_get(v___x_1452_, 0);
        crate::leanh::lean_inc(v_val_1453_);
        crate::leanh::lean_dec_ref_known(v___x_1452_, 1);
        v_kind_1454_ = crate::leanh::lean_ctor_get_uint8(
            v_val_1453_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        crate::leanh::lean_dec(v_val_1453_);
        if v_kind_1454_ == 7 {
            let mut v___x_1455_: u8 = 0;
            v___x_1455_ = 1;
            return v___x_1455_;
        } else {
            return v___x_1451_;
        }
    } else {
        crate::leanh::lean_dec(v___x_1452_);
        return v___x_1451_;
    }
}
pub unsafe fn l_Lean_isRecCore___boxed(
    mut v_env_1456_: *mut crate::leanh::LeanObject,
    mut v_declName_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_isRecCore(v_env_1456_, v_declName_1457_);
    v_r_1459_ = crate::leanh::lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Lean_isRec___redArg___lam__0(
    mut v_declName_1460_: *mut crate::leanh::LeanObject,
    mut v_toPure_1461_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_isRecCore(v_____do__lift_1462_, v_declName_1460_);
    v___x_1464_ = crate::leanh::lean_box((v___x_1463_) as usize);
    v___x_1465_ =
        crate::leanh::lean_apply_2(v_toPure_1461_, crate::leanh::lean_box(0), v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_isRec___redArg(
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v_inst_1467_: *mut crate::leanh::LeanObject,
    mut v_declName_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1469_ = crate::leanh::lean_ctor_get(v_inst_1466_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1469_);
    v_toBind_1470_ = crate::leanh::lean_ctor_get(v_inst_1466_, 1);
    crate::leanh::lean_inc(v_toBind_1470_);
    crate::leanh::lean_dec_ref(v_inst_1466_);
    v_getEnv_1471_ = crate::leanh::lean_ctor_get(v_inst_1467_, 0);
    crate::leanh::lean_inc(v_getEnv_1471_);
    crate::leanh::lean_dec_ref(v_inst_1467_);
    v_toPure_1472_ = crate::leanh::lean_ctor_get(v_toApplicative_1469_, 1);
    crate::leanh::lean_inc(v_toPure_1472_);
    crate::leanh::lean_dec_ref(v_toApplicative_1469_);
    v___f_1473_ = crate::leanh::lean_alloc_closure(
        l_Lean_isRec___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1473_, 0, v_declName_1468_);
    crate::leanh::lean_closure_set(v___f_1473_, 1, v_toPure_1472_);
    v___x_1474_ = crate::leanh::lean_apply_4(
        v_toBind_1470_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1471_,
        v___f_1473_,
    );
    return v___x_1474_;
}
pub unsafe fn l_Lean_isRec(
    mut v_m_1475_: *mut crate::leanh::LeanObject,
    mut v_inst_1476_: *mut crate::leanh::LeanObject,
    mut v_inst_1477_: *mut crate::leanh::LeanObject,
    mut v_declName_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_isRec___redArg(v_inst_1476_, v_inst_1477_, v_declName_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_withoutModifyingEnv___redArg___lam__0(
    mut v_inst_1480_: *mut crate::leanh::LeanObject,
    mut v_inst_1481_: *mut crate::leanh::LeanObject,
    mut v_inst_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = l_Lean_Environment_unlockAsync(v_____do__lift_1484_);
    v___x_1486_ = l_Lean_withEnv___redArg(
        v_inst_1480_,
        v_inst_1481_,
        v_inst_1482_,
        v___x_1485_,
        v_x_1483_,
    );
    return v___x_1486_;
}
pub unsafe fn l_Lean_withoutModifyingEnv___redArg(
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
    mut v_inst_1488_: *mut crate::leanh::LeanObject,
    mut v_inst_1489_: *mut crate::leanh::LeanObject,
    mut v_x_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1491_ = crate::leanh::lean_ctor_get(v_inst_1487_, 1);
    crate::leanh::lean_inc(v_toBind_1491_);
    v_getEnv_1492_ = crate::leanh::lean_ctor_get(v_inst_1488_, 0);
    crate::leanh::lean_inc(v_getEnv_1492_);
    v___f_1493_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1493_, 0, v_inst_1487_);
    crate::leanh::lean_closure_set(v___f_1493_, 1, v_inst_1489_);
    crate::leanh::lean_closure_set(v___f_1493_, 2, v_inst_1488_);
    crate::leanh::lean_closure_set(v___f_1493_, 3, v_x_1490_);
    v___x_1494_ = crate::leanh::lean_apply_4(
        v_toBind_1491_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1492_,
        v___f_1493_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_withoutModifyingEnv(
    mut v_m_1495_: *mut crate::leanh::LeanObject,
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_inst_1497_: *mut crate::leanh::LeanObject,
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1501_ = crate::leanh::lean_ctor_get(v_inst_1496_, 1);
    crate::leanh::lean_inc(v_toBind_1501_);
    v_getEnv_1502_ = crate::leanh::lean_ctor_get(v_inst_1497_, 0);
    crate::leanh::lean_inc(v_getEnv_1502_);
    v___f_1503_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1503_, 0, v_inst_1496_);
    crate::leanh::lean_closure_set(v___f_1503_, 1, v_inst_1498_);
    crate::leanh::lean_closure_set(v___f_1503_, 2, v_inst_1497_);
    crate::leanh::lean_closure_set(v___f_1503_, 3, v_x_1500_);
    v___x_1504_ = crate::leanh::lean_apply_4(
        v_toBind_1501_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1502_,
        v___f_1503_,
    );
    return v___x_1504_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0(
    mut v_x_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1506_ = crate::leanh::lean_ctor_get(v_x_1505_, 0);
    crate::leanh::lean_inc(v_fst_1506_);
    return v_fst_1506_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(
    mut v_x_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(v_x_1507_);
    crate::leanh::lean_dec_ref(v_x_1507_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__1(
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_toPure_1510_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1512_, 0, v_a_1509_);
    crate::leanh::lean_ctor_set(v___x_1512_, 1, v_____do__lift_1511_);
    v___x_1513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    v___x_1514_ =
        crate::leanh::lean_apply_2(v_toPure_1510_, crate::leanh::lean_box(0), v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__2(
    mut v_toPure_1515_: *mut crate::leanh::LeanObject,
    mut v_toBind_1516_: *mut crate::leanh::LeanObject,
    mut v_getEnv_1517_: *mut crate::leanh::LeanObject,
    mut v_a_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1519_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1519_, 0, v_a_1518_);
    crate::leanh::lean_closure_set(v___f_1519_, 1, v_toPure_1515_);
    v___x_1520_ = crate::leanh::lean_apply_4(
        v_toBind_1516_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1517_,
        v___f_1519_,
    );
    return v___x_1520_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__3(
    mut v_toPure_1521_: *mut crate::leanh::LeanObject,
    mut v_e_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1523_ = crate::leanh::lean_ctor_get(v_e_1522_, 0);
    crate::leanh::lean_inc(v_a_1523_);
    crate::leanh::lean_dec_ref(v_e_1522_);
    v___x_1524_ = crate::leanh::lean_apply_2(v_toPure_1521_, crate::leanh::lean_box(0), v_a_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4(
    mut v___x_1525_: *mut crate::leanh::LeanObject,
    mut v_x_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_1525_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(
    mut v___x_1527_: *mut crate::leanh::LeanObject,
    mut v_x_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(v___x_1527_, v_x_1528_);
    crate::leanh::lean_dec(v_x_1528_);
    crate::leanh::lean_dec(v___x_1527_);
    return v_res_1529_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__5(
    mut v_toFunctor_1530_: *mut crate::leanh::LeanObject,
    mut v_toBind_1531_: *mut crate::leanh::LeanObject,
    mut v_x_1532_: *mut crate::leanh::LeanObject,
    mut v___f_1533_: *mut crate::leanh::LeanObject,
    mut v_inst_1534_: *mut crate::leanh::LeanObject,
    mut v_inst_1535_: *mut crate::leanh::LeanObject,
    mut v___f_1536_: *mut crate::leanh::LeanObject,
    mut v___f_1537_: *mut crate::leanh::LeanObject,
    mut v_env_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1539_ = crate::leanh::lean_ctor_get(v_toFunctor_1530_, 0);
    crate::leanh::lean_inc(v_map_1539_);
    crate::leanh::lean_dec_ref(v_toFunctor_1530_);
    crate::leanh::lean_inc(v_toBind_1531_);
    v___x_1540_ = crate::leanh::lean_apply_4(
        v_toBind_1531_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_1532_,
        v___f_1533_,
    );
    v___x_1541_ = l_Lean_setEnv___redArg(v_inst_1534_, v_env_1538_);
    v___f_1542_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1542_, 0, v___x_1541_);
    v_y_1543_ = crate::leanh::lean_apply_4(
        v_inst_1535_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1540_,
        v___f_1542_,
    );
    v___x_1544_ = crate::leanh::lean_apply_4(
        v_map_1539_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1536_,
        v_y_1543_,
    );
    v___x_1545_ = crate::leanh::lean_apply_4(
        v_toBind_1531_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1544_,
        v___f_1537_,
    );
    return v___x_1545_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg(
    mut v_inst_1547_: *mut crate::leanh::LeanObject,
    mut v_inst_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
    mut v_x_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1551_ = crate::leanh::lean_ctor_get(v_inst_1547_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1551_);
    v_toBind_1552_ = crate::leanh::lean_ctor_get(v_inst_1547_, 1);
    crate::leanh::lean_inc_n(v_toBind_1552_, 3);
    crate::leanh::lean_dec_ref(v_inst_1547_);
    v_getEnv_1553_ = crate::leanh::lean_ctor_get(v_inst_1548_, 0);
    crate::leanh::lean_inc_n(v_getEnv_1553_, 2);
    v_toFunctor_1554_ = crate::leanh::lean_ctor_get(v_toApplicative_1551_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1554_);
    v_toPure_1555_ = crate::leanh::lean_ctor_get(v_toApplicative_1551_, 1);
    crate::leanh::lean_inc_n(v_toPure_1555_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1551_);
    v___f_1556_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1557_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1557_, 0, v_toPure_1555_);
    crate::leanh::lean_closure_set(v___f_1557_, 1, v_toBind_1552_);
    crate::leanh::lean_closure_set(v___f_1557_, 2, v_getEnv_1553_);
    v___f_1558_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1558_, 0, v_toPure_1555_);
    v___f_1559_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1559_, 0, v_toFunctor_1554_);
    crate::leanh::lean_closure_set(v___f_1559_, 1, v_toBind_1552_);
    crate::leanh::lean_closure_set(v___f_1559_, 2, v_x_1550_);
    crate::leanh::lean_closure_set(v___f_1559_, 3, v___f_1557_);
    crate::leanh::lean_closure_set(v___f_1559_, 4, v_inst_1548_);
    crate::leanh::lean_closure_set(v___f_1559_, 5, v_inst_1549_);
    crate::leanh::lean_closure_set(v___f_1559_, 6, v___f_1556_);
    crate::leanh::lean_closure_set(v___f_1559_, 7, v___f_1558_);
    v___x_1560_ = crate::leanh::lean_apply_4(
        v_toBind_1552_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1553_,
        v___f_1559_,
    );
    return v___x_1560_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27(
    mut v_m_1561_: *mut crate::leanh::LeanObject,
    mut v_inst_1562_: *mut crate::leanh::LeanObject,
    mut v_inst_1563_: *mut crate::leanh::LeanObject,
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1565_: *mut crate::leanh::LeanObject,
    mut v_x_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1567_ = crate::leanh::lean_ctor_get(v_inst_1562_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1567_);
    v_toBind_1568_ = crate::leanh::lean_ctor_get(v_inst_1562_, 1);
    crate::leanh::lean_inc_n(v_toBind_1568_, 3);
    crate::leanh::lean_dec_ref(v_inst_1562_);
    v_getEnv_1569_ = crate::leanh::lean_ctor_get(v_inst_1563_, 0);
    crate::leanh::lean_inc_n(v_getEnv_1569_, 2);
    v_toFunctor_1570_ = crate::leanh::lean_ctor_get(v_toApplicative_1567_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1570_);
    v_toPure_1571_ = crate::leanh::lean_ctor_get(v_toApplicative_1567_, 1);
    crate::leanh::lean_inc_n(v_toPure_1571_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1567_);
    v___f_1572_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1573_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1573_, 0, v_toPure_1571_);
    crate::leanh::lean_closure_set(v___f_1573_, 1, v_toBind_1568_);
    crate::leanh::lean_closure_set(v___f_1573_, 2, v_getEnv_1569_);
    v___f_1574_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1574_, 0, v_toPure_1571_);
    v___f_1575_ = crate::leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1575_, 0, v_toFunctor_1570_);
    crate::leanh::lean_closure_set(v___f_1575_, 1, v_toBind_1568_);
    crate::leanh::lean_closure_set(v___f_1575_, 2, v_x_1566_);
    crate::leanh::lean_closure_set(v___f_1575_, 3, v___f_1573_);
    crate::leanh::lean_closure_set(v___f_1575_, 4, v_inst_1563_);
    crate::leanh::lean_closure_set(v___f_1575_, 5, v_inst_1564_);
    crate::leanh::lean_closure_set(v___f_1575_, 6, v___f_1572_);
    crate::leanh::lean_closure_set(v___f_1575_, 7, v___f_1574_);
    v___x_1576_ = crate::leanh::lean_apply_4(
        v_toBind_1568_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1569_,
        v___f_1575_,
    );
    return v___x_1576_;
}
pub unsafe fn l_Lean_matchConst___redArg___lam__0(
    mut v_declName_1577_: *mut crate::leanh::LeanObject,
    mut v_failK_1578_: *mut crate::leanh::LeanObject,
    mut v_k_1579_: *mut crate::leanh::LeanObject,
    mut v_us_1580_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1582_ = 0;
    v___x_1583_ = l_Lean_Environment_find_x3f(v_____do__lift_1581_, v_declName_1577_, v___x_1582_);
    if crate::leanh::lean_obj_tag(v___x_1583_) == 0 {
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_us_1580_);
        crate::leanh::lean_dec(v_k_1579_);
        v___x_1584_ = crate::leanh::lean_box(0);
        v___x_1585_ = crate::leanh::lean_apply_1(v_failK_1578_, v___x_1584_);
        return v___x_1585_;
    } else {
        let mut v_val_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_failK_1578_);
        v_val_1586_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
        crate::leanh::lean_inc(v_val_1586_);
        crate::leanh::lean_dec_ref_known(v___x_1583_, 1);
        v___x_1587_ = crate::leanh::lean_apply_2(v_k_1579_, v_val_1586_, v_us_1580_);
        return v___x_1587_;
    }
}
pub unsafe fn l_Lean_matchConst___redArg(
    mut v_inst_1588_: *mut crate::leanh::LeanObject,
    mut v_inst_1589_: *mut crate::leanh::LeanObject,
    mut v_e_1590_: *mut crate::leanh::LeanObject,
    mut v_failK_1591_: *mut crate::leanh::LeanObject,
    mut v_k_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1590_) == 4 {
        let mut v_toBind_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1593_ = crate::leanh::lean_ctor_get(v_inst_1588_, 1);
        crate::leanh::lean_inc(v_toBind_1593_);
        crate::leanh::lean_dec_ref(v_inst_1588_);
        v_declName_1594_ = crate::leanh::lean_ctor_get(v_e_1590_, 0);
        crate::leanh::lean_inc(v_declName_1594_);
        v_us_1595_ = crate::leanh::lean_ctor_get(v_e_1590_, 1);
        crate::leanh::lean_inc(v_us_1595_);
        crate::leanh::lean_dec_ref_known(v_e_1590_, 2);
        v_getEnv_1596_ = crate::leanh::lean_ctor_get(v_inst_1589_, 0);
        crate::leanh::lean_inc(v_getEnv_1596_);
        crate::leanh::lean_dec_ref(v_inst_1589_);
        v___f_1597_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1597_, 0, v_declName_1594_);
        crate::leanh::lean_closure_set(v___f_1597_, 1, v_failK_1591_);
        crate::leanh::lean_closure_set(v___f_1597_, 2, v_k_1592_);
        crate::leanh::lean_closure_set(v___f_1597_, 3, v_us_1595_);
        v___x_1598_ = crate::leanh::lean_apply_4(
            v_toBind_1593_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1596_,
            v___f_1597_,
        );
        return v___x_1598_;
    } else {
        let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1592_);
        crate::leanh::lean_dec_ref(v_e_1590_);
        crate::leanh::lean_dec_ref(v_inst_1589_);
        crate::leanh::lean_dec_ref(v_inst_1588_);
        v___x_1599_ = crate::leanh::lean_box(0);
        v___x_1600_ = crate::leanh::lean_apply_1(v_failK_1591_, v___x_1599_);
        return v___x_1600_;
    }
}
pub unsafe fn l_Lean_matchConst(
    mut v_m_1601_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1602_: *mut crate::leanh::LeanObject,
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
    mut v_inst_1604_: *mut crate::leanh::LeanObject,
    mut v_e_1605_: *mut crate::leanh::LeanObject,
    mut v_failK_1606_: *mut crate::leanh::LeanObject,
    mut v_k_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1605_) == 4 {
        let mut v_toBind_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1608_ = crate::leanh::lean_ctor_get(v_inst_1603_, 1);
        crate::leanh::lean_inc(v_toBind_1608_);
        crate::leanh::lean_dec_ref(v_inst_1603_);
        v_declName_1609_ = crate::leanh::lean_ctor_get(v_e_1605_, 0);
        crate::leanh::lean_inc(v_declName_1609_);
        v_us_1610_ = crate::leanh::lean_ctor_get(v_e_1605_, 1);
        crate::leanh::lean_inc(v_us_1610_);
        crate::leanh::lean_dec_ref_known(v_e_1605_, 2);
        v_getEnv_1611_ = crate::leanh::lean_ctor_get(v_inst_1604_, 0);
        crate::leanh::lean_inc(v_getEnv_1611_);
        crate::leanh::lean_dec_ref(v_inst_1604_);
        v___f_1612_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1612_, 0, v_declName_1609_);
        crate::leanh::lean_closure_set(v___f_1612_, 1, v_failK_1606_);
        crate::leanh::lean_closure_set(v___f_1612_, 2, v_k_1607_);
        crate::leanh::lean_closure_set(v___f_1612_, 3, v_us_1610_);
        v___x_1613_ = crate::leanh::lean_apply_4(
            v_toBind_1608_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1611_,
            v___f_1612_,
        );
        return v___x_1613_;
    } else {
        let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1607_);
        crate::leanh::lean_dec_ref(v_e_1605_);
        crate::leanh::lean_dec_ref(v_inst_1604_);
        crate::leanh::lean_dec_ref(v_inst_1603_);
        v___x_1614_ = crate::leanh::lean_box(0);
        v___x_1615_ = crate::leanh::lean_apply_1(v_failK_1606_, v___x_1614_);
        return v___x_1615_;
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg___lam__0(
    mut v_declName_1616_: *mut crate::leanh::LeanObject,
    mut v_failK_1617_: *mut crate::leanh::LeanObject,
    mut v_k_1618_: *mut crate::leanh::LeanObject,
    mut v_us_1619_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = 0;
    v___x_1622_ = l_Lean_Environment_find_x3f(v_____do__lift_1620_, v_declName_1616_, v___x_1621_);
    if crate::leanh::lean_obj_tag(v___x_1622_) == 0 {
        let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_us_1619_);
        crate::leanh::lean_dec(v_k_1618_);
        v___x_1623_ = crate::leanh::lean_box(0);
        v___x_1624_ = crate::leanh::lean_apply_1(v_failK_1617_, v___x_1623_);
        return v___x_1624_;
    } else {
        let mut v_val_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1625_ = crate::leanh::lean_ctor_get(v___x_1622_, 0);
        crate::leanh::lean_inc(v_val_1625_);
        crate::leanh::lean_dec_ref_known(v___x_1622_, 1);
        if crate::leanh::lean_obj_tag(v_val_1625_) == 5 {
            let mut v_val_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_failK_1617_);
            v_val_1626_ = crate::leanh::lean_ctor_get(v_val_1625_, 0);
            crate::leanh::lean_inc_ref(v_val_1626_);
            crate::leanh::lean_dec_ref_known(v_val_1625_, 1);
            v___x_1627_ = crate::leanh::lean_apply_2(v_k_1618_, v_val_1626_, v_us_1619_);
            return v___x_1627_;
        } else {
            let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_1625_);
            crate::leanh::lean_dec(v_us_1619_);
            crate::leanh::lean_dec(v_k_1618_);
            v___x_1628_ = crate::leanh::lean_box(0);
            v___x_1629_ = crate::leanh::lean_apply_1(v_failK_1617_, v___x_1628_);
            return v___x_1629_;
        }
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg(
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_inst_1631_: *mut crate::leanh::LeanObject,
    mut v_e_1632_: *mut crate::leanh::LeanObject,
    mut v_failK_1633_: *mut crate::leanh::LeanObject,
    mut v_k_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1632_) == 4 {
        let mut v_toBind_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1635_ = crate::leanh::lean_ctor_get(v_inst_1630_, 1);
        crate::leanh::lean_inc(v_toBind_1635_);
        crate::leanh::lean_dec_ref(v_inst_1630_);
        v_declName_1636_ = crate::leanh::lean_ctor_get(v_e_1632_, 0);
        crate::leanh::lean_inc(v_declName_1636_);
        v_us_1637_ = crate::leanh::lean_ctor_get(v_e_1632_, 1);
        crate::leanh::lean_inc(v_us_1637_);
        crate::leanh::lean_dec_ref_known(v_e_1632_, 2);
        v_getEnv_1638_ = crate::leanh::lean_ctor_get(v_inst_1631_, 0);
        crate::leanh::lean_inc(v_getEnv_1638_);
        crate::leanh::lean_dec_ref(v_inst_1631_);
        v___f_1639_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1639_, 0, v_declName_1636_);
        crate::leanh::lean_closure_set(v___f_1639_, 1, v_failK_1633_);
        crate::leanh::lean_closure_set(v___f_1639_, 2, v_k_1634_);
        crate::leanh::lean_closure_set(v___f_1639_, 3, v_us_1637_);
        v___x_1640_ = crate::leanh::lean_apply_4(
            v_toBind_1635_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1638_,
            v___f_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1634_);
        crate::leanh::lean_dec_ref(v_e_1632_);
        crate::leanh::lean_dec_ref(v_inst_1631_);
        crate::leanh::lean_dec_ref(v_inst_1630_);
        v___x_1641_ = crate::leanh::lean_box(0);
        v___x_1642_ = crate::leanh::lean_apply_1(v_failK_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l_Lean_matchConstInduct(
    mut v_m_1643_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1644_: *mut crate::leanh::LeanObject,
    mut v_inst_1645_: *mut crate::leanh::LeanObject,
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_e_1647_: *mut crate::leanh::LeanObject,
    mut v_failK_1648_: *mut crate::leanh::LeanObject,
    mut v_k_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1647_) == 4 {
        let mut v_toBind_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1650_ = crate::leanh::lean_ctor_get(v_inst_1645_, 1);
        crate::leanh::lean_inc(v_toBind_1650_);
        crate::leanh::lean_dec_ref(v_inst_1645_);
        v_declName_1651_ = crate::leanh::lean_ctor_get(v_e_1647_, 0);
        crate::leanh::lean_inc(v_declName_1651_);
        v_us_1652_ = crate::leanh::lean_ctor_get(v_e_1647_, 1);
        crate::leanh::lean_inc(v_us_1652_);
        crate::leanh::lean_dec_ref_known(v_e_1647_, 2);
        v_getEnv_1653_ = crate::leanh::lean_ctor_get(v_inst_1646_, 0);
        crate::leanh::lean_inc(v_getEnv_1653_);
        crate::leanh::lean_dec_ref(v_inst_1646_);
        v___f_1654_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1654_, 0, v_declName_1651_);
        crate::leanh::lean_closure_set(v___f_1654_, 1, v_failK_1648_);
        crate::leanh::lean_closure_set(v___f_1654_, 2, v_k_1649_);
        crate::leanh::lean_closure_set(v___f_1654_, 3, v_us_1652_);
        v___x_1655_ = crate::leanh::lean_apply_4(
            v_toBind_1650_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1653_,
            v___f_1654_,
        );
        return v___x_1655_;
    } else {
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1649_);
        crate::leanh::lean_dec_ref(v_e_1647_);
        crate::leanh::lean_dec_ref(v_inst_1646_);
        crate::leanh::lean_dec_ref(v_inst_1645_);
        v___x_1656_ = crate::leanh::lean_box(0);
        v___x_1657_ = crate::leanh::lean_apply_1(v_failK_1648_, v___x_1656_);
        return v___x_1657_;
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg___lam__0(
    mut v_declName_1658_: *mut crate::leanh::LeanObject,
    mut v_failK_1659_: *mut crate::leanh::LeanObject,
    mut v_k_1660_: *mut crate::leanh::LeanObject,
    mut v_us_1661_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = 0;
    v___x_1664_ = l_Lean_Environment_find_x3f(v_____do__lift_1662_, v_declName_1658_, v___x_1663_);
    if crate::leanh::lean_obj_tag(v___x_1664_) == 0 {
        let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_us_1661_);
        crate::leanh::lean_dec(v_k_1660_);
        v___x_1665_ = crate::leanh::lean_box(0);
        v___x_1666_ = crate::leanh::lean_apply_1(v_failK_1659_, v___x_1665_);
        return v___x_1666_;
    } else {
        let mut v_val_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1667_ = crate::leanh::lean_ctor_get(v___x_1664_, 0);
        crate::leanh::lean_inc(v_val_1667_);
        crate::leanh::lean_dec_ref_known(v___x_1664_, 1);
        if crate::leanh::lean_obj_tag(v_val_1667_) == 6 {
            let mut v_val_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_failK_1659_);
            v_val_1668_ = crate::leanh::lean_ctor_get(v_val_1667_, 0);
            crate::leanh::lean_inc_ref(v_val_1668_);
            crate::leanh::lean_dec_ref_known(v_val_1667_, 1);
            v___x_1669_ = crate::leanh::lean_apply_2(v_k_1660_, v_val_1668_, v_us_1661_);
            return v___x_1669_;
        } else {
            let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_1667_);
            crate::leanh::lean_dec(v_us_1661_);
            crate::leanh::lean_dec(v_k_1660_);
            v___x_1670_ = crate::leanh::lean_box(0);
            v___x_1671_ = crate::leanh::lean_apply_1(v_failK_1659_, v___x_1670_);
            return v___x_1671_;
        }
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg(
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_e_1674_: *mut crate::leanh::LeanObject,
    mut v_failK_1675_: *mut crate::leanh::LeanObject,
    mut v_k_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1674_) == 4 {
        let mut v_toBind_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1677_ = crate::leanh::lean_ctor_get(v_inst_1672_, 1);
        crate::leanh::lean_inc(v_toBind_1677_);
        crate::leanh::lean_dec_ref(v_inst_1672_);
        v_declName_1678_ = crate::leanh::lean_ctor_get(v_e_1674_, 0);
        crate::leanh::lean_inc(v_declName_1678_);
        v_us_1679_ = crate::leanh::lean_ctor_get(v_e_1674_, 1);
        crate::leanh::lean_inc(v_us_1679_);
        crate::leanh::lean_dec_ref_known(v_e_1674_, 2);
        v_getEnv_1680_ = crate::leanh::lean_ctor_get(v_inst_1673_, 0);
        crate::leanh::lean_inc(v_getEnv_1680_);
        crate::leanh::lean_dec_ref(v_inst_1673_);
        v___f_1681_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1681_, 0, v_declName_1678_);
        crate::leanh::lean_closure_set(v___f_1681_, 1, v_failK_1675_);
        crate::leanh::lean_closure_set(v___f_1681_, 2, v_k_1676_);
        crate::leanh::lean_closure_set(v___f_1681_, 3, v_us_1679_);
        v___x_1682_ = crate::leanh::lean_apply_4(
            v_toBind_1677_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1680_,
            v___f_1681_,
        );
        return v___x_1682_;
    } else {
        let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1676_);
        crate::leanh::lean_dec_ref(v_e_1674_);
        crate::leanh::lean_dec_ref(v_inst_1673_);
        crate::leanh::lean_dec_ref(v_inst_1672_);
        v___x_1683_ = crate::leanh::lean_box(0);
        v___x_1684_ = crate::leanh::lean_apply_1(v_failK_1675_, v___x_1683_);
        return v___x_1684_;
    }
}
pub unsafe fn l_Lean_matchConstCtor(
    mut v_m_1685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1686_: *mut crate::leanh::LeanObject,
    mut v_inst_1687_: *mut crate::leanh::LeanObject,
    mut v_inst_1688_: *mut crate::leanh::LeanObject,
    mut v_e_1689_: *mut crate::leanh::LeanObject,
    mut v_failK_1690_: *mut crate::leanh::LeanObject,
    mut v_k_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1689_) == 4 {
        let mut v_toBind_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1692_ = crate::leanh::lean_ctor_get(v_inst_1687_, 1);
        crate::leanh::lean_inc(v_toBind_1692_);
        crate::leanh::lean_dec_ref(v_inst_1687_);
        v_declName_1693_ = crate::leanh::lean_ctor_get(v_e_1689_, 0);
        crate::leanh::lean_inc(v_declName_1693_);
        v_us_1694_ = crate::leanh::lean_ctor_get(v_e_1689_, 1);
        crate::leanh::lean_inc(v_us_1694_);
        crate::leanh::lean_dec_ref_known(v_e_1689_, 2);
        v_getEnv_1695_ = crate::leanh::lean_ctor_get(v_inst_1688_, 0);
        crate::leanh::lean_inc(v_getEnv_1695_);
        crate::leanh::lean_dec_ref(v_inst_1688_);
        v___f_1696_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1696_, 0, v_declName_1693_);
        crate::leanh::lean_closure_set(v___f_1696_, 1, v_failK_1690_);
        crate::leanh::lean_closure_set(v___f_1696_, 2, v_k_1691_);
        crate::leanh::lean_closure_set(v___f_1696_, 3, v_us_1694_);
        v___x_1697_ = crate::leanh::lean_apply_4(
            v_toBind_1692_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1695_,
            v___f_1696_,
        );
        return v___x_1697_;
    } else {
        let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1691_);
        crate::leanh::lean_dec_ref(v_e_1689_);
        crate::leanh::lean_dec_ref(v_inst_1688_);
        crate::leanh::lean_dec_ref(v_inst_1687_);
        v___x_1698_ = crate::leanh::lean_box(0);
        v___x_1699_ = crate::leanh::lean_apply_1(v_failK_1690_, v___x_1698_);
        return v___x_1699_;
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg___lam__0(
    mut v_declName_1700_: *mut crate::leanh::LeanObject,
    mut v_failK_1701_: *mut crate::leanh::LeanObject,
    mut v_k_1702_: *mut crate::leanh::LeanObject,
    mut v_us_1703_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = 0;
    v___x_1706_ = l_Lean_Environment_find_x3f(v_____do__lift_1704_, v_declName_1700_, v___x_1705_);
    if crate::leanh::lean_obj_tag(v___x_1706_) == 0 {
        let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_us_1703_);
        crate::leanh::lean_dec(v_k_1702_);
        v___x_1707_ = crate::leanh::lean_box(0);
        v___x_1708_ = crate::leanh::lean_apply_1(v_failK_1701_, v___x_1707_);
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1709_ = crate::leanh::lean_ctor_get(v___x_1706_, 0);
        crate::leanh::lean_inc(v_val_1709_);
        crate::leanh::lean_dec_ref_known(v___x_1706_, 1);
        if crate::leanh::lean_obj_tag(v_val_1709_) == 7 {
            let mut v_val_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_failK_1701_);
            v_val_1710_ = crate::leanh::lean_ctor_get(v_val_1709_, 0);
            crate::leanh::lean_inc_ref(v_val_1710_);
            crate::leanh::lean_dec_ref_known(v_val_1709_, 1);
            v___x_1711_ = crate::leanh::lean_apply_2(v_k_1702_, v_val_1710_, v_us_1703_);
            return v___x_1711_;
        } else {
            let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_1709_);
            crate::leanh::lean_dec(v_us_1703_);
            crate::leanh::lean_dec(v_k_1702_);
            v___x_1712_ = crate::leanh::lean_box(0);
            v___x_1713_ = crate::leanh::lean_apply_1(v_failK_1701_, v___x_1712_);
            return v___x_1713_;
        }
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg(
    mut v_inst_1714_: *mut crate::leanh::LeanObject,
    mut v_inst_1715_: *mut crate::leanh::LeanObject,
    mut v_e_1716_: *mut crate::leanh::LeanObject,
    mut v_failK_1717_: *mut crate::leanh::LeanObject,
    mut v_k_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1716_) == 4 {
        let mut v_toBind_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1719_ = crate::leanh::lean_ctor_get(v_inst_1714_, 1);
        crate::leanh::lean_inc(v_toBind_1719_);
        crate::leanh::lean_dec_ref(v_inst_1714_);
        v_declName_1720_ = crate::leanh::lean_ctor_get(v_e_1716_, 0);
        crate::leanh::lean_inc(v_declName_1720_);
        v_us_1721_ = crate::leanh::lean_ctor_get(v_e_1716_, 1);
        crate::leanh::lean_inc(v_us_1721_);
        crate::leanh::lean_dec_ref_known(v_e_1716_, 2);
        v_getEnv_1722_ = crate::leanh::lean_ctor_get(v_inst_1715_, 0);
        crate::leanh::lean_inc(v_getEnv_1722_);
        crate::leanh::lean_dec_ref(v_inst_1715_);
        v___f_1723_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1723_, 0, v_declName_1720_);
        crate::leanh::lean_closure_set(v___f_1723_, 1, v_failK_1717_);
        crate::leanh::lean_closure_set(v___f_1723_, 2, v_k_1718_);
        crate::leanh::lean_closure_set(v___f_1723_, 3, v_us_1721_);
        v___x_1724_ = crate::leanh::lean_apply_4(
            v_toBind_1719_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1722_,
            v___f_1723_,
        );
        return v___x_1724_;
    } else {
        let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1718_);
        crate::leanh::lean_dec_ref(v_e_1716_);
        crate::leanh::lean_dec_ref(v_inst_1715_);
        crate::leanh::lean_dec_ref(v_inst_1714_);
        v___x_1725_ = crate::leanh::lean_box(0);
        v___x_1726_ = crate::leanh::lean_apply_1(v_failK_1717_, v___x_1725_);
        return v___x_1726_;
    }
}
pub unsafe fn l_Lean_matchConstRec(
    mut v_m_1727_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1728_: *mut crate::leanh::LeanObject,
    mut v_inst_1729_: *mut crate::leanh::LeanObject,
    mut v_inst_1730_: *mut crate::leanh::LeanObject,
    mut v_e_1731_: *mut crate::leanh::LeanObject,
    mut v_failK_1732_: *mut crate::leanh::LeanObject,
    mut v_k_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_1731_) == 4 {
        let mut v_toBind_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1734_ = crate::leanh::lean_ctor_get(v_inst_1729_, 1);
        crate::leanh::lean_inc(v_toBind_1734_);
        crate::leanh::lean_dec_ref(v_inst_1729_);
        v_declName_1735_ = crate::leanh::lean_ctor_get(v_e_1731_, 0);
        crate::leanh::lean_inc(v_declName_1735_);
        v_us_1736_ = crate::leanh::lean_ctor_get(v_e_1731_, 1);
        crate::leanh::lean_inc(v_us_1736_);
        crate::leanh::lean_dec_ref_known(v_e_1731_, 2);
        v_getEnv_1737_ = crate::leanh::lean_ctor_get(v_inst_1730_, 0);
        crate::leanh::lean_inc(v_getEnv_1737_);
        crate::leanh::lean_dec_ref(v_inst_1730_);
        v___f_1738_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1738_, 0, v_declName_1735_);
        crate::leanh::lean_closure_set(v___f_1738_, 1, v_failK_1732_);
        crate::leanh::lean_closure_set(v___f_1738_, 2, v_k_1733_);
        crate::leanh::lean_closure_set(v___f_1738_, 3, v_us_1736_);
        v___x_1739_ = crate::leanh::lean_apply_4(
            v_toBind_1734_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1737_,
            v___f_1738_,
        );
        return v___x_1739_;
    } else {
        let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1733_);
        crate::leanh::lean_dec_ref(v_e_1731_);
        crate::leanh::lean_dec_ref(v_inst_1730_);
        crate::leanh::lean_dec_ref(v_inst_1729_);
        v___x_1740_ = crate::leanh::lean_box(0);
        v___x_1741_ = crate::leanh::lean_apply_1(v_failK_1732_, v___x_1740_);
        return v___x_1741_;
    }
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0(
    mut v_constName_1742_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1743_: u8,
    mut v_toPure_1744_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ =
        l_Lean_Environment_contains(v_____do__lift_1745_, v_constName_1742_, v_skipRealize_1743_);
    v___x_1747_ = crate::leanh::lean_box((v___x_1746_) as usize);
    v___x_1748_ =
        crate::leanh::lean_apply_2(v_toPure_1744_, crate::leanh::lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0___boxed(
    mut v_constName_1749_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1750_: *mut crate::leanh::LeanObject,
    mut v_toPure_1751_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1753_: u8 = 0;
    let mut v_res_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1753_ = (crate::leanh::lean_unbox(v_skipRealize_1750_) as u8);
    v_res_1754_ = l_Lean_hasConst___redArg___lam__0(
        v_constName_1749_,
        v_skipRealize_boxed_1753_,
        v_toPure_1751_,
        v_____do__lift_1752_,
    );
    return v_res_1754_;
}
pub unsafe fn l_Lean_hasConst___redArg(
    mut v_inst_1755_: *mut crate::leanh::LeanObject,
    mut v_inst_1756_: *mut crate::leanh::LeanObject,
    mut v_constName_1757_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1758_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1759_ = crate::leanh::lean_ctor_get(v_inst_1755_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1759_);
    v_toBind_1760_ = crate::leanh::lean_ctor_get(v_inst_1755_, 1);
    crate::leanh::lean_inc(v_toBind_1760_);
    crate::leanh::lean_dec_ref(v_inst_1755_);
    v_getEnv_1761_ = crate::leanh::lean_ctor_get(v_inst_1756_, 0);
    crate::leanh::lean_inc(v_getEnv_1761_);
    crate::leanh::lean_dec_ref(v_inst_1756_);
    v_toPure_1762_ = crate::leanh::lean_ctor_get(v_toApplicative_1759_, 1);
    crate::leanh::lean_inc(v_toPure_1762_);
    crate::leanh::lean_dec_ref(v_toApplicative_1759_);
    v___x_1763_ = crate::leanh::lean_box((v_skipRealize_1758_) as usize);
    v___f_1764_ = crate::leanh::lean_alloc_closure(
        l_Lean_hasConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1764_, 0, v_constName_1757_);
    crate::leanh::lean_closure_set(v___f_1764_, 1, v___x_1763_);
    crate::leanh::lean_closure_set(v___f_1764_, 2, v_toPure_1762_);
    v___x_1765_ = crate::leanh::lean_apply_4(
        v_toBind_1760_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1761_,
        v___f_1764_,
    );
    return v___x_1765_;
}
pub unsafe fn l_Lean_hasConst___redArg___boxed(
    mut v_inst_1766_: *mut crate::leanh::LeanObject,
    mut v_inst_1767_: *mut crate::leanh::LeanObject,
    mut v_constName_1768_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1770_: u8 = 0;
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1770_ = (crate::leanh::lean_unbox(v_skipRealize_1769_) as u8);
    v_res_1771_ = l_Lean_hasConst___redArg(
        v_inst_1766_,
        v_inst_1767_,
        v_constName_1768_,
        v_skipRealize_boxed_1770_,
    );
    return v_res_1771_;
}
pub unsafe fn l_Lean_hasConst(
    mut v_m_1772_: *mut crate::leanh::LeanObject,
    mut v_inst_1773_: *mut crate::leanh::LeanObject,
    mut v_inst_1774_: *mut crate::leanh::LeanObject,
    mut v_constName_1775_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1776_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_hasConst___redArg(
        v_inst_1773_,
        v_inst_1774_,
        v_constName_1775_,
        v_skipRealize_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_hasConst___boxed(
    mut v_m_1778_: *mut crate::leanh::LeanObject,
    mut v_inst_1779_: *mut crate::leanh::LeanObject,
    mut v_inst_1780_: *mut crate::leanh::LeanObject,
    mut v_constName_1781_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1783_: u8 = 0;
    let mut v_res_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1783_ = (crate::leanh::lean_unbox(v_skipRealize_1782_) as u8);
    v_res_1784_ = l_Lean_hasConst(
        v_m_1778_,
        v_inst_1779_,
        v_inst_1780_,
        v_constName_1781_,
        v_skipRealize_boxed_1783_,
    );
    return v_res_1784_;
}
pub unsafe fn l_Lean_getConstInfo___redArg___lam__0(
    mut v_constName_1785_: *mut crate::leanh::LeanObject,
    mut v_inst_1786_: *mut crate::leanh::LeanObject,
    mut v_inst_1787_: *mut crate::leanh::LeanObject,
    mut v_inst_1788_: *mut crate::leanh::LeanObject,
    mut v_toPure_1789_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = 0;
    crate::leanh::lean_inc(v_constName_1785_);
    v___x_1792_ = l_Lean_Environment_find_x3f(v_____do__lift_1790_, v_constName_1785_, v___x_1791_);
    if crate::leanh::lean_obj_tag(v___x_1792_) == 0 {
        let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1789_);
        v___x_1793_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1786_,
            v_inst_1787_,
            v_inst_1788_,
            v_constName_1785_,
        );
        return v___x_1793_;
    } else {
        let mut v_val_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1788_);
        crate::leanh::lean_dec_ref(v_inst_1787_);
        crate::leanh::lean_dec_ref(v_inst_1786_);
        crate::leanh::lean_dec(v_constName_1785_);
        v_val_1794_ = crate::leanh::lean_ctor_get(v___x_1792_, 0);
        crate::leanh::lean_inc(v_val_1794_);
        crate::leanh::lean_dec_ref_known(v___x_1792_, 1);
        v___x_1795_ =
            crate::leanh::lean_apply_2(v_toPure_1789_, crate::leanh::lean_box(0), v_val_1794_);
        return v___x_1795_;
    }
}
pub unsafe fn l_Lean_getConstInfo___redArg(
    mut v_inst_1796_: *mut crate::leanh::LeanObject,
    mut v_inst_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_constName_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1800_ = crate::leanh::lean_ctor_get(v_inst_1796_, 0);
    v_toBind_1801_ = crate::leanh::lean_ctor_get(v_inst_1796_, 1);
    crate::leanh::lean_inc(v_toBind_1801_);
    v_getEnv_1802_ = crate::leanh::lean_ctor_get(v_inst_1797_, 0);
    crate::leanh::lean_inc(v_getEnv_1802_);
    v_toPure_1803_ = crate::leanh::lean_ctor_get(v_toApplicative_1800_, 1);
    crate::leanh::lean_inc(v_toPure_1803_);
    v___f_1804_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfo___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1804_, 0, v_constName_1799_);
    crate::leanh::lean_closure_set(v___f_1804_, 1, v_inst_1796_);
    crate::leanh::lean_closure_set(v___f_1804_, 2, v_inst_1797_);
    crate::leanh::lean_closure_set(v___f_1804_, 3, v_inst_1798_);
    crate::leanh::lean_closure_set(v___f_1804_, 4, v_toPure_1803_);
    v___x_1805_ = crate::leanh::lean_apply_4(
        v_toBind_1801_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1802_,
        v___f_1804_,
    );
    return v___x_1805_;
}
pub unsafe fn l_Lean_getConstInfo(
    mut v_m_1806_: *mut crate::leanh::LeanObject,
    mut v_inst_1807_: *mut crate::leanh::LeanObject,
    mut v_inst_1808_: *mut crate::leanh::LeanObject,
    mut v_inst_1809_: *mut crate::leanh::LeanObject,
    mut v_constName_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ =
        l_Lean_getConstInfo___redArg(v_inst_1807_, v_inst_1808_, v_inst_1809_, v_constName_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Lean_getConstVal___redArg___lam__0(
    mut v_constName_1812_: *mut crate::leanh::LeanObject,
    mut v_inst_1813_: *mut crate::leanh::LeanObject,
    mut v_inst_1814_: *mut crate::leanh::LeanObject,
    mut v_inst_1815_: *mut crate::leanh::LeanObject,
    mut v_toPure_1816_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = 0;
    crate::leanh::lean_inc(v_constName_1812_);
    v___x_1819_ =
        l_Lean_Environment_findConstVal_x3f(v_____do__lift_1817_, v_constName_1812_, v___x_1818_);
    if crate::leanh::lean_obj_tag(v___x_1819_) == 0 {
        let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1816_);
        v___x_1820_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1813_,
            v_inst_1814_,
            v_inst_1815_,
            v_constName_1812_,
        );
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1815_);
        crate::leanh::lean_dec_ref(v_inst_1814_);
        crate::leanh::lean_dec_ref(v_inst_1813_);
        crate::leanh::lean_dec(v_constName_1812_);
        v_val_1821_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
        crate::leanh::lean_inc(v_val_1821_);
        crate::leanh::lean_dec_ref_known(v___x_1819_, 1);
        v___x_1822_ =
            crate::leanh::lean_apply_2(v_toPure_1816_, crate::leanh::lean_box(0), v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l_Lean_getConstVal___redArg(
    mut v_inst_1823_: *mut crate::leanh::LeanObject,
    mut v_inst_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_1825_: *mut crate::leanh::LeanObject,
    mut v_constName_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1827_ = crate::leanh::lean_ctor_get(v_inst_1823_, 0);
    v_toBind_1828_ = crate::leanh::lean_ctor_get(v_inst_1823_, 1);
    crate::leanh::lean_inc(v_toBind_1828_);
    v_getEnv_1829_ = crate::leanh::lean_ctor_get(v_inst_1824_, 0);
    crate::leanh::lean_inc(v_getEnv_1829_);
    v_toPure_1830_ = crate::leanh::lean_ctor_get(v_toApplicative_1827_, 1);
    crate::leanh::lean_inc(v_toPure_1830_);
    v___f_1831_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstVal___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1831_, 0, v_constName_1826_);
    crate::leanh::lean_closure_set(v___f_1831_, 1, v_inst_1823_);
    crate::leanh::lean_closure_set(v___f_1831_, 2, v_inst_1824_);
    crate::leanh::lean_closure_set(v___f_1831_, 3, v_inst_1825_);
    crate::leanh::lean_closure_set(v___f_1831_, 4, v_toPure_1830_);
    v___x_1832_ = crate::leanh::lean_apply_4(
        v_toBind_1828_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1829_,
        v___f_1831_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Lean_getConstVal(
    mut v_m_1833_: *mut crate::leanh::LeanObject,
    mut v_inst_1834_: *mut crate::leanh::LeanObject,
    mut v_inst_1835_: *mut crate::leanh::LeanObject,
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_constName_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ =
        l_Lean_getConstVal___redArg(v_inst_1834_, v_inst_1835_, v_inst_1836_, v_constName_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0(
    mut v_constName_1839_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1840_: u8,
    mut v_inst_1841_: *mut crate::leanh::LeanObject,
    mut v_inst_1842_: *mut crate::leanh::LeanObject,
    mut v_inst_1843_: *mut crate::leanh::LeanObject,
    mut v_toPure_1844_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_constName_1839_);
    v___x_1846_ = l_Lean_Environment_findAsync_x3f(
        v_____do__lift_1845_,
        v_constName_1839_,
        v_skipRealize_1840_,
    );
    if crate::leanh::lean_obj_tag(v___x_1846_) == 0 {
        let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1844_);
        v___x_1847_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1841_,
            v_inst_1842_,
            v_inst_1843_,
            v_constName_1839_,
        );
        return v___x_1847_;
    } else {
        let mut v_val_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1843_);
        crate::leanh::lean_dec_ref(v_inst_1842_);
        crate::leanh::lean_dec_ref(v_inst_1841_);
        crate::leanh::lean_dec(v_constName_1839_);
        v_val_1848_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
        crate::leanh::lean_inc(v_val_1848_);
        crate::leanh::lean_dec_ref_known(v___x_1846_, 1);
        v___x_1849_ =
            crate::leanh::lean_apply_2(v_toPure_1844_, crate::leanh::lean_box(0), v_val_1848_);
        return v___x_1849_;
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(
    mut v_constName_1850_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1851_: *mut crate::leanh::LeanObject,
    mut v_inst_1852_: *mut crate::leanh::LeanObject,
    mut v_inst_1853_: *mut crate::leanh::LeanObject,
    mut v_inst_1854_: *mut crate::leanh::LeanObject,
    mut v_toPure_1855_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1857_: u8 = 0;
    let mut v_res_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1857_ = (crate::leanh::lean_unbox(v_skipRealize_1851_) as u8);
    v_res_1858_ = l_Lean_getAsyncConstInfo___redArg___lam__0(
        v_constName_1850_,
        v_skipRealize_boxed_1857_,
        v_inst_1852_,
        v_inst_1853_,
        v_inst_1854_,
        v_toPure_1855_,
        v_____do__lift_1856_,
    );
    return v_res_1858_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg(
    mut v_inst_1859_: *mut crate::leanh::LeanObject,
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_inst_1861_: *mut crate::leanh::LeanObject,
    mut v_constName_1862_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1863_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = crate::leanh::lean_ctor_get(v_inst_1859_, 0);
    v_toBind_1865_ = crate::leanh::lean_ctor_get(v_inst_1859_, 1);
    crate::leanh::lean_inc(v_toBind_1865_);
    v_getEnv_1866_ = crate::leanh::lean_ctor_get(v_inst_1860_, 0);
    crate::leanh::lean_inc(v_getEnv_1866_);
    v_toPure_1867_ = crate::leanh::lean_ctor_get(v_toApplicative_1864_, 1);
    crate::leanh::lean_inc(v_toPure_1867_);
    v___x_1868_ = crate::leanh::lean_box((v_skipRealize_1863_) as usize);
    v___f_1869_ = crate::leanh::lean_alloc_closure(
        l_Lean_getAsyncConstInfo___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1869_, 0, v_constName_1862_);
    crate::leanh::lean_closure_set(v___f_1869_, 1, v___x_1868_);
    crate::leanh::lean_closure_set(v___f_1869_, 2, v_inst_1859_);
    crate::leanh::lean_closure_set(v___f_1869_, 3, v_inst_1860_);
    crate::leanh::lean_closure_set(v___f_1869_, 4, v_inst_1861_);
    crate::leanh::lean_closure_set(v___f_1869_, 5, v_toPure_1867_);
    v___x_1870_ = crate::leanh::lean_apply_4(
        v_toBind_1865_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1866_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___boxed(
    mut v_inst_1871_: *mut crate::leanh::LeanObject,
    mut v_inst_1872_: *mut crate::leanh::LeanObject,
    mut v_inst_1873_: *mut crate::leanh::LeanObject,
    mut v_constName_1874_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1876_: u8 = 0;
    let mut v_res_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1876_ = (crate::leanh::lean_unbox(v_skipRealize_1875_) as u8);
    v_res_1877_ = l_Lean_getAsyncConstInfo___redArg(
        v_inst_1871_,
        v_inst_1872_,
        v_inst_1873_,
        v_constName_1874_,
        v_skipRealize_boxed_1876_,
    );
    return v_res_1877_;
}
pub unsafe fn l_Lean_getAsyncConstInfo(
    mut v_m_1878_: *mut crate::leanh::LeanObject,
    mut v_inst_1879_: *mut crate::leanh::LeanObject,
    mut v_inst_1880_: *mut crate::leanh::LeanObject,
    mut v_inst_1881_: *mut crate::leanh::LeanObject,
    mut v_constName_1882_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1883_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = l_Lean_getAsyncConstInfo___redArg(
        v_inst_1879_,
        v_inst_1880_,
        v_inst_1881_,
        v_constName_1882_,
        v_skipRealize_1883_,
    );
    return v___x_1884_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___boxed(
    mut v_m_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_constName_1889_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_1891_: u8 = 0;
    let mut v_res_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1891_ = (crate::leanh::lean_unbox(v_skipRealize_1890_) as u8);
    v_res_1892_ = l_Lean_getAsyncConstInfo(
        v_m_1885_,
        v_inst_1886_,
        v_inst_1887_,
        v_inst_1888_,
        v_constName_1889_,
        v_skipRealize_boxed_1891_,
    );
    return v_res_1892_;
}
pub unsafe fn l_panic___at___00Lean_isInductiveCore_x3f_spec__0(
    mut v_msg_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = crate::leanh::lean_box(0);
    v___x_1895_ = lean_panic_fn_borrowed(v___x_1894_, v_msg_1893_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lean_isInductiveCore_x3f___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1900_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1901_ = crate::leanh::lean_unsigned_to_nat(105);
    v___x_1902_ = l_Lean_isInductiveCore_x3f___closed__1;
    v___x_1903_ = l_Lean_isInductiveCore_x3f___closed__0;
    v___x_1904_ = l_mkPanicMessageWithDecl(
        v___x_1903_,
        v___x_1902_,
        v___x_1901_,
        v___x_1900_,
        v___x_1899_,
    );
    return v___x_1904_;
}
pub unsafe fn l_Lean_isInductiveCore_x3f(
    mut v_env_1905_: *mut crate::leanh::LeanObject,
    mut v_declName_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v_kind_1913_: u8 = 0;
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1907_ = 0;
                v___x_1908_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1905_, v_declName_1906_, v___x_1907_);
                if crate::leanh::lean_obj_tag(v___x_1908_) == 1 {
                    v_val_1909_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                    v_isSharedCheck_1922_ = (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v___x_1911_ = v___x_1908_;
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1909_);
                        crate::leanh::lean_dec(v___x_1908_);
                        v___x_1911_ = crate::leanh::lean_box(0);
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1908_);
                    v___x_1923_ = crate::leanh::lean_box(0);
                    return v___x_1923_;
                }
            }
            1 => {
                v_kind_1913_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_1909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_1913_ == 5 {
                    v___x_1914_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1909_);
                    if crate::leanh::lean_obj_tag(v___x_1914_) == 5 {
                        v_val_1915_ = crate::leanh::lean_ctor_get(v___x_1914_, 0);
                        crate::leanh::lean_inc_ref(v_val_1915_);
                        crate::leanh::lean_dec_ref_known(v___x_1914_, 1);
                        if v_isShared_1912_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1911_, 0, v_val_1915_);
                            v___x_1917_ = v___x_1911_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1918_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
                            v___x_1917_ = v_reuseFailAlloc_1918_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1914_);
                        crate::leanh::lean_del_object(v___x_1911_);
                        v___x_1919_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3_once),
                            _init_l_Lean_isInductiveCore_x3f___closed__3,
                        );
                        v___x_1920_ =
                            l_panic___at___00Lean_isInductiveCore_x3f_spec__0(v___x_1919_);
                        return v___x_1920_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1911_);
                    crate::leanh::lean_dec(v_val_1909_);
                    v___x_1921_ = crate::leanh::lean_box(0);
                    return v___x_1921_;
                }
            }
            2 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isInductive_x3f___redArg___lam__0(
    mut v_declName_1924_: *mut crate::leanh::LeanObject,
    mut v_toPure_1925_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_isInductiveCore_x3f(v_____do__lift_1926_, v_declName_1924_);
    v___x_1928_ =
        crate::leanh::lean_apply_2(v_toPure_1925_, crate::leanh::lean_box(0), v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lean_isInductive_x3f___redArg(
    mut v_inst_1929_: *mut crate::leanh::LeanObject,
    mut v_inst_1930_: *mut crate::leanh::LeanObject,
    mut v_declName_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1932_ = crate::leanh::lean_ctor_get(v_inst_1929_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1932_);
    v_toBind_1933_ = crate::leanh::lean_ctor_get(v_inst_1929_, 1);
    crate::leanh::lean_inc(v_toBind_1933_);
    crate::leanh::lean_dec_ref(v_inst_1929_);
    v_getEnv_1934_ = crate::leanh::lean_ctor_get(v_inst_1930_, 0);
    crate::leanh::lean_inc(v_getEnv_1934_);
    crate::leanh::lean_dec_ref(v_inst_1930_);
    v_toPure_1935_ = crate::leanh::lean_ctor_get(v_toApplicative_1932_, 1);
    crate::leanh::lean_inc(v_toPure_1935_);
    crate::leanh::lean_dec_ref(v_toApplicative_1932_);
    v___f_1936_ = crate::leanh::lean_alloc_closure(
        l_Lean_isInductive_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1936_, 0, v_declName_1931_);
    crate::leanh::lean_closure_set(v___f_1936_, 1, v_toPure_1935_);
    v___x_1937_ = crate::leanh::lean_apply_4(
        v_toBind_1933_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1934_,
        v___f_1936_,
    );
    return v___x_1937_;
}
pub unsafe fn l_Lean_isInductive_x3f(
    mut v_m_1938_: *mut crate::leanh::LeanObject,
    mut v_inst_1939_: *mut crate::leanh::LeanObject,
    mut v_inst_1940_: *mut crate::leanh::LeanObject,
    mut v_declName_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_isInductive_x3f___redArg(v_inst_1939_, v_inst_1940_, v_declName_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1945_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1946_ = crate::leanh::lean_unsigned_to_nat(115);
    v___x_1947_ = l_Lean_isDefn_x3f___redArg___lam__0___closed__0;
    v___x_1948_ = l_Lean_isInductiveCore_x3f___closed__0;
    v___x_1949_ = l_mkPanicMessageWithDecl(
        v___x_1948_,
        v___x_1947_,
        v___x_1946_,
        v___x_1945_,
        v___x_1944_,
    );
    return v___x_1949_;
}
pub unsafe fn l_Lean_isDefn_x3f___redArg___lam__0(
    mut v_toPure_1950_: *mut crate::leanh::LeanObject,
    mut v_constName_1951_: *mut crate::leanh::LeanObject,
    mut v___x_1952_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v_kind_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1957_ = 0;
                v___x_1958_ = l_Lean_Environment_findAsync_x3f(
                    v_____do__lift_1953_,
                    v_constName_1951_,
                    v___x_1957_,
                );
                if crate::leanh::lean_obj_tag(v___x_1958_) == 1 {
                    v_val_1959_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                    v_isSharedCheck_1972_ = (!crate::leanh::lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_1972_ == 0 {
                        v___x_1961_ = v___x_1958_;
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1959_);
                        crate::leanh::lean_dec(v___x_1958_);
                        v___x_1961_ = crate::leanh::lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1958_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = crate::leanh::lean_box(0);
                v___x_1956_ = crate::leanh::lean_apply_2(
                    v_toPure_1950_,
                    crate::leanh::lean_box(0),
                    v___x_1955_,
                );
                return v___x_1956_;
            }
            2 => {
                v_kind_1963_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_1959_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_1963_ == 0 {
                    v___x_1964_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1959_);
                    if crate::leanh::lean_obj_tag(v___x_1964_) == 1 {
                        v_val_1965_ = crate::leanh::lean_ctor_get(v___x_1964_, 0);
                        crate::leanh::lean_inc_ref(v_val_1965_);
                        crate::leanh::lean_dec_ref_known(v___x_1964_, 1);
                        if v_isShared_1962_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1961_, 0, v_val_1965_);
                            v___x_1967_ = v___x_1961_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1969_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_val_1965_);
                            v___x_1967_ = v_reuseFailAlloc_1969_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1964_);
                        crate::leanh::lean_del_object(v___x_1961_);
                        crate::leanh::lean_dec(v_toPure_1950_);
                        v___x_1970_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_isDefn_x3f___redArg___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once
                            ),
                            _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1,
                        );
                        v___x_1971_ = l_panic___redArg(v___x_1952_, v___x_1970_);
                        return v___x_1971_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1961_);
                    crate::leanh::lean_dec(v_val_1959_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1968_ = crate::leanh::lean_apply_2(
                    v_toPure_1950_,
                    crate::leanh::lean_box(0),
                    v___x_1967_,
                );
                return v___x_1968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isDefn_x3f___redArg___lam__0___boxed(
    mut v_toPure_1973_: *mut crate::leanh::LeanObject,
    mut v_constName_1974_: *mut crate::leanh::LeanObject,
    mut v___x_1975_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_isDefn_x3f___redArg___lam__0(
        v_toPure_1973_,
        v_constName_1974_,
        v___x_1975_,
        v_____do__lift_1976_,
    );
    crate::leanh::lean_dec(v___x_1975_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_isDefn_x3f___redArg(
    mut v_inst_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_constName_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1981_ = crate::leanh::lean_ctor_get(v_inst_1978_, 0);
    v_toBind_1982_ = crate::leanh::lean_ctor_get(v_inst_1978_, 1);
    crate::leanh::lean_inc(v_toBind_1982_);
    v_getEnv_1983_ = crate::leanh::lean_ctor_get(v_inst_1979_, 0);
    crate::leanh::lean_inc(v_getEnv_1983_);
    crate::leanh::lean_dec_ref(v_inst_1979_);
    v_toPure_1984_ = crate::leanh::lean_ctor_get(v_toApplicative_1981_, 1);
    crate::leanh::lean_inc(v_toPure_1984_);
    v___x_1985_ = crate::leanh::lean_box(0);
    v___x_1986_ = l_instInhabitedOfMonad___redArg(v_inst_1978_, v___x_1985_);
    v___f_1987_ = crate::leanh::lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1987_, 0, v_toPure_1984_);
    crate::leanh::lean_closure_set(v___f_1987_, 1, v_constName_1980_);
    crate::leanh::lean_closure_set(v___f_1987_, 2, v___x_1986_);
    v___x_1988_ = crate::leanh::lean_apply_4(
        v_toBind_1982_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1983_,
        v___f_1987_,
    );
    return v___x_1988_;
}
pub unsafe fn l_Lean_isDefn_x3f(
    mut v_m_1989_: *mut crate::leanh::LeanObject,
    mut v_inst_1990_: *mut crate::leanh::LeanObject,
    mut v_inst_1991_: *mut crate::leanh::LeanObject,
    mut v_constName_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1993_ = l_Lean_isDefn_x3f___redArg(v_inst_1990_, v_inst_1991_, v_constName_1992_);
    return v___x_1993_;
}
pub unsafe fn _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1996_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1997_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_1998_ = l_Lean_isCtor_x3f___redArg___lam__0___closed__0;
    v___x_1999_ = l_Lean_isInductiveCore_x3f___closed__0;
    v___x_2000_ = l_mkPanicMessageWithDecl(
        v___x_1999_,
        v___x_1998_,
        v___x_1997_,
        v___x_1996_,
        v___x_1995_,
    );
    return v___x_2000_;
}
pub unsafe fn l_Lean_isCtor_x3f___redArg___lam__0(
    mut v_toPure_2001_: *mut crate::leanh::LeanObject,
    mut v_constName_2002_: *mut crate::leanh::LeanObject,
    mut v___x_2003_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v_kind_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = 0;
                v___x_2009_ = l_Lean_Environment_findAsync_x3f(
                    v_____do__lift_2004_,
                    v_constName_2002_,
                    v___x_2008_,
                );
                if crate::leanh::lean_obj_tag(v___x_2009_) == 1 {
                    v_val_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2023_ = (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2010_);
                        crate::leanh::lean_dec(v___x_2009_);
                        v___x_2012_ = crate::leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2009_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2006_ = crate::leanh::lean_box(0);
                v___x_2007_ = crate::leanh::lean_apply_2(
                    v_toPure_2001_,
                    crate::leanh::lean_box(0),
                    v___x_2006_,
                );
                return v___x_2007_;
            }
            2 => {
                v_kind_2014_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_2010_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_2014_ == 6 {
                    v___x_2015_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2010_);
                    if crate::leanh::lean_obj_tag(v___x_2015_) == 6 {
                        v_val_2016_ = crate::leanh::lean_ctor_get(v___x_2015_, 0);
                        crate::leanh::lean_inc_ref(v_val_2016_);
                        crate::leanh::lean_dec_ref_known(v___x_2015_, 1);
                        if v_isShared_2013_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2012_, 0, v_val_2016_);
                            v___x_2018_ = v___x_2012_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2020_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_val_2016_);
                            v___x_2018_ = v_reuseFailAlloc_2020_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2015_);
                        crate::leanh::lean_del_object(v___x_2012_);
                        crate::leanh::lean_dec(v_toPure_2001_);
                        v___x_2021_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_isCtor_x3f___redArg___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once
                            ),
                            _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1,
                        );
                        v___x_2022_ = l_panic___redArg(v___x_2003_, v___x_2021_);
                        return v___x_2022_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2012_);
                    crate::leanh::lean_dec(v_val_2010_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2019_ = crate::leanh::lean_apply_2(
                    v_toPure_2001_,
                    crate::leanh::lean_box(0),
                    v___x_2018_,
                );
                return v___x_2019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isCtor_x3f___redArg___lam__0___boxed(
    mut v_toPure_2024_: *mut crate::leanh::LeanObject,
    mut v_constName_2025_: *mut crate::leanh::LeanObject,
    mut v___x_2026_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lean_isCtor_x3f___redArg___lam__0(
        v_toPure_2024_,
        v_constName_2025_,
        v___x_2026_,
        v_____do__lift_2027_,
    );
    crate::leanh::lean_dec(v___x_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Lean_isCtor_x3f___redArg(
    mut v_inst_2029_: *mut crate::leanh::LeanObject,
    mut v_inst_2030_: *mut crate::leanh::LeanObject,
    mut v_constName_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2032_ = crate::leanh::lean_ctor_get(v_inst_2029_, 0);
    v_toBind_2033_ = crate::leanh::lean_ctor_get(v_inst_2029_, 1);
    crate::leanh::lean_inc(v_toBind_2033_);
    v_getEnv_2034_ = crate::leanh::lean_ctor_get(v_inst_2030_, 0);
    crate::leanh::lean_inc(v_getEnv_2034_);
    crate::leanh::lean_dec_ref(v_inst_2030_);
    v_toPure_2035_ = crate::leanh::lean_ctor_get(v_toApplicative_2032_, 1);
    crate::leanh::lean_inc(v_toPure_2035_);
    v___x_2036_ = crate::leanh::lean_box(0);
    v___x_2037_ = l_instInhabitedOfMonad___redArg(v_inst_2029_, v___x_2036_);
    v___f_2038_ = crate::leanh::lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2038_, 0, v_toPure_2035_);
    crate::leanh::lean_closure_set(v___f_2038_, 1, v_constName_2031_);
    crate::leanh::lean_closure_set(v___f_2038_, 2, v___x_2037_);
    v___x_2039_ = crate::leanh::lean_apply_4(
        v_toBind_2033_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2034_,
        v___f_2038_,
    );
    return v___x_2039_;
}
pub unsafe fn l_Lean_isCtor_x3f(
    mut v_m_2040_: *mut crate::leanh::LeanObject,
    mut v_inst_2041_: *mut crate::leanh::LeanObject,
    mut v_inst_2042_: *mut crate::leanh::LeanObject,
    mut v_constName_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Lean_isCtor_x3f___redArg(v_inst_2041_, v_inst_2042_, v_constName_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_2047_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2048_ = crate::leanh::lean_unsigned_to_nat(129);
    v___x_2049_ = l_Lean_isRec_x3f___redArg___lam__0___closed__0;
    v___x_2050_ = l_Lean_isInductiveCore_x3f___closed__0;
    v___x_2051_ = l_mkPanicMessageWithDecl(
        v___x_2050_,
        v___x_2049_,
        v___x_2048_,
        v___x_2047_,
        v___x_2046_,
    );
    return v___x_2051_;
}
pub unsafe fn l_Lean_isRec_x3f___redArg___lam__0(
    mut v_toPure_2052_: *mut crate::leanh::LeanObject,
    mut v_constName_2053_: *mut crate::leanh::LeanObject,
    mut v___x_2054_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_kind_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2059_ = 0;
                v___x_2060_ = l_Lean_Environment_findAsync_x3f(
                    v_____do__lift_2055_,
                    v_constName_2053_,
                    v___x_2059_,
                );
                if crate::leanh::lean_obj_tag(v___x_2060_) == 1 {
                    v_val_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                    v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_2060_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2063_ = v___x_2060_;
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2061_);
                        crate::leanh::lean_dec(v___x_2060_);
                        v___x_2063_ = crate::leanh::lean_box(0);
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2060_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2057_ = crate::leanh::lean_box(0);
                v___x_2058_ = crate::leanh::lean_apply_2(
                    v_toPure_2052_,
                    crate::leanh::lean_box(0),
                    v___x_2057_,
                );
                return v___x_2058_;
            }
            2 => {
                v_kind_2065_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_2061_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_2065_ == 7 {
                    v___x_2066_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2061_);
                    if crate::leanh::lean_obj_tag(v___x_2066_) == 7 {
                        v_val_2067_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                        crate::leanh::lean_inc_ref(v_val_2067_);
                        crate::leanh::lean_dec_ref_known(v___x_2066_, 1);
                        if v_isShared_2064_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2063_, 0, v_val_2067_);
                            v___x_2069_ = v___x_2063_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2071_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2067_);
                            v___x_2069_ = v_reuseFailAlloc_2071_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2066_);
                        crate::leanh::lean_del_object(v___x_2063_);
                        crate::leanh::lean_dec(v_toPure_2052_);
                        v___x_2072_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_isRec_x3f___redArg___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_isRec_x3f___redArg___lam__0___closed__1_once
                            ),
                            _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1,
                        );
                        v___x_2073_ = l_panic___redArg(v___x_2054_, v___x_2072_);
                        return v___x_2073_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2063_);
                    crate::leanh::lean_dec(v_val_2061_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2070_ = crate::leanh::lean_apply_2(
                    v_toPure_2052_,
                    crate::leanh::lean_box(0),
                    v___x_2069_,
                );
                return v___x_2070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isRec_x3f___redArg___lam__0___boxed(
    mut v_toPure_2075_: *mut crate::leanh::LeanObject,
    mut v_constName_2076_: *mut crate::leanh::LeanObject,
    mut v___x_2077_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_isRec_x3f___redArg___lam__0(
        v_toPure_2075_,
        v_constName_2076_,
        v___x_2077_,
        v_____do__lift_2078_,
    );
    crate::leanh::lean_dec(v___x_2077_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_isRec_x3f___redArg(
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_constName_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2083_ = crate::leanh::lean_ctor_get(v_inst_2080_, 0);
    v_toBind_2084_ = crate::leanh::lean_ctor_get(v_inst_2080_, 1);
    crate::leanh::lean_inc(v_toBind_2084_);
    v_getEnv_2085_ = crate::leanh::lean_ctor_get(v_inst_2081_, 0);
    crate::leanh::lean_inc(v_getEnv_2085_);
    crate::leanh::lean_dec_ref(v_inst_2081_);
    v_toPure_2086_ = crate::leanh::lean_ctor_get(v_toApplicative_2083_, 1);
    crate::leanh::lean_inc(v_toPure_2086_);
    v___x_2087_ = crate::leanh::lean_box(0);
    v___x_2088_ = l_instInhabitedOfMonad___redArg(v_inst_2080_, v___x_2087_);
    v___f_2089_ = crate::leanh::lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2089_, 0, v_toPure_2086_);
    crate::leanh::lean_closure_set(v___f_2089_, 1, v_constName_2082_);
    crate::leanh::lean_closure_set(v___f_2089_, 2, v___x_2088_);
    v___x_2090_ = crate::leanh::lean_apply_4(
        v_toBind_2084_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2085_,
        v___f_2089_,
    );
    return v___x_2090_;
}
pub unsafe fn l_Lean_isRec_x3f(
    mut v_m_2091_: *mut crate::leanh::LeanObject,
    mut v_inst_2092_: *mut crate::leanh::LeanObject,
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_constName_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_isRec_x3f___redArg(v_inst_2092_, v_inst_2093_, v_constName_2094_);
    return v___x_2095_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg___lam__0(
    mut v_constName_2097_: *mut crate::leanh::LeanObject,
    mut v_toPure_2098_: *mut crate::leanh::LeanObject,
    mut v_info_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_levelParams_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_levelParams_2100_ = crate::leanh::lean_ctor_get(v_info_2099_, 1);
    crate::leanh::lean_inc(v_levelParams_2100_);
    crate::leanh::lean_dec_ref(v_info_2099_);
    v___x_2101_ = l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0;
    v___x_2102_ = crate::leanh::lean_box(0);
    v___x_2103_ = l_List_mapTR_loop___redArg(v___x_2101_, v_levelParams_2100_, v___x_2102_);
    v___x_2104_ = l_Lean_mkConst(v_constName_2097_, v___x_2103_);
    v___x_2105_ =
        crate::leanh::lean_apply_2(v_toPure_2098_, crate::leanh::lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg(
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_inst_2107_: *mut crate::leanh::LeanObject,
    mut v_inst_2108_: *mut crate::leanh::LeanObject,
    mut v_constName_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2110_ = crate::leanh::lean_ctor_get(v_inst_2106_, 0);
    v_toBind_2111_ = crate::leanh::lean_ctor_get(v_inst_2106_, 1);
    crate::leanh::lean_inc(v_toBind_2111_);
    v_toPure_2112_ = crate::leanh::lean_ctor_get(v_toApplicative_2110_, 1);
    crate::leanh::lean_inc(v_toPure_2112_);
    crate::leanh::lean_inc(v_constName_2109_);
    v___x_2113_ =
        l_Lean_getConstVal___redArg(v_inst_2106_, v_inst_2107_, v_inst_2108_, v_constName_2109_);
    v___f_2114_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkConstWithLevelParams___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2114_, 0, v_constName_2109_);
    crate::leanh::lean_closure_set(v___f_2114_, 1, v_toPure_2112_);
    v___x_2115_ = crate::leanh::lean_apply_4(
        v_toBind_2111_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2113_,
        v___f_2114_,
    );
    return v___x_2115_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams(
    mut v_m_2116_: *mut crate::leanh::LeanObject,
    mut v_inst_2117_: *mut crate::leanh::LeanObject,
    mut v_inst_2118_: *mut crate::leanh::LeanObject,
    mut v_inst_2119_: *mut crate::leanh::LeanObject,
    mut v_constName_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_mkConstWithLevelParams___redArg(
        v_inst_2117_,
        v_inst_2118_,
        v_inst_2119_,
        v_constName_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__0;
    v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__2;
    v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg___lam__0(
    mut v_constName_2128_: *mut crate::leanh::LeanObject,
    mut v_inst_2129_: *mut crate::leanh::LeanObject,
    mut v_inst_2130_: *mut crate::leanh::LeanObject,
    mut v_toPure_2131_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2132_) == 0 {
        let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: u8 = 0;
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2131_);
        v___x_2133_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2134_ = 0;
        v___x_2135_ = l_Lean_MessageData_ofConstName(v_constName_2128_, v___x_2134_);
        v___x_2136_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2133_);
        crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
        v___x_2137_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3,
        );
        v___x_2138_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
        crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
        v___x_2139_ = l_Lean_throwError___redArg(v_inst_2129_, v_inst_2130_, v___x_2138_);
        return v___x_2139_;
    } else {
        let mut v_val_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2130_);
        crate::leanh::lean_dec_ref(v_inst_2129_);
        crate::leanh::lean_dec(v_constName_2128_);
        v_val_2140_ = crate::leanh::lean_ctor_get(v_____do__lift_2132_, 0);
        crate::leanh::lean_inc(v_val_2140_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2132_, 1);
        v___x_2141_ =
            crate::leanh::lean_apply_2(v_toPure_2131_, crate::leanh::lean_box(0), v_val_2140_);
        return v___x_2141_;
    }
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg(
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_inst_2144_: *mut crate::leanh::LeanObject,
    mut v_constName_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2146_ = crate::leanh::lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2147_ = crate::leanh::lean_ctor_get(v_inst_2142_, 1);
    crate::leanh::lean_inc_n(v_toBind_2147_, 2);
    v_getEnv_2148_ = crate::leanh::lean_ctor_get(v_inst_2143_, 0);
    crate::leanh::lean_inc(v_getEnv_2148_);
    crate::leanh::lean_dec_ref(v_inst_2143_);
    v_toPure_2149_ = crate::leanh::lean_ctor_get(v_toApplicative_2146_, 1);
    crate::leanh::lean_inc_n(v_toPure_2149_, 2);
    v___x_2150_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_inst_2142_);
    crate::leanh::lean_inc(v_constName_2145_);
    v___f_2151_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfoDefn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2151_, 0, v_constName_2145_);
    crate::leanh::lean_closure_set(v___f_2151_, 1, v_inst_2142_);
    crate::leanh::lean_closure_set(v___f_2151_, 2, v_inst_2144_);
    crate::leanh::lean_closure_set(v___f_2151_, 3, v_toPure_2149_);
    v___x_2152_ = l_instInhabitedOfMonad___redArg(v_inst_2142_, v___x_2150_);
    v___f_2153_ = crate::leanh::lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2153_, 0, v_toPure_2149_);
    crate::leanh::lean_closure_set(v___f_2153_, 1, v_constName_2145_);
    crate::leanh::lean_closure_set(v___f_2153_, 2, v___x_2152_);
    v___x_2154_ = crate::leanh::lean_apply_4(
        v_toBind_2147_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2148_,
        v___f_2153_,
    );
    v___x_2155_ = crate::leanh::lean_apply_4(
        v_toBind_2147_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2154_,
        v___f_2151_,
    );
    return v___x_2155_;
}
pub unsafe fn l_Lean_getConstInfoDefn(
    mut v_m_2156_: *mut crate::leanh::LeanObject,
    mut v_inst_2157_: *mut crate::leanh::LeanObject,
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
    mut v_inst_2159_: *mut crate::leanh::LeanObject,
    mut v_constName_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_getConstInfoDefn___redArg(
        v_inst_2157_,
        v_inst_2158_,
        v_inst_2159_,
        v_constName_2160_,
    );
    return v___x_2161_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = l_Lean_getConstInfoInduct___redArg___lam__0___closed__0;
    v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__0(
    mut v_constName_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
    mut v_toPure_2168_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2169_) == 0 {
        let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: u8 = 0;
        let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2168_);
        v___x_2170_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2171_ = 0;
        v___x_2172_ = l_Lean_MessageData_ofConstName(v_constName_2165_, v___x_2171_);
        v___x_2173_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2170_);
        crate::leanh::lean_ctor_set(v___x_2173_, 1, v___x_2172_);
        v___x_2174_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1,
        );
        v___x_2175_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2175_, 0, v___x_2173_);
        crate::leanh::lean_ctor_set(v___x_2175_, 1, v___x_2174_);
        v___x_2176_ = l_Lean_throwError___redArg(v_inst_2166_, v_inst_2167_, v___x_2175_);
        return v___x_2176_;
    } else {
        let mut v_val_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2167_);
        crate::leanh::lean_dec_ref(v_inst_2166_);
        crate::leanh::lean_dec(v_constName_2165_);
        v_val_2177_ = crate::leanh::lean_ctor_get(v_____do__lift_2169_, 0);
        crate::leanh::lean_inc(v_val_2177_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2169_, 1);
        v___x_2178_ =
            crate::leanh::lean_apply_2(v_toPure_2168_, crate::leanh::lean_box(0), v_val_2177_);
        return v___x_2178_;
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__1(
    mut v_constName_2179_: *mut crate::leanh::LeanObject,
    mut v_toPure_2180_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_isInductiveCore_x3f(v_____do__lift_2181_, v_constName_2179_);
    v___x_2183_ =
        crate::leanh::lean_apply_2(v_toPure_2180_, crate::leanh::lean_box(0), v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg(
    mut v_inst_2184_: *mut crate::leanh::LeanObject,
    mut v_inst_2185_: *mut crate::leanh::LeanObject,
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
    mut v_constName_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2188_ = crate::leanh::lean_ctor_get(v_inst_2184_, 0);
    v_toBind_2189_ = crate::leanh::lean_ctor_get(v_inst_2184_, 1);
    crate::leanh::lean_inc_n(v_toBind_2189_, 2);
    v_getEnv_2190_ = crate::leanh::lean_ctor_get(v_inst_2185_, 0);
    crate::leanh::lean_inc(v_getEnv_2190_);
    crate::leanh::lean_dec_ref(v_inst_2185_);
    v_toPure_2191_ = crate::leanh::lean_ctor_get(v_toApplicative_2188_, 1);
    crate::leanh::lean_inc_n(v_toPure_2191_, 2);
    crate::leanh::lean_inc(v_constName_2187_);
    v___f_2192_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2192_, 0, v_constName_2187_);
    crate::leanh::lean_closure_set(v___f_2192_, 1, v_inst_2184_);
    crate::leanh::lean_closure_set(v___f_2192_, 2, v_inst_2186_);
    crate::leanh::lean_closure_set(v___f_2192_, 3, v_toPure_2191_);
    v___f_2193_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2193_, 0, v_constName_2187_);
    crate::leanh::lean_closure_set(v___f_2193_, 1, v_toPure_2191_);
    v___x_2194_ = crate::leanh::lean_apply_4(
        v_toBind_2189_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2190_,
        v___f_2193_,
    );
    v___x_2195_ = crate::leanh::lean_apply_4(
        v_toBind_2189_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2194_,
        v___f_2192_,
    );
    return v___x_2195_;
}
pub unsafe fn l_Lean_getConstInfoInduct(
    mut v_m_2196_: *mut crate::leanh::LeanObject,
    mut v_inst_2197_: *mut crate::leanh::LeanObject,
    mut v_inst_2198_: *mut crate::leanh::LeanObject,
    mut v_inst_2199_: *mut crate::leanh::LeanObject,
    mut v_constName_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Lean_getConstInfoInduct___redArg(
        v_inst_2197_,
        v_inst_2198_,
        v_inst_2199_,
        v_constName_2200_,
    );
    return v___x_2201_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Lean_getConstInfoCtor___redArg___lam__0___closed__0;
    v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg___lam__0(
    mut v_constName_2205_: *mut crate::leanh::LeanObject,
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
    mut v_toPure_2208_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2209_) == 0 {
        let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: u8 = 0;
        let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2208_);
        v___x_2210_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2211_ = 0;
        v___x_2212_ = l_Lean_MessageData_ofConstName(v_constName_2205_, v___x_2211_);
        v___x_2213_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2210_);
        crate::leanh::lean_ctor_set(v___x_2213_, 1, v___x_2212_);
        v___x_2214_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1,
        );
        v___x_2215_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2213_);
        crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2214_);
        v___x_2216_ = l_Lean_throwError___redArg(v_inst_2206_, v_inst_2207_, v___x_2215_);
        return v___x_2216_;
    } else {
        let mut v_val_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2207_);
        crate::leanh::lean_dec_ref(v_inst_2206_);
        crate::leanh::lean_dec(v_constName_2205_);
        v_val_2217_ = crate::leanh::lean_ctor_get(v_____do__lift_2209_, 0);
        crate::leanh::lean_inc(v_val_2217_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2209_, 1);
        v___x_2218_ =
            crate::leanh::lean_apply_2(v_toPure_2208_, crate::leanh::lean_box(0), v_val_2217_);
        return v___x_2218_;
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg(
    mut v_inst_2219_: *mut crate::leanh::LeanObject,
    mut v_inst_2220_: *mut crate::leanh::LeanObject,
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
    mut v_constName_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2223_ = crate::leanh::lean_ctor_get(v_inst_2219_, 0);
    v_toBind_2224_ = crate::leanh::lean_ctor_get(v_inst_2219_, 1);
    crate::leanh::lean_inc_n(v_toBind_2224_, 2);
    v_getEnv_2225_ = crate::leanh::lean_ctor_get(v_inst_2220_, 0);
    crate::leanh::lean_inc(v_getEnv_2225_);
    crate::leanh::lean_dec_ref(v_inst_2220_);
    v_toPure_2226_ = crate::leanh::lean_ctor_get(v_toApplicative_2223_, 1);
    crate::leanh::lean_inc_n(v_toPure_2226_, 2);
    v___x_2227_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_inst_2219_);
    crate::leanh::lean_inc(v_constName_2222_);
    v___f_2228_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfoCtor___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2228_, 0, v_constName_2222_);
    crate::leanh::lean_closure_set(v___f_2228_, 1, v_inst_2219_);
    crate::leanh::lean_closure_set(v___f_2228_, 2, v_inst_2221_);
    crate::leanh::lean_closure_set(v___f_2228_, 3, v_toPure_2226_);
    v___x_2229_ = l_instInhabitedOfMonad___redArg(v_inst_2219_, v___x_2227_);
    v___f_2230_ = crate::leanh::lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2230_, 0, v_toPure_2226_);
    crate::leanh::lean_closure_set(v___f_2230_, 1, v_constName_2222_);
    crate::leanh::lean_closure_set(v___f_2230_, 2, v___x_2229_);
    v___x_2231_ = crate::leanh::lean_apply_4(
        v_toBind_2224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2225_,
        v___f_2230_,
    );
    v___x_2232_ = crate::leanh::lean_apply_4(
        v_toBind_2224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2231_,
        v___f_2228_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_getConstInfoCtor(
    mut v_m_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
    mut v_inst_2235_: *mut crate::leanh::LeanObject,
    mut v_inst_2236_: *mut crate::leanh::LeanObject,
    mut v_constName_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = l_Lean_getConstInfoCtor___redArg(
        v_inst_2234_,
        v_inst_2235_,
        v_inst_2236_,
        v_constName_2237_,
    );
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_getConstInfoRec___redArg___lam__0___closed__0;
    v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
    return v___x_2241_;
}
pub unsafe fn l_Lean_getConstInfoRec___redArg___lam__0(
    mut v_constName_2242_: *mut crate::leanh::LeanObject,
    mut v_inst_2243_: *mut crate::leanh::LeanObject,
    mut v_inst_2244_: *mut crate::leanh::LeanObject,
    mut v_toPure_2245_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2246_) == 0 {
        let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: u8 = 0;
        let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2245_);
        v___x_2247_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2248_ = 0;
        v___x_2249_ = l_Lean_MessageData_ofConstName(v_constName_2242_, v___x_2248_);
        v___x_2250_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2250_, 0, v___x_2247_);
        crate::leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
        v___x_2251_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1,
        );
        v___x_2252_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2250_);
        crate::leanh::lean_ctor_set(v___x_2252_, 1, v___x_2251_);
        v___x_2253_ = l_Lean_throwError___redArg(v_inst_2243_, v_inst_2244_, v___x_2252_);
        return v___x_2253_;
    } else {
        let mut v_val_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2244_);
        crate::leanh::lean_dec_ref(v_inst_2243_);
        crate::leanh::lean_dec(v_constName_2242_);
        v_val_2254_ = crate::leanh::lean_ctor_get(v_____do__lift_2246_, 0);
        crate::leanh::lean_inc(v_val_2254_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2246_, 1);
        v___x_2255_ =
            crate::leanh::lean_apply_2(v_toPure_2245_, crate::leanh::lean_box(0), v_val_2254_);
        return v___x_2255_;
    }
}
pub unsafe fn l_Lean_getConstInfoRec___redArg(
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
    mut v_inst_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_constName_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2260_ = crate::leanh::lean_ctor_get(v_inst_2256_, 0);
    v_toBind_2261_ = crate::leanh::lean_ctor_get(v_inst_2256_, 1);
    crate::leanh::lean_inc_n(v_toBind_2261_, 2);
    v_getEnv_2262_ = crate::leanh::lean_ctor_get(v_inst_2257_, 0);
    crate::leanh::lean_inc(v_getEnv_2262_);
    crate::leanh::lean_dec_ref(v_inst_2257_);
    v_toPure_2263_ = crate::leanh::lean_ctor_get(v_toApplicative_2260_, 1);
    crate::leanh::lean_inc_n(v_toPure_2263_, 2);
    v___x_2264_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_inst_2256_);
    crate::leanh::lean_inc(v_constName_2259_);
    v___f_2265_ = crate::leanh::lean_alloc_closure(
        l_Lean_getConstInfoRec___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2265_, 0, v_constName_2259_);
    crate::leanh::lean_closure_set(v___f_2265_, 1, v_inst_2256_);
    crate::leanh::lean_closure_set(v___f_2265_, 2, v_inst_2258_);
    crate::leanh::lean_closure_set(v___f_2265_, 3, v_toPure_2263_);
    v___x_2266_ = l_instInhabitedOfMonad___redArg(v_inst_2256_, v___x_2264_);
    v___f_2267_ = crate::leanh::lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2267_, 0, v_toPure_2263_);
    crate::leanh::lean_closure_set(v___f_2267_, 1, v_constName_2259_);
    crate::leanh::lean_closure_set(v___f_2267_, 2, v___x_2266_);
    v___x_2268_ = crate::leanh::lean_apply_4(
        v_toBind_2261_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2262_,
        v___f_2267_,
    );
    v___x_2269_ = crate::leanh::lean_apply_4(
        v_toBind_2261_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2268_,
        v___f_2265_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_getConstInfoRec(
    mut v_m_2270_: *mut crate::leanh::LeanObject,
    mut v_inst_2271_: *mut crate::leanh::LeanObject,
    mut v_inst_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_constName_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_getConstInfoRec___redArg(
        v_inst_2271_,
        v_inst_2272_,
        v_inst_2273_,
        v_constName_2274_,
    );
    return v___x_2275_;
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__0(
    mut v_k_2276_: *mut crate::leanh::LeanObject,
    mut v_val_2277_: *mut crate::leanh::LeanObject,
    mut v_us_2278_: *mut crate::leanh::LeanObject,
    mut v_failK_2279_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2280_) == 6 {
        let mut v_val_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_failK_2279_);
        v_val_2281_ = crate::leanh::lean_ctor_get(v_____do__lift_2280_, 0);
        crate::leanh::lean_inc_ref(v_val_2281_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2280_, 1);
        v___x_2282_ = crate::leanh::lean_apply_3(v_k_2276_, v_val_2277_, v_us_2278_, v_val_2281_);
        return v___x_2282_;
    } else {
        let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____do__lift_2280_);
        crate::leanh::lean_dec(v_us_2278_);
        crate::leanh::lean_dec_ref(v_val_2277_);
        crate::leanh::lean_dec(v_k_2276_);
        v___x_2283_ = crate::leanh::lean_box(0);
        v___x_2284_ = crate::leanh::lean_apply_1(v_failK_2279_, v___x_2283_);
        return v___x_2284_;
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__1(
    mut v_declName_2285_: *mut crate::leanh::LeanObject,
    mut v_failK_2286_: *mut crate::leanh::LeanObject,
    mut v_k_2287_: *mut crate::leanh::LeanObject,
    mut v_us_2288_: *mut crate::leanh::LeanObject,
    mut v_inst_2289_: *mut crate::leanh::LeanObject,
    mut v_inst_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_toBind_2292_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2297_ = 0;
                v___x_2298_ = l_Lean_Environment_find_x3f(
                    v_____do__lift_2293_,
                    v_declName_2285_,
                    v___x_2297_,
                );
                if crate::leanh::lean_obj_tag(v___x_2298_) == 0 {
                    crate::leanh::lean_dec(v_toBind_2292_);
                    crate::leanh::lean_dec_ref(v_inst_2291_);
                    crate::leanh::lean_dec_ref(v_inst_2290_);
                    crate::leanh::lean_dec_ref(v_inst_2289_);
                    crate::leanh::lean_dec(v_us_2288_);
                    crate::leanh::lean_dec(v_k_2287_);
                    v___x_2299_ = crate::leanh::lean_box(0);
                    v___x_2300_ = crate::leanh::lean_apply_1(v_failK_2286_, v___x_2299_);
                    return v___x_2300_;
                } else {
                    v_val_2301_ = crate::leanh::lean_ctor_get(v___x_2298_, 0);
                    crate::leanh::lean_inc(v_val_2301_);
                    crate::leanh::lean_dec_ref_known(v___x_2298_, 1);
                    if crate::leanh::lean_obj_tag(v_val_2301_) == 5 {
                        v_val_2302_ = crate::leanh::lean_ctor_get(v_val_2301_, 0);
                        crate::leanh::lean_inc_ref(v_val_2302_);
                        crate::leanh::lean_dec_ref_known(v_val_2301_, 1);
                        v_ctors_2303_ = crate::leanh::lean_ctor_get(v_val_2302_, 4);
                        if crate::leanh::lean_obj_tag(v_ctors_2303_) == 1 {
                            v_tail_2304_ = crate::leanh::lean_ctor_get(v_ctors_2303_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_2304_) == 0 {
                                v_head_2305_ = crate::leanh::lean_ctor_get(v_ctors_2303_, 0);
                                crate::leanh::lean_inc(v_head_2305_);
                                v___f_2306_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_matchConstStructure___redArg___lam__0
                                        as *mut core::ffi::c_void,
                                    5,
                                    4,
                                );
                                crate::leanh::lean_closure_set(v___f_2306_, 0, v_k_2287_);
                                crate::leanh::lean_closure_set(v___f_2306_, 1, v_val_2302_);
                                crate::leanh::lean_closure_set(v___f_2306_, 2, v_us_2288_);
                                crate::leanh::lean_closure_set(v___f_2306_, 3, v_failK_2286_);
                                v___x_2307_ = l_Lean_getConstInfo___redArg(
                                    v_inst_2289_,
                                    v_inst_2290_,
                                    v_inst_2291_,
                                    v_head_2305_,
                                );
                                v___x_2308_ = crate::leanh::lean_apply_4(
                                    v_toBind_2292_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2307_,
                                    v___f_2306_,
                                );
                                return v___x_2308_;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_2302_);
                                crate::leanh::lean_dec(v_toBind_2292_);
                                crate::leanh::lean_dec_ref(v_inst_2291_);
                                crate::leanh::lean_dec_ref(v_inst_2290_);
                                crate::leanh::lean_dec_ref(v_inst_2289_);
                                crate::leanh::lean_dec(v_us_2288_);
                                crate::leanh::lean_dec(v_k_2287_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_val_2302_);
                            crate::leanh::lean_dec(v_toBind_2292_);
                            crate::leanh::lean_dec_ref(v_inst_2291_);
                            crate::leanh::lean_dec_ref(v_inst_2290_);
                            crate::leanh::lean_dec_ref(v_inst_2289_);
                            crate::leanh::lean_dec(v_us_2288_);
                            crate::leanh::lean_dec(v_k_2287_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2301_);
                        crate::leanh::lean_dec(v_toBind_2292_);
                        crate::leanh::lean_dec_ref(v_inst_2291_);
                        crate::leanh::lean_dec_ref(v_inst_2290_);
                        crate::leanh::lean_dec_ref(v_inst_2289_);
                        crate::leanh::lean_dec(v_us_2288_);
                        crate::leanh::lean_dec(v_k_2287_);
                        v___x_2309_ = crate::leanh::lean_box(0);
                        v___x_2310_ = crate::leanh::lean_apply_1(v_failK_2286_, v___x_2309_);
                        return v___x_2310_;
                    }
                }
            }
            1 => {
                v___x_2295_ = crate::leanh::lean_box(0);
                v___x_2296_ = crate::leanh::lean_apply_1(v_failK_2286_, v___x_2295_);
                return v___x_2296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg(
    mut v_inst_2311_: *mut crate::leanh::LeanObject,
    mut v_inst_2312_: *mut crate::leanh::LeanObject,
    mut v_inst_2313_: *mut crate::leanh::LeanObject,
    mut v_e_2314_: *mut crate::leanh::LeanObject,
    mut v_failK_2315_: *mut crate::leanh::LeanObject,
    mut v_k_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2314_) == 4 {
        let mut v_toBind_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2317_ = crate::leanh::lean_ctor_get(v_inst_2311_, 1);
        crate::leanh::lean_inc_n(v_toBind_2317_, 2);
        v_declName_2318_ = crate::leanh::lean_ctor_get(v_e_2314_, 0);
        crate::leanh::lean_inc(v_declName_2318_);
        v_us_2319_ = crate::leanh::lean_ctor_get(v_e_2314_, 1);
        crate::leanh::lean_inc(v_us_2319_);
        crate::leanh::lean_dec_ref_known(v_e_2314_, 2);
        v_getEnv_2320_ = crate::leanh::lean_ctor_get(v_inst_2312_, 0);
        crate::leanh::lean_inc(v_getEnv_2320_);
        v___f_2321_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_2321_, 0, v_declName_2318_);
        crate::leanh::lean_closure_set(v___f_2321_, 1, v_failK_2315_);
        crate::leanh::lean_closure_set(v___f_2321_, 2, v_k_2316_);
        crate::leanh::lean_closure_set(v___f_2321_, 3, v_us_2319_);
        crate::leanh::lean_closure_set(v___f_2321_, 4, v_inst_2311_);
        crate::leanh::lean_closure_set(v___f_2321_, 5, v_inst_2312_);
        crate::leanh::lean_closure_set(v___f_2321_, 6, v_inst_2313_);
        crate::leanh::lean_closure_set(v___f_2321_, 7, v_toBind_2317_);
        v___x_2322_ = crate::leanh::lean_apply_4(
            v_toBind_2317_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2320_,
            v___f_2321_,
        );
        return v___x_2322_;
    } else {
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_2316_);
        crate::leanh::lean_dec_ref(v_e_2314_);
        crate::leanh::lean_dec_ref(v_inst_2313_);
        crate::leanh::lean_dec_ref(v_inst_2312_);
        crate::leanh::lean_dec_ref(v_inst_2311_);
        v___x_2323_ = crate::leanh::lean_box(0);
        v___x_2324_ = crate::leanh::lean_apply_1(v_failK_2315_, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_matchConstStructure(
    mut v_m_2325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2326_: *mut crate::leanh::LeanObject,
    mut v_inst_2327_: *mut crate::leanh::LeanObject,
    mut v_inst_2328_: *mut crate::leanh::LeanObject,
    mut v_inst_2329_: *mut crate::leanh::LeanObject,
    mut v_e_2330_: *mut crate::leanh::LeanObject,
    mut v_failK_2331_: *mut crate::leanh::LeanObject,
    mut v_k_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2330_) == 4 {
        let mut v_toBind_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2333_ = crate::leanh::lean_ctor_get(v_inst_2327_, 1);
        crate::leanh::lean_inc_n(v_toBind_2333_, 2);
        v_declName_2334_ = crate::leanh::lean_ctor_get(v_e_2330_, 0);
        crate::leanh::lean_inc(v_declName_2334_);
        v_us_2335_ = crate::leanh::lean_ctor_get(v_e_2330_, 1);
        crate::leanh::lean_inc(v_us_2335_);
        crate::leanh::lean_dec_ref_known(v_e_2330_, 2);
        v_getEnv_2336_ = crate::leanh::lean_ctor_get(v_inst_2328_, 0);
        crate::leanh::lean_inc(v_getEnv_2336_);
        v___f_2337_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_2337_, 0, v_declName_2334_);
        crate::leanh::lean_closure_set(v___f_2337_, 1, v_failK_2331_);
        crate::leanh::lean_closure_set(v___f_2337_, 2, v_k_2332_);
        crate::leanh::lean_closure_set(v___f_2337_, 3, v_us_2335_);
        crate::leanh::lean_closure_set(v___f_2337_, 4, v_inst_2327_);
        crate::leanh::lean_closure_set(v___f_2337_, 5, v_inst_2328_);
        crate::leanh::lean_closure_set(v___f_2337_, 6, v_inst_2329_);
        crate::leanh::lean_closure_set(v___f_2337_, 7, v_toBind_2333_);
        v___x_2338_ = crate::leanh::lean_apply_4(
            v_toBind_2333_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2336_,
            v___f_2337_,
        );
        return v___x_2338_;
    } else {
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_2332_);
        crate::leanh::lean_dec_ref(v_e_2330_);
        crate::leanh::lean_dec_ref(v_inst_2329_);
        crate::leanh::lean_dec_ref(v_inst_2328_);
        crate::leanh::lean_dec_ref(v_inst_2327_);
        v___x_2339_ = crate::leanh::lean_box(0);
        v___x_2340_ = crate::leanh::lean_apply_1(v_failK_2331_, v___x_2339_);
        return v___x_2340_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg___lam__1(
    mut v_declName_2341_: *mut crate::leanh::LeanObject,
    mut v_failK_2342_: *mut crate::leanh::LeanObject,
    mut v_k_2343_: *mut crate::leanh::LeanObject,
    mut v_us_2344_: *mut crate::leanh::LeanObject,
    mut v_inst_2345_: *mut crate::leanh::LeanObject,
    mut v_inst_2346_: *mut crate::leanh::LeanObject,
    mut v_inst_2347_: *mut crate::leanh::LeanObject,
    mut v_toBind_2348_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_2362_: u8 = 0;
    let mut v_numIndices_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v_tail_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2356_ = 0;
                v___x_2357_ = l_Lean_Environment_find_x3f(
                    v_____do__lift_2349_,
                    v_declName_2341_,
                    v___x_2356_,
                );
                if crate::leanh::lean_obj_tag(v___x_2357_) == 0 {
                    crate::leanh::lean_dec(v_toBind_2348_);
                    crate::leanh::lean_dec_ref(v_inst_2347_);
                    crate::leanh::lean_dec_ref(v_inst_2346_);
                    crate::leanh::lean_dec_ref(v_inst_2345_);
                    crate::leanh::lean_dec(v_us_2344_);
                    crate::leanh::lean_dec(v_k_2343_);
                    v___x_2358_ = crate::leanh::lean_box(0);
                    v___x_2359_ = crate::leanh::lean_apply_1(v_failK_2342_, v___x_2358_);
                    return v___x_2359_;
                } else {
                    v_val_2360_ = crate::leanh::lean_ctor_get(v___x_2357_, 0);
                    crate::leanh::lean_inc(v_val_2360_);
                    crate::leanh::lean_dec_ref_known(v___x_2357_, 1);
                    if crate::leanh::lean_obj_tag(v_val_2360_) == 5 {
                        v_val_2361_ = crate::leanh::lean_ctor_get(v_val_2360_, 0);
                        crate::leanh::lean_inc_ref(v_val_2361_);
                        crate::leanh::lean_dec_ref_known(v_val_2360_, 1);
                        v_isRec_2362_ = crate::leanh::lean_ctor_get_uint8(
                            v_val_2361_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        );
                        if v_isRec_2362_ == 0 {
                            v_numIndices_2363_ = crate::leanh::lean_ctor_get(v_val_2361_, 2);
                            v_ctors_2364_ = crate::leanh::lean_ctor_get(v_val_2361_, 4);
                            v___x_2365_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2366_ = lean_nat_dec_eq(v_numIndices_2363_, v___x_2365_);
                            if v___x_2366_ == 0 {
                                crate::leanh::lean_dec_ref(v_val_2361_);
                                crate::leanh::lean_dec(v_toBind_2348_);
                                crate::leanh::lean_dec_ref(v_inst_2347_);
                                crate::leanh::lean_dec_ref(v_inst_2346_);
                                crate::leanh::lean_dec_ref(v_inst_2345_);
                                crate::leanh::lean_dec(v_us_2344_);
                                crate::leanh::lean_dec(v_k_2343_);
                                state = 1;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v_ctors_2364_) == 1 {
                                    v_tail_2367_ = crate::leanh::lean_ctor_get(v_ctors_2364_, 1);
                                    if crate::leanh::lean_obj_tag(v_tail_2367_) == 0 {
                                        v_head_2368_ =
                                            crate::leanh::lean_ctor_get(v_ctors_2364_, 0);
                                        crate::leanh::lean_inc(v_head_2368_);
                                        v___f_2369_ = crate::leanh::lean_alloc_closure(
                                            l_Lean_matchConstStructure___redArg___lam__0
                                                as *mut core::ffi::c_void,
                                            5,
                                            4,
                                        );
                                        crate::leanh::lean_closure_set(v___f_2369_, 0, v_k_2343_);
                                        crate::leanh::lean_closure_set(v___f_2369_, 1, v_val_2361_);
                                        crate::leanh::lean_closure_set(v___f_2369_, 2, v_us_2344_);
                                        crate::leanh::lean_closure_set(
                                            v___f_2369_,
                                            3,
                                            v_failK_2342_,
                                        );
                                        v___x_2370_ = l_Lean_getConstInfo___redArg(
                                            v_inst_2345_,
                                            v_inst_2346_,
                                            v_inst_2347_,
                                            v_head_2368_,
                                        );
                                        v___x_2371_ = crate::leanh::lean_apply_4(
                                            v_toBind_2348_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v___x_2370_,
                                            v___f_2369_,
                                        );
                                        return v___x_2371_;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_val_2361_);
                                        crate::leanh::lean_dec(v_toBind_2348_);
                                        crate::leanh::lean_dec_ref(v_inst_2347_);
                                        crate::leanh::lean_dec_ref(v_inst_2346_);
                                        crate::leanh::lean_dec_ref(v_inst_2345_);
                                        crate::leanh::lean_dec(v_us_2344_);
                                        crate::leanh::lean_dec(v_k_2343_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_val_2361_);
                                    crate::leanh::lean_dec(v_toBind_2348_);
                                    crate::leanh::lean_dec_ref(v_inst_2347_);
                                    crate::leanh::lean_dec_ref(v_inst_2346_);
                                    crate::leanh::lean_dec_ref(v_inst_2345_);
                                    crate::leanh::lean_dec(v_us_2344_);
                                    crate::leanh::lean_dec(v_k_2343_);
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_val_2361_);
                            crate::leanh::lean_dec(v_toBind_2348_);
                            crate::leanh::lean_dec_ref(v_inst_2347_);
                            crate::leanh::lean_dec_ref(v_inst_2346_);
                            crate::leanh::lean_dec_ref(v_inst_2345_);
                            crate::leanh::lean_dec(v_us_2344_);
                            crate::leanh::lean_dec(v_k_2343_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2360_);
                        crate::leanh::lean_dec(v_toBind_2348_);
                        crate::leanh::lean_dec_ref(v_inst_2347_);
                        crate::leanh::lean_dec_ref(v_inst_2346_);
                        crate::leanh::lean_dec_ref(v_inst_2345_);
                        crate::leanh::lean_dec(v_us_2344_);
                        crate::leanh::lean_dec(v_k_2343_);
                        v___x_2372_ = crate::leanh::lean_box(0);
                        v___x_2373_ = crate::leanh::lean_apply_1(v_failK_2342_, v___x_2372_);
                        return v___x_2373_;
                    }
                }
            }
            1 => {
                v___x_2351_ = crate::leanh::lean_box(0);
                v___x_2352_ = crate::leanh::lean_apply_1(v_failK_2342_, v___x_2351_);
                return v___x_2352_;
            }
            2 => {
                v___x_2354_ = crate::leanh::lean_box(0);
                v___x_2355_ = crate::leanh::lean_apply_1(v_failK_2342_, v___x_2354_);
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg(
    mut v_inst_2374_: *mut crate::leanh::LeanObject,
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
    mut v_inst_2376_: *mut crate::leanh::LeanObject,
    mut v_e_2377_: *mut crate::leanh::LeanObject,
    mut v_failK_2378_: *mut crate::leanh::LeanObject,
    mut v_k_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2377_) == 4 {
        let mut v_toBind_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2380_ = crate::leanh::lean_ctor_get(v_inst_2374_, 1);
        crate::leanh::lean_inc_n(v_toBind_2380_, 2);
        v_declName_2381_ = crate::leanh::lean_ctor_get(v_e_2377_, 0);
        crate::leanh::lean_inc(v_declName_2381_);
        v_us_2382_ = crate::leanh::lean_ctor_get(v_e_2377_, 1);
        crate::leanh::lean_inc(v_us_2382_);
        crate::leanh::lean_dec_ref_known(v_e_2377_, 2);
        v_getEnv_2383_ = crate::leanh::lean_ctor_get(v_inst_2375_, 0);
        crate::leanh::lean_inc(v_getEnv_2383_);
        v___f_2384_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_2384_, 0, v_declName_2381_);
        crate::leanh::lean_closure_set(v___f_2384_, 1, v_failK_2378_);
        crate::leanh::lean_closure_set(v___f_2384_, 2, v_k_2379_);
        crate::leanh::lean_closure_set(v___f_2384_, 3, v_us_2382_);
        crate::leanh::lean_closure_set(v___f_2384_, 4, v_inst_2374_);
        crate::leanh::lean_closure_set(v___f_2384_, 5, v_inst_2375_);
        crate::leanh::lean_closure_set(v___f_2384_, 6, v_inst_2376_);
        crate::leanh::lean_closure_set(v___f_2384_, 7, v_toBind_2380_);
        v___x_2385_ = crate::leanh::lean_apply_4(
            v_toBind_2380_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2383_,
            v___f_2384_,
        );
        return v___x_2385_;
    } else {
        let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_2379_);
        crate::leanh::lean_dec_ref(v_e_2377_);
        crate::leanh::lean_dec_ref(v_inst_2376_);
        crate::leanh::lean_dec_ref(v_inst_2375_);
        crate::leanh::lean_dec_ref(v_inst_2374_);
        v___x_2386_ = crate::leanh::lean_box(0);
        v___x_2387_ = crate::leanh::lean_apply_1(v_failK_2378_, v___x_2386_);
        return v___x_2387_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure(
    mut v_m_2388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2389_: *mut crate::leanh::LeanObject,
    mut v_inst_2390_: *mut crate::leanh::LeanObject,
    mut v_inst_2391_: *mut crate::leanh::LeanObject,
    mut v_inst_2392_: *mut crate::leanh::LeanObject,
    mut v_e_2393_: *mut crate::leanh::LeanObject,
    mut v_failK_2394_: *mut crate::leanh::LeanObject,
    mut v_k_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2393_) == 4 {
        let mut v_toBind_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2396_ = crate::leanh::lean_ctor_get(v_inst_2390_, 1);
        crate::leanh::lean_inc_n(v_toBind_2396_, 2);
        v_declName_2397_ = crate::leanh::lean_ctor_get(v_e_2393_, 0);
        crate::leanh::lean_inc(v_declName_2397_);
        v_us_2398_ = crate::leanh::lean_ctor_get(v_e_2393_, 1);
        crate::leanh::lean_inc(v_us_2398_);
        crate::leanh::lean_dec_ref_known(v_e_2393_, 2);
        v_getEnv_2399_ = crate::leanh::lean_ctor_get(v_inst_2391_, 0);
        crate::leanh::lean_inc(v_getEnv_2399_);
        v___f_2400_ = crate::leanh::lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_2400_, 0, v_declName_2397_);
        crate::leanh::lean_closure_set(v___f_2400_, 1, v_failK_2394_);
        crate::leanh::lean_closure_set(v___f_2400_, 2, v_k_2395_);
        crate::leanh::lean_closure_set(v___f_2400_, 3, v_us_2398_);
        crate::leanh::lean_closure_set(v___f_2400_, 4, v_inst_2390_);
        crate::leanh::lean_closure_set(v___f_2400_, 5, v_inst_2391_);
        crate::leanh::lean_closure_set(v___f_2400_, 6, v_inst_2392_);
        crate::leanh::lean_closure_set(v___f_2400_, 7, v_toBind_2396_);
        v___x_2401_ = crate::leanh::lean_apply_4(
            v_toBind_2396_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2399_,
            v___f_2400_,
        );
        return v___x_2401_;
    } else {
        let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_2395_);
        crate::leanh::lean_dec_ref(v_e_2393_);
        crate::leanh::lean_dec_ref(v_inst_2392_);
        crate::leanh::lean_dec_ref(v_inst_2391_);
        crate::leanh::lean_dec_ref(v_inst_2390_);
        v___x_2402_ = crate::leanh::lean_box(0);
        v___x_2403_ = crate::leanh::lean_apply_1(v_failK_2394_, v___x_2402_);
        return v___x_2403_;
    }
}
pub unsafe fn l_Lean_hasCompileError___boxed(
    mut v_env_2406_: *mut crate::leanh::LeanObject,
    mut v_constName_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = lean_has_compile_error(v_env_2406_, v_constName_2407_);
    v_r_2409_ = crate::leanh::lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__0(
    mut v_____do__lift_2410_: *mut crate::leanh::LeanObject,
    mut v_constName_2411_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2412_: u8,
    mut v_inst_2413_: *mut crate::leanh::LeanObject,
    mut v_inst_2414_: *mut crate::leanh::LeanObject,
    mut v___x_2415_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2417_ = l_Lean_Environment_evalConst___redArg(
        v_____do__lift_2410_,
        v_____do__lift_2416_,
        v_constName_2411_,
        v_checkMeta_2412_,
    );
    v___x_2418_ = l_Lean_ofExcept___redArg(v_inst_2413_, v_inst_2414_, v___x_2415_, v___x_2417_);
    return v___x_2418_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__0___boxed(
    mut v_____do__lift_2419_: *mut crate::leanh::LeanObject,
    mut v_constName_2420_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2421_: *mut crate::leanh::LeanObject,
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
    mut v_inst_2423_: *mut crate::leanh::LeanObject,
    mut v___x_2424_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_2426_: u8 = 0;
    let mut v_res_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2426_ = (crate::leanh::lean_unbox(v_checkMeta_2421_) as u8);
    v_res_2427_ = l_Lean_evalConst___redArg___lam__0(
        v_____do__lift_2419_,
        v_constName_2420_,
        v_checkMeta_boxed_2426_,
        v_inst_2422_,
        v_inst_2423_,
        v___x_2424_,
        v_____do__lift_2425_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2425_);
    crate::leanh::lean_dec(v_constName_2420_);
    crate::leanh::lean_dec_ref(v_____do__lift_2419_);
    return v_res_2427_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1(
    mut v_constName_2428_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2429_: u8,
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v___x_2432_: *mut crate::leanh::LeanObject,
    mut v_toBind_2433_: *mut crate::leanh::LeanObject,
    mut v_inst_2434_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ = crate::leanh::lean_box((v_checkMeta_2429_) as usize);
    v___f_2437_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2437_, 0, v_____do__lift_2435_);
    crate::leanh::lean_closure_set(v___f_2437_, 1, v_constName_2428_);
    crate::leanh::lean_closure_set(v___f_2437_, 2, v___x_2436_);
    crate::leanh::lean_closure_set(v___f_2437_, 3, v_inst_2430_);
    crate::leanh::lean_closure_set(v___f_2437_, 4, v_inst_2431_);
    crate::leanh::lean_closure_set(v___f_2437_, 5, v___x_2432_);
    v___x_2438_ = crate::leanh::lean_apply_4(
        v_toBind_2433_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2434_,
        v___f_2437_,
    );
    return v___x_2438_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1___boxed(
    mut v_constName_2439_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2440_: *mut crate::leanh::LeanObject,
    mut v_inst_2441_: *mut crate::leanh::LeanObject,
    mut v_inst_2442_: *mut crate::leanh::LeanObject,
    mut v___x_2443_: *mut crate::leanh::LeanObject,
    mut v_toBind_2444_: *mut crate::leanh::LeanObject,
    mut v_inst_2445_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_2447_: u8 = 0;
    let mut v_res_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2447_ = (crate::leanh::lean_unbox(v_checkMeta_2440_) as u8);
    v_res_2448_ = l_Lean_evalConst___redArg___lam__1(
        v_constName_2439_,
        v_checkMeta_boxed_2447_,
        v_inst_2441_,
        v_inst_2442_,
        v___x_2443_,
        v_toBind_2444_,
        v_inst_2445_,
        v_____do__lift_2446_,
    );
    return v_res_2448_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__2(
    mut v_toBind_2449_: *mut crate::leanh::LeanObject,
    mut v_getEnv_2450_: *mut crate::leanh::LeanObject,
    mut v___f_2451_: *mut crate::leanh::LeanObject,
    mut v_____r_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = crate::leanh::lean_apply_4(
        v_toBind_2449_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2450_,
        v___f_2451_,
    );
    return v___x_2453_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__3(
    mut v_constName_2454_: *mut crate::leanh::LeanObject,
    mut v_toBind_2455_: *mut crate::leanh::LeanObject,
    mut v_getEnv_2456_: *mut crate::leanh::LeanObject,
    mut v___f_2457_: *mut crate::leanh::LeanObject,
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v___f_2459_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: u8 = 0;
    v___x_2461_ = lean_has_compile_error(v_____do__lift_2460_, v_constName_2454_);
    if v___x_2461_ == 0 {
        let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2459_);
        crate::leanh::lean_dec_ref(v_inst_2458_);
        v___x_2462_ = crate::leanh::lean_apply_4(
            v_toBind_2455_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2456_,
            v___f_2457_,
        );
        return v___x_2462_;
    } else {
        let mut v_toMonadExceptOf_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2457_);
        crate::leanh::lean_dec(v_getEnv_2456_);
        v_toMonadExceptOf_2463_ = crate::leanh::lean_ctor_get(v_inst_2458_, 0);
        crate::leanh::lean_inc_ref(v_toMonadExceptOf_2463_);
        crate::leanh::lean_dec_ref(v_inst_2458_);
        v___x_2464_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_2463_);
        v___x_2465_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_2464_);
        v___x_2466_ = crate::leanh::lean_apply_4(
            v_toBind_2455_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2465_,
            v___f_2459_,
        );
        return v___x_2466_;
    }
}
pub unsafe fn l_Lean_evalConst___redArg(
    mut v_inst_2468_: *mut crate::leanh::LeanObject,
    mut v_inst_2469_: *mut crate::leanh::LeanObject,
    mut v_inst_2470_: *mut crate::leanh::LeanObject,
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
    mut v_constName_2472_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2473_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2474_ = crate::leanh::lean_ctor_get(v_inst_2468_, 1);
    crate::leanh::lean_inc_n(v_toBind_2474_, 4);
    v_getEnv_2475_ = crate::leanh::lean_ctor_get(v_inst_2469_, 0);
    crate::leanh::lean_inc_n(v_getEnv_2475_, 3);
    crate::leanh::lean_dec_ref(v_inst_2469_);
    v___x_2476_ = l_Lean_evalConst___redArg___closed__0;
    v___x_2477_ = crate::leanh::lean_box((v_checkMeta_2473_) as usize);
    crate::leanh::lean_inc_ref(v_inst_2470_);
    crate::leanh::lean_inc(v_constName_2472_);
    v___f_2478_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2478_, 0, v_constName_2472_);
    crate::leanh::lean_closure_set(v___f_2478_, 1, v___x_2477_);
    crate::leanh::lean_closure_set(v___f_2478_, 2, v_inst_2468_);
    crate::leanh::lean_closure_set(v___f_2478_, 3, v_inst_2470_);
    crate::leanh::lean_closure_set(v___f_2478_, 4, v___x_2476_);
    crate::leanh::lean_closure_set(v___f_2478_, 5, v_toBind_2474_);
    crate::leanh::lean_closure_set(v___f_2478_, 6, v_inst_2471_);
    crate::leanh::lean_inc_ref(v___f_2478_);
    v___f_2479_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2479_, 0, v_toBind_2474_);
    crate::leanh::lean_closure_set(v___f_2479_, 1, v_getEnv_2475_);
    crate::leanh::lean_closure_set(v___f_2479_, 2, v___f_2478_);
    v___f_2480_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2480_, 0, v_constName_2472_);
    crate::leanh::lean_closure_set(v___f_2480_, 1, v_toBind_2474_);
    crate::leanh::lean_closure_set(v___f_2480_, 2, v_getEnv_2475_);
    crate::leanh::lean_closure_set(v___f_2480_, 3, v___f_2478_);
    crate::leanh::lean_closure_set(v___f_2480_, 4, v_inst_2470_);
    crate::leanh::lean_closure_set(v___f_2480_, 5, v___f_2479_);
    v___x_2481_ = crate::leanh::lean_apply_4(
        v_toBind_2474_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2475_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_evalConst___redArg___boxed(
    mut v_inst_2482_: *mut crate::leanh::LeanObject,
    mut v_inst_2483_: *mut crate::leanh::LeanObject,
    mut v_inst_2484_: *mut crate::leanh::LeanObject,
    mut v_inst_2485_: *mut crate::leanh::LeanObject,
    mut v_constName_2486_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_2488_: u8 = 0;
    let mut v_res_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2488_ = (crate::leanh::lean_unbox(v_checkMeta_2487_) as u8);
    v_res_2489_ = l_Lean_evalConst___redArg(
        v_inst_2482_,
        v_inst_2483_,
        v_inst_2484_,
        v_inst_2485_,
        v_constName_2486_,
        v_checkMeta_boxed_2488_,
    );
    return v_res_2489_;
}
pub unsafe fn l_Lean_evalConst(
    mut v_m_2490_: *mut crate::leanh::LeanObject,
    mut v_inst_2491_: *mut crate::leanh::LeanObject,
    mut v_inst_2492_: *mut crate::leanh::LeanObject,
    mut v_inst_2493_: *mut crate::leanh::LeanObject,
    mut v_inst_2494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2495_: *mut crate::leanh::LeanObject,
    mut v_constName_2496_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2497_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2498_ = l_Lean_evalConst___redArg(
        v_inst_2491_,
        v_inst_2492_,
        v_inst_2493_,
        v_inst_2494_,
        v_constName_2496_,
        v_checkMeta_2497_,
    );
    return v___x_2498_;
}
pub unsafe fn l_Lean_evalConst___boxed(
    mut v_m_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_inst_2501_: *mut crate::leanh::LeanObject,
    mut v_inst_2502_: *mut crate::leanh::LeanObject,
    mut v_inst_2503_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2504_: *mut crate::leanh::LeanObject,
    mut v_constName_2505_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_2507_: u8 = 0;
    let mut v_res_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2507_ = (crate::leanh::lean_unbox(v_checkMeta_2506_) as u8);
    v_res_2508_ = l_Lean_evalConst(
        v_m_2499_,
        v_inst_2500_,
        v_inst_2501_,
        v_inst_2502_,
        v_inst_2503_,
        v_00_u03b1_2504_,
        v_constName_2505_,
        v_checkMeta_boxed_2507_,
    );
    return v_res_2508_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg___lam__0(
    mut v_____do__lift_2509_: *mut crate::leanh::LeanObject,
    mut v_typeName_2510_: *mut crate::leanh::LeanObject,
    mut v_constName_2511_: *mut crate::leanh::LeanObject,
    mut v_inst_2512_: *mut crate::leanh::LeanObject,
    mut v_inst_2513_: *mut crate::leanh::LeanObject,
    mut v___x_2514_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Environment_evalConstCheck___redArg(
        v_____do__lift_2509_,
        v_____do__lift_2515_,
        v_typeName_2510_,
        v_constName_2511_,
    );
    v___x_2517_ = l_Lean_ofExcept___redArg(v_inst_2512_, v_inst_2513_, v___x_2514_, v___x_2516_);
    return v___x_2517_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg___lam__0___boxed(
    mut v_____do__lift_2518_: *mut crate::leanh::LeanObject,
    mut v_typeName_2519_: *mut crate::leanh::LeanObject,
    mut v_constName_2520_: *mut crate::leanh::LeanObject,
    mut v_inst_2521_: *mut crate::leanh::LeanObject,
    mut v_inst_2522_: *mut crate::leanh::LeanObject,
    mut v___x_2523_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_evalConstCheck___redArg___lam__0(
        v_____do__lift_2518_,
        v_typeName_2519_,
        v_constName_2520_,
        v_inst_2521_,
        v_inst_2522_,
        v___x_2523_,
        v_____do__lift_2524_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2524_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg___lam__1(
    mut v_typeName_2526_: *mut crate::leanh::LeanObject,
    mut v_constName_2527_: *mut crate::leanh::LeanObject,
    mut v_inst_2528_: *mut crate::leanh::LeanObject,
    mut v_inst_2529_: *mut crate::leanh::LeanObject,
    mut v___x_2530_: *mut crate::leanh::LeanObject,
    mut v_toBind_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2534_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2534_, 0, v_____do__lift_2533_);
    crate::leanh::lean_closure_set(v___f_2534_, 1, v_typeName_2526_);
    crate::leanh::lean_closure_set(v___f_2534_, 2, v_constName_2527_);
    crate::leanh::lean_closure_set(v___f_2534_, 3, v_inst_2528_);
    crate::leanh::lean_closure_set(v___f_2534_, 4, v_inst_2529_);
    crate::leanh::lean_closure_set(v___f_2534_, 5, v___x_2530_);
    v___x_2535_ = crate::leanh::lean_apply_4(
        v_toBind_2531_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2532_,
        v___f_2534_,
    );
    return v___x_2535_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg(
    mut v_inst_2536_: *mut crate::leanh::LeanObject,
    mut v_inst_2537_: *mut crate::leanh::LeanObject,
    mut v_inst_2538_: *mut crate::leanh::LeanObject,
    mut v_inst_2539_: *mut crate::leanh::LeanObject,
    mut v_typeName_2540_: *mut crate::leanh::LeanObject,
    mut v_constName_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2542_ = crate::leanh::lean_ctor_get(v_inst_2536_, 1);
    crate::leanh::lean_inc_n(v_toBind_2542_, 4);
    v_getEnv_2543_ = crate::leanh::lean_ctor_get(v_inst_2537_, 0);
    crate::leanh::lean_inc_n(v_getEnv_2543_, 3);
    crate::leanh::lean_dec_ref(v_inst_2537_);
    v___x_2544_ = l_Lean_evalConst___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_inst_2538_);
    crate::leanh::lean_inc(v_constName_2541_);
    v___f_2545_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2545_, 0, v_typeName_2540_);
    crate::leanh::lean_closure_set(v___f_2545_, 1, v_constName_2541_);
    crate::leanh::lean_closure_set(v___f_2545_, 2, v_inst_2536_);
    crate::leanh::lean_closure_set(v___f_2545_, 3, v_inst_2538_);
    crate::leanh::lean_closure_set(v___f_2545_, 4, v___x_2544_);
    crate::leanh::lean_closure_set(v___f_2545_, 5, v_toBind_2542_);
    crate::leanh::lean_closure_set(v___f_2545_, 6, v_inst_2539_);
    crate::leanh::lean_inc_ref(v___f_2545_);
    v___f_2546_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2546_, 0, v_toBind_2542_);
    crate::leanh::lean_closure_set(v___f_2546_, 1, v_getEnv_2543_);
    crate::leanh::lean_closure_set(v___f_2546_, 2, v___f_2545_);
    v___f_2547_ = crate::leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2547_, 0, v_constName_2541_);
    crate::leanh::lean_closure_set(v___f_2547_, 1, v_toBind_2542_);
    crate::leanh::lean_closure_set(v___f_2547_, 2, v_getEnv_2543_);
    crate::leanh::lean_closure_set(v___f_2547_, 3, v___f_2545_);
    crate::leanh::lean_closure_set(v___f_2547_, 4, v_inst_2538_);
    crate::leanh::lean_closure_set(v___f_2547_, 5, v___f_2546_);
    v___x_2548_ = crate::leanh::lean_apply_4(
        v_toBind_2542_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2543_,
        v___f_2547_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_evalConstCheck(
    mut v_m_2549_: *mut crate::leanh::LeanObject,
    mut v_inst_2550_: *mut crate::leanh::LeanObject,
    mut v_inst_2551_: *mut crate::leanh::LeanObject,
    mut v_inst_2552_: *mut crate::leanh::LeanObject,
    mut v_inst_2553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2554_: *mut crate::leanh::LeanObject,
    mut v_typeName_2555_: *mut crate::leanh::LeanObject,
    mut v_constName_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = l_Lean_evalConstCheck___redArg(
        v_inst_2550_,
        v_inst_2551_,
        v_inst_2552_,
        v_inst_2553_,
        v_typeName_2555_,
        v_constName_2556_,
    );
    return v___x_2557_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__0(
    mut v___x_2558_: *mut crate::leanh::LeanObject,
    mut v_val_2559_: *mut crate::leanh::LeanObject,
    mut v_toPure_2560_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_2561_);
    v___x_2563_ = lean_array_get(v___x_2558_, v___x_2562_, v_val_2559_);
    crate::leanh::lean_dec_ref(v___x_2562_);
    v___x_2564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    v___x_2565_ =
        crate::leanh::lean_apply_2(v_toPure_2560_, crate::leanh::lean_box(0), v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(
    mut v___x_2566_: *mut crate::leanh::LeanObject,
    mut v_val_2567_: *mut crate::leanh::LeanObject,
    mut v_toPure_2568_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Lean_findModuleOf_x3f___redArg___lam__0(
        v___x_2566_,
        v_val_2567_,
        v_toPure_2568_,
        v_____do__lift_2569_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2569_);
    crate::leanh::lean_dec(v_val_2567_);
    crate::leanh::lean_dec(v___x_2566_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1(
    mut v_declName_2571_: *mut crate::leanh::LeanObject,
    mut v_toPure_2572_: *mut crate::leanh::LeanObject,
    mut v___x_2573_: *mut crate::leanh::LeanObject,
    mut v_toBind_2574_: *mut crate::leanh::LeanObject,
    mut v_getEnv_2575_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2576_, v_declName_2571_);
    if crate::leanh::lean_obj_tag(v___x_2577_) == 0 {
        let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_getEnv_2575_);
        crate::leanh::lean_dec(v_toBind_2574_);
        crate::leanh::lean_dec(v___x_2573_);
        v___x_2578_ = crate::leanh::lean_box(0);
        v___x_2579_ =
            crate::leanh::lean_apply_2(v_toPure_2572_, crate::leanh::lean_box(0), v___x_2578_);
        return v___x_2579_;
    } else {
        let mut v_val_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2580_ = crate::leanh::lean_ctor_get(v___x_2577_, 0);
        crate::leanh::lean_inc(v_val_2580_);
        crate::leanh::lean_dec_ref_known(v___x_2577_, 1);
        v___f_2581_ = crate::leanh::lean_alloc_closure(
            l_Lean_findModuleOf_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2581_, 0, v___x_2573_);
        crate::leanh::lean_closure_set(v___f_2581_, 1, v_val_2580_);
        crate::leanh::lean_closure_set(v___f_2581_, 2, v_toPure_2572_);
        v___x_2582_ = crate::leanh::lean_apply_4(
            v_toBind_2574_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_2575_,
            v___f_2581_,
        );
        return v___x_2582_;
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(
    mut v_declName_2583_: *mut crate::leanh::LeanObject,
    mut v_toPure_2584_: *mut crate::leanh::LeanObject,
    mut v___x_2585_: *mut crate::leanh::LeanObject,
    mut v_toBind_2586_: *mut crate::leanh::LeanObject,
    mut v_getEnv_2587_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_Lean_findModuleOf_x3f___redArg___lam__1(
        v_declName_2583_,
        v_toPure_2584_,
        v___x_2585_,
        v_toBind_2586_,
        v_getEnv_2587_,
        v_____do__lift_2588_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2588_);
    crate::leanh::lean_dec(v_declName_2583_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__2(
    mut v_inst_2590_: *mut crate::leanh::LeanObject,
    mut v_declName_2591_: *mut crate::leanh::LeanObject,
    mut v_toPure_2592_: *mut crate::leanh::LeanObject,
    mut v___x_2593_: *mut crate::leanh::LeanObject,
    mut v_toBind_2594_: *mut crate::leanh::LeanObject,
    mut v_____r_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getEnv_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_2596_ = crate::leanh::lean_ctor_get(v_inst_2590_, 0);
    crate::leanh::lean_inc_n(v_getEnv_2596_, 2);
    crate::leanh::lean_dec_ref(v_inst_2590_);
    crate::leanh::lean_inc(v_toBind_2594_);
    v___f_2597_ = crate::leanh::lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2597_, 0, v_declName_2591_);
    crate::leanh::lean_closure_set(v___f_2597_, 1, v_toPure_2592_);
    crate::leanh::lean_closure_set(v___f_2597_, 2, v___x_2593_);
    crate::leanh::lean_closure_set(v___f_2597_, 3, v_toBind_2594_);
    crate::leanh::lean_closure_set(v___f_2597_, 4, v_getEnv_2596_);
    v___x_2598_ = crate::leanh::lean_apply_4(
        v_toBind_2594_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_2596_,
        v___f_2597_,
    );
    return v___x_2598_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg(
    mut v_inst_2599_: *mut crate::leanh::LeanObject,
    mut v_inst_2600_: *mut crate::leanh::LeanObject,
    mut v_inst_2601_: *mut crate::leanh::LeanObject,
    mut v_declName_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2603_ = crate::leanh::lean_ctor_get(v_inst_2599_, 0);
    v_toFunctor_2604_ = crate::leanh::lean_ctor_get(v_toApplicative_2603_, 0);
    v_toBind_2605_ = crate::leanh::lean_ctor_get(v_inst_2599_, 1);
    crate::leanh::lean_inc_n(v_toBind_2605_, 2);
    v_toPure_2606_ = crate::leanh::lean_ctor_get(v_toApplicative_2603_, 1);
    v_mapConst_2607_ = crate::leanh::lean_ctor_get(v_toFunctor_2604_, 1);
    crate::leanh::lean_inc(v_mapConst_2607_);
    v___x_2608_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_toPure_2606_);
    crate::leanh::lean_inc(v_declName_2602_);
    crate::leanh::lean_inc_ref(v_inst_2600_);
    v___f_2609_ = crate::leanh::lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2609_, 0, v_inst_2600_);
    crate::leanh::lean_closure_set(v___f_2609_, 1, v_declName_2602_);
    crate::leanh::lean_closure_set(v___f_2609_, 2, v_toPure_2606_);
    crate::leanh::lean_closure_set(v___f_2609_, 3, v___x_2608_);
    crate::leanh::lean_closure_set(v___f_2609_, 4, v_toBind_2605_);
    v___x_2610_ =
        l_Lean_getConstInfo___redArg(v_inst_2599_, v_inst_2600_, v_inst_2601_, v_declName_2602_);
    v___x_2611_ = crate::leanh::lean_box(0);
    v___x_2612_ = crate::leanh::lean_apply_4(
        v_mapConst_2607_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2611_,
        v___x_2610_,
    );
    v___x_2613_ = crate::leanh::lean_apply_4(
        v_toBind_2605_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2612_,
        v___f_2609_,
    );
    return v___x_2613_;
}
pub unsafe fn l_Lean_findModuleOf_x3f(
    mut v_m_2614_: *mut crate::leanh::LeanObject,
    mut v_inst_2615_: *mut crate::leanh::LeanObject,
    mut v_inst_2616_: *mut crate::leanh::LeanObject,
    mut v_inst_2617_: *mut crate::leanh::LeanObject,
    mut v_declName_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_findModuleOf_x3f___redArg(
        v_inst_2615_,
        v_inst_2616_,
        v_inst_2617_,
        v_declName_2618_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0(
    mut v___x_2620_: *mut crate::leanh::LeanObject,
    mut v_toPure_2621_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2622_: u8,
    mut v_____x_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2623_) == 6 {
        let mut v_val_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2626_: u8 = 0;
        let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2624_ = crate::leanh::lean_ctor_get(v_____x_2623_, 0);
        v_numFields_2625_ = crate::leanh::lean_ctor_get(v_val_2624_, 4);
        v___x_2626_ = lean_nat_dec_eq(v_numFields_2625_, v___x_2620_);
        v___x_2627_ = crate::leanh::lean_box((v___x_2626_) as usize);
        v___x_2628_ =
            crate::leanh::lean_apply_2(v_toPure_2621_, crate::leanh::lean_box(0), v___x_2627_);
        return v___x_2628_;
    } else {
        let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2629_ = crate::leanh::lean_box((v_isUnsafe_2622_) as usize);
        v___x_2630_ =
            crate::leanh::lean_apply_2(v_toPure_2621_, crate::leanh::lean_box(0), v___x_2629_);
        return v___x_2630_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0___boxed(
    mut v___x_2631_: *mut crate::leanh::LeanObject,
    mut v_toPure_2632_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2633_: *mut crate::leanh::LeanObject,
    mut v_____x_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isUnsafe_boxed_2635_: u8 = 0;
    let mut v_res_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2635_ = (crate::leanh::lean_unbox(v_isUnsafe_2633_) as u8);
    v_res_2636_ = l_Lean_isEnumType___redArg___lam__0(
        v___x_2631_,
        v_toPure_2632_,
        v_isUnsafe_boxed_2635_,
        v_____x_2634_,
    );
    crate::leanh::lean_dec_ref(v_____x_2634_);
    crate::leanh::lean_dec(v___x_2631_);
    return v_res_2636_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__1(
    mut v_inst_2637_: *mut crate::leanh::LeanObject,
    mut v_inst_2638_: *mut crate::leanh::LeanObject,
    mut v_inst_2639_: *mut crate::leanh::LeanObject,
    mut v_toBind_2640_: *mut crate::leanh::LeanObject,
    mut v___f_2641_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ =
        l_Lean_getConstInfo___redArg(v_inst_2637_, v_inst_2638_, v_inst_2639_, v_ctorName_2642_);
    v___x_2644_ = crate::leanh::lean_apply_4(
        v_toBind_2640_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2643_,
        v___f_2641_,
    );
    return v___x_2644_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__2(
    mut v_toPure_2645_: *mut crate::leanh::LeanObject,
    mut v_inst_2646_: *mut crate::leanh::LeanObject,
    mut v_inst_2647_: *mut crate::leanh::LeanObject,
    mut v_inst_2648_: *mut crate::leanh::LeanObject,
    mut v_toBind_2649_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2650_) == 5 {
        let mut v_val_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toConstantVal_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numParams_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numIndices_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ctors_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isRec_2656_: u8 = 0;
        let mut v_isUnsafe_2657_: u8 = 0;
        let mut v_type_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2659_: u8 = 0;
        v_val_2651_ = crate::leanh::lean_ctor_get(v_____do__lift_2650_, 0);
        crate::leanh::lean_inc_ref(v_val_2651_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2650_, 1);
        v_toConstantVal_2652_ = crate::leanh::lean_ctor_get(v_val_2651_, 0);
        v_numParams_2653_ = crate::leanh::lean_ctor_get(v_val_2651_, 1);
        crate::leanh::lean_inc(v_numParams_2653_);
        v_numIndices_2654_ = crate::leanh::lean_ctor_get(v_val_2651_, 2);
        crate::leanh::lean_inc(v_numIndices_2654_);
        v_ctors_2655_ = crate::leanh::lean_ctor_get(v_val_2651_, 4);
        crate::leanh::lean_inc(v_ctors_2655_);
        v_isRec_2656_ = crate::leanh::lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        );
        v_isUnsafe_2657_ = crate::leanh::lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
        );
        v_type_2658_ = crate::leanh::lean_ctor_get(v_toConstantVal_2652_, 2);
        v___x_2659_ = l_Lean_Expr_isProp(v_type_2658_);
        if v___x_2659_ == 0 {
            let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2662_: u8 = 0;
            v___x_2660_ = l_Lean_InductiveVal_numTypeFormers(v_val_2651_);
            crate::leanh::lean_dec_ref(v_val_2651_);
            v___x_2661_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2662_ = lean_nat_dec_eq(v___x_2660_, v___x_2661_);
            crate::leanh::lean_dec(v___x_2660_);
            if v___x_2662_ == 0 {
                let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_ctors_2655_);
                crate::leanh::lean_dec(v_numIndices_2654_);
                crate::leanh::lean_dec(v_numParams_2653_);
                crate::leanh::lean_dec(v_toBind_2649_);
                crate::leanh::lean_dec_ref(v_inst_2648_);
                crate::leanh::lean_dec_ref(v_inst_2647_);
                crate::leanh::lean_dec_ref(v_inst_2646_);
                v___x_2663_ = crate::leanh::lean_box((v___x_2662_) as usize);
                v___x_2664_ = crate::leanh::lean_apply_2(
                    v_toPure_2645_,
                    crate::leanh::lean_box(0),
                    v___x_2663_,
                );
                return v___x_2664_;
            } else {
                let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2666_: u8 = 0;
                v___x_2665_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2666_ = lean_nat_dec_eq(v_numIndices_2654_, v___x_2665_);
                crate::leanh::lean_dec(v_numIndices_2654_);
                if v___x_2666_ == 0 {
                    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_ctors_2655_);
                    crate::leanh::lean_dec(v_numParams_2653_);
                    crate::leanh::lean_dec(v_toBind_2649_);
                    crate::leanh::lean_dec_ref(v_inst_2648_);
                    crate::leanh::lean_dec_ref(v_inst_2647_);
                    crate::leanh::lean_dec_ref(v_inst_2646_);
                    v___x_2667_ = crate::leanh::lean_box((v___x_2666_) as usize);
                    v___x_2668_ = crate::leanh::lean_apply_2(
                        v_toPure_2645_,
                        crate::leanh::lean_box(0),
                        v___x_2667_,
                    );
                    return v___x_2668_;
                } else {
                    let mut v___x_2669_: u8 = 0;
                    v___x_2669_ = lean_nat_dec_eq(v_numParams_2653_, v___x_2665_);
                    crate::leanh::lean_dec(v_numParams_2653_);
                    if v___x_2669_ == 0 {
                        let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_ctors_2655_);
                        crate::leanh::lean_dec(v_toBind_2649_);
                        crate::leanh::lean_dec_ref(v_inst_2648_);
                        crate::leanh::lean_dec_ref(v_inst_2647_);
                        crate::leanh::lean_dec_ref(v_inst_2646_);
                        v___x_2670_ = crate::leanh::lean_box((v___x_2669_) as usize);
                        v___x_2671_ = crate::leanh::lean_apply_2(
                            v_toPure_2645_,
                            crate::leanh::lean_box(0),
                            v___x_2670_,
                        );
                        return v___x_2671_;
                    } else {
                        let mut v___x_2672_: u8 = 0;
                        v___x_2672_ = l_List_isEmpty___redArg(v_ctors_2655_);
                        if v___x_2672_ == 0 {
                            if v_isRec_2656_ == 0 {
                                if v_isUnsafe_2657_ == 0 {
                                    let mut v___x_2673_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_2674_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_2675_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2676_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_2673_ =
                                        crate::leanh::lean_box((v_isUnsafe_2657_) as usize);
                                    v___f_2674_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2674_, 0, v___x_2665_);
                                    crate::leanh::lean_closure_set(v___f_2674_, 1, v_toPure_2645_);
                                    crate::leanh::lean_closure_set(v___f_2674_, 2, v___x_2673_);
                                    crate::leanh::lean_inc_ref(v_inst_2646_);
                                    v___f_2675_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__1
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2675_, 0, v_inst_2646_);
                                    crate::leanh::lean_closure_set(v___f_2675_, 1, v_inst_2647_);
                                    crate::leanh::lean_closure_set(v___f_2675_, 2, v_inst_2648_);
                                    crate::leanh::lean_closure_set(v___f_2675_, 3, v_toBind_2649_);
                                    crate::leanh::lean_closure_set(v___f_2675_, 4, v___f_2674_);
                                    v___x_2676_ = l_List_allM___redArg(
                                        v_inst_2646_,
                                        v___f_2675_,
                                        v_ctors_2655_,
                                    );
                                    return v___x_2676_;
                                } else {
                                    let mut v___x_2677_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2678_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v_ctors_2655_);
                                    crate::leanh::lean_dec(v_toBind_2649_);
                                    crate::leanh::lean_dec_ref(v_inst_2648_);
                                    crate::leanh::lean_dec_ref(v_inst_2647_);
                                    crate::leanh::lean_dec_ref(v_inst_2646_);
                                    v___x_2677_ = crate::leanh::lean_box((v_isRec_2656_) as usize);
                                    v___x_2678_ = crate::leanh::lean_apply_2(
                                        v_toPure_2645_,
                                        crate::leanh::lean_box(0),
                                        v___x_2677_,
                                    );
                                    return v___x_2678_;
                                }
                            } else {
                                let mut v___x_2679_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2680_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v_ctors_2655_);
                                crate::leanh::lean_dec(v_toBind_2649_);
                                crate::leanh::lean_dec_ref(v_inst_2648_);
                                crate::leanh::lean_dec_ref(v_inst_2647_);
                                crate::leanh::lean_dec_ref(v_inst_2646_);
                                v___x_2679_ = crate::leanh::lean_box((v___x_2672_) as usize);
                                v___x_2680_ = crate::leanh::lean_apply_2(
                                    v_toPure_2645_,
                                    crate::leanh::lean_box(0),
                                    v___x_2679_,
                                );
                                return v___x_2680_;
                            }
                        } else {
                            let mut v___x_2681_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2682_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_ctors_2655_);
                            crate::leanh::lean_dec(v_toBind_2649_);
                            crate::leanh::lean_dec_ref(v_inst_2648_);
                            crate::leanh::lean_dec_ref(v_inst_2647_);
                            crate::leanh::lean_dec_ref(v_inst_2646_);
                            v___x_2681_ = crate::leanh::lean_box((v___x_2659_) as usize);
                            v___x_2682_ = crate::leanh::lean_apply_2(
                                v_toPure_2645_,
                                crate::leanh::lean_box(0),
                                v___x_2681_,
                            );
                            return v___x_2682_;
                        }
                    }
                }
            }
        } else {
            let mut v___x_2683_: u8 = 0;
            let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_ctors_2655_);
            crate::leanh::lean_dec(v_numIndices_2654_);
            crate::leanh::lean_dec(v_numParams_2653_);
            crate::leanh::lean_dec_ref(v_val_2651_);
            crate::leanh::lean_dec(v_toBind_2649_);
            crate::leanh::lean_dec_ref(v_inst_2648_);
            crate::leanh::lean_dec_ref(v_inst_2647_);
            crate::leanh::lean_dec_ref(v_inst_2646_);
            v___x_2683_ = 0;
            v___x_2684_ = crate::leanh::lean_box((v___x_2683_) as usize);
            v___x_2685_ =
                crate::leanh::lean_apply_2(v_toPure_2645_, crate::leanh::lean_box(0), v___x_2684_);
            return v___x_2685_;
        }
    } else {
        let mut v___x_2686_: u8 = 0;
        let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____do__lift_2650_);
        crate::leanh::lean_dec(v_toBind_2649_);
        crate::leanh::lean_dec_ref(v_inst_2648_);
        crate::leanh::lean_dec_ref(v_inst_2647_);
        crate::leanh::lean_dec_ref(v_inst_2646_);
        v___x_2686_ = 0;
        v___x_2687_ = crate::leanh::lean_box((v___x_2686_) as usize);
        v___x_2688_ =
            crate::leanh::lean_apply_2(v_toPure_2645_, crate::leanh::lean_box(0), v___x_2687_);
        return v___x_2688_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg(
    mut v_inst_2689_: *mut crate::leanh::LeanObject,
    mut v_inst_2690_: *mut crate::leanh::LeanObject,
    mut v_inst_2691_: *mut crate::leanh::LeanObject,
    mut v_declName_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2693_ = crate::leanh::lean_ctor_get(v_inst_2689_, 0);
    v_toBind_2694_ = crate::leanh::lean_ctor_get(v_inst_2689_, 1);
    crate::leanh::lean_inc_n(v_toBind_2694_, 2);
    v_toPure_2695_ = crate::leanh::lean_ctor_get(v_toApplicative_2693_, 1);
    crate::leanh::lean_inc(v_toPure_2695_);
    crate::leanh::lean_inc_ref(v_inst_2691_);
    crate::leanh::lean_inc_ref(v_inst_2690_);
    crate::leanh::lean_inc_ref(v_inst_2689_);
    v___x_2696_ =
        l_Lean_getConstInfo___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_declName_2692_);
    v___f_2697_ = crate::leanh::lean_alloc_closure(
        l_Lean_isEnumType___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2697_, 0, v_toPure_2695_);
    crate::leanh::lean_closure_set(v___f_2697_, 1, v_inst_2689_);
    crate::leanh::lean_closure_set(v___f_2697_, 2, v_inst_2690_);
    crate::leanh::lean_closure_set(v___f_2697_, 3, v_inst_2691_);
    crate::leanh::lean_closure_set(v___f_2697_, 4, v_toBind_2694_);
    v___x_2698_ = crate::leanh::lean_apply_4(
        v_toBind_2694_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2696_,
        v___f_2697_,
    );
    return v___x_2698_;
}
pub unsafe fn l_Lean_isEnumType(
    mut v_m_2699_: *mut crate::leanh::LeanObject,
    mut v_inst_2700_: *mut crate::leanh::LeanObject,
    mut v_inst_2701_: *mut crate::leanh::LeanObject,
    mut v_inst_2702_: *mut crate::leanh::LeanObject,
    mut v_declName_2703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ =
        l_Lean_isEnumType___redArg(v_inst_2700_, v_inst_2701_, v_inst_2702_, v_declName_2703_);
    return v___x_2704_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_MonadEnv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AuxRecursor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_MonadEnv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_MonadEnv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_AuxRecursor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Old(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_MonadEnv(builtin);
}
