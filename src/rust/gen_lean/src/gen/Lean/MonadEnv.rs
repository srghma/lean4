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
pub static l_Lean_withEnv___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_withEnv___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withEnv___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withEnv___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_withoutModifyingEnv_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_isInductiveCore_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__1_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_isInductiveCore_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__2_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_isInductiveCore_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_isInductiveCore_x3f___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isInductiveCore_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_isRec_x3f___redArg___lam__0___closed__0_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isRec_x3f___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkLevelParam as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_evalConst___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_stringToMessageData as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_evalConst___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_evalConst___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_setEnv___redArg___lam__0(
    mut v_env_1353_: *mut leanh::LeanObject,
    mut v_x_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_env_1353_);
    return v_env_1353_;
}
pub unsafe fn l_Lean_setEnv___redArg___lam__0___boxed(
    mut v_env_1355_: *mut leanh::LeanObject,
    mut v_x_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1357_ = l_Lean_setEnv___redArg___lam__0(v_env_1355_, v_x_1356_);
    leanh::lean_dec_ref(v_x_1356_);
    leanh::lean_dec_ref(v_env_1355_);
    return v_res_1357_;
}
pub unsafe fn l_Lean_setEnv___redArg(
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_env_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyEnv_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_1360_ = leanh::lean_ctor_get(v_inst_1358_, 1);
    leanh::lean_inc(v_modifyEnv_1360_);
    leanh::lean_dec_ref(v_inst_1358_);
    v___f_1361_ = leanh::lean_alloc_closure(
        l_Lean_setEnv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1361_, 0, v_env_1359_);
    v___x_1362_ = leanh::lean_apply_1(v_modifyEnv_1360_, v___f_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lean_setEnv(
    mut v_m_1363_: *mut leanh::LeanObject,
    mut v_inst_1364_: *mut leanh::LeanObject,
    mut v_env_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_setEnv___redArg(v_inst_1364_, v_env_1365_);
    return v___x_1366_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0(
    mut v_x_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1368_ = leanh::lean_ctor_get(v_x_1367_, 0);
    leanh::lean_inc(v_fst_1368_);
    return v_fst_1368_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0___boxed(
    mut v_x_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_withEnv___redArg___lam__0(v_x_1369_);
    leanh::lean_dec_ref(v_x_1369_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1(
    mut v_x_1371_: *mut leanh::LeanObject,
    mut v_____r_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1371_);
    return v_x_1371_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1___boxed(
    mut v_x_1373_: *mut leanh::LeanObject,
    mut v_____r_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_withEnv___redArg___lam__1(v_x_1373_, v_____r_1374_);
    leanh::lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2(
    mut v___x_1376_: *mut leanh::LeanObject,
    mut v_x_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_1376_);
    return v___x_1376_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2___boxed(
    mut v___x_1378_: *mut leanh::LeanObject,
    mut v_x_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1380_ = l_Lean_withEnv___redArg___lam__2(v___x_1378_, v_x_1379_);
    leanh::lean_dec(v_x_1379_);
    leanh::lean_dec(v___x_1378_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__3(
    mut v_toFunctor_1381_: *mut leanh::LeanObject,
    mut v_inst_1382_: *mut leanh::LeanObject,
    mut v_env_1383_: *mut leanh::LeanObject,
    mut v_toBind_1384_: *mut leanh::LeanObject,
    mut v___f_1385_: *mut leanh::LeanObject,
    mut v_inst_1386_: *mut leanh::LeanObject,
    mut v___f_1387_: *mut leanh::LeanObject,
    mut v_saved_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1389_ = leanh::lean_ctor_get(v_toFunctor_1381_, 0);
    leanh::lean_inc(v_map_1389_);
    leanh::lean_dec_ref(v_toFunctor_1381_);
    leanh::lean_inc_ref(v_inst_1382_);
    v___x_1390_ = l_Lean_setEnv___redArg(v_inst_1382_, v_env_1383_);
    v___x_1391_ = leanh::lean_apply_4(
        v_toBind_1384_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1390_,
        v___f_1385_,
    );
    v___x_1392_ = l_Lean_setEnv___redArg(v_inst_1382_, v_saved_1388_);
    v___f_1393_ = leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1393_, 0, v___x_1392_);
    v_y_1394_ = leanh::lean_apply_4(
        v_inst_1386_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1391_,
        v___f_1393_,
    );
    v___x_1395_ = leanh::lean_apply_4(
        v_map_1389_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1387_,
        v_y_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Lean_withEnv___redArg(
    mut v_inst_1397_: *mut leanh::LeanObject,
    mut v_inst_1398_: *mut leanh::LeanObject,
    mut v_inst_1399_: *mut leanh::LeanObject,
    mut v_env_1400_: *mut leanh::LeanObject,
    mut v_x_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1402_ = leanh::lean_ctor_get(v_inst_1397_, 0);
    leanh::lean_inc_ref(v_toApplicative_1402_);
    v_toBind_1403_ = leanh::lean_ctor_get(v_inst_1397_, 1);
    leanh::lean_inc_n(v_toBind_1403_, 2);
    leanh::lean_dec_ref(v_inst_1397_);
    v_getEnv_1404_ = leanh::lean_ctor_get(v_inst_1399_, 0);
    leanh::lean_inc(v_getEnv_1404_);
    v_toFunctor_1405_ = leanh::lean_ctor_get(v_toApplicative_1402_, 0);
    leanh::lean_inc_ref(v_toFunctor_1405_);
    leanh::lean_dec_ref(v_toApplicative_1402_);
    v___f_1406_ = l_Lean_withEnv___redArg___closed__0;
    v___f_1407_ = leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1407_, 0, v_x_1401_);
    v___f_1408_ = leanh::lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1408_, 0, v_toFunctor_1405_);
    leanh::lean_closure_set(v___f_1408_, 1, v_inst_1399_);
    leanh::lean_closure_set(v___f_1408_, 2, v_env_1400_);
    leanh::lean_closure_set(v___f_1408_, 3, v_toBind_1403_);
    leanh::lean_closure_set(v___f_1408_, 4, v___f_1407_);
    leanh::lean_closure_set(v___f_1408_, 5, v_inst_1398_);
    leanh::lean_closure_set(v___f_1408_, 6, v___f_1406_);
    v___x_1409_ = leanh::lean_apply_4(
        v_toBind_1403_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1404_,
        v___f_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lean_withEnv(
    mut v_m_1410_: *mut leanh::LeanObject,
    mut v_00_u03b1_1411_: *mut leanh::LeanObject,
    mut v_inst_1412_: *mut leanh::LeanObject,
    mut v_inst_1413_: *mut leanh::LeanObject,
    mut v_inst_1414_: *mut leanh::LeanObject,
    mut v_env_1415_: *mut leanh::LeanObject,
    mut v_x_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_env_1418_: *mut leanh::LeanObject,
    mut v_declName_1419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = 0;
    v___x_1421_ = l_Lean_Environment_findAsync_x3f(v_env_1418_, v_declName_1419_, v___x_1420_);
    if leanh::lean_obj_tag(v___x_1421_) == 1 {
        let mut v_val_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_1423_: u8 = 0;
        v_val_1422_ = leanh::lean_ctor_get(v___x_1421_, 0);
        leanh::lean_inc(v_val_1422_);
        leanh::lean_dec_ref_known(v___x_1421_, 1);
        v_kind_1423_ = leanh::lean_ctor_get_uint8(
            v_val_1422_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        );
        leanh::lean_dec(v_val_1422_);
        if v_kind_1423_ == 5 {
            let mut v___x_1424_: u8 = 0;
            v___x_1424_ = 1;
            return v___x_1424_;
        } else {
            return v___x_1420_;
        }
    } else {
        leanh::lean_dec(v___x_1421_);
        return v___x_1420_;
    }
}
pub unsafe fn l_Lean_isInductiveCore___boxed(
    mut v_env_1425_: *mut leanh::LeanObject,
    mut v_declName_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_isInductiveCore(v_env_1425_, v_declName_1426_);
    v_r_1428_ = leanh::lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Lean_isInductive___redArg___lam__0(
    mut v_declName_1429_: *mut leanh::LeanObject,
    mut v_toPure_1430_: *mut leanh::LeanObject,
    mut v_____do__lift_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Lean_isInductiveCore(v_____do__lift_1431_, v_declName_1429_);
    v___x_1433_ = leanh::lean_box((v___x_1432_) as usize);
    v___x_1434_ =
        leanh::lean_apply_2(v_toPure_1430_, leanh::lean_box(0), v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Lean_isInductive___redArg(
    mut v_inst_1435_: *mut leanh::LeanObject,
    mut v_inst_1436_: *mut leanh::LeanObject,
    mut v_declName_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1438_ = leanh::lean_ctor_get(v_inst_1435_, 0);
    leanh::lean_inc_ref(v_toApplicative_1438_);
    v_toBind_1439_ = leanh::lean_ctor_get(v_inst_1435_, 1);
    leanh::lean_inc(v_toBind_1439_);
    leanh::lean_dec_ref(v_inst_1435_);
    v_getEnv_1440_ = leanh::lean_ctor_get(v_inst_1436_, 0);
    leanh::lean_inc(v_getEnv_1440_);
    leanh::lean_dec_ref(v_inst_1436_);
    v_toPure_1441_ = leanh::lean_ctor_get(v_toApplicative_1438_, 1);
    leanh::lean_inc(v_toPure_1441_);
    leanh::lean_dec_ref(v_toApplicative_1438_);
    v___f_1442_ = leanh::lean_alloc_closure(
        l_Lean_isInductive___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1442_, 0, v_declName_1437_);
    leanh::lean_closure_set(v___f_1442_, 1, v_toPure_1441_);
    v___x_1443_ = leanh::lean_apply_4(
        v_toBind_1439_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1440_,
        v___f_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l_Lean_isInductive(
    mut v_m_1444_: *mut leanh::LeanObject,
    mut v_inst_1445_: *mut leanh::LeanObject,
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v_declName_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_isInductive___redArg(v_inst_1445_, v_inst_1446_, v_declName_1447_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_isRecCore(
    mut v_env_1449_: *mut leanh::LeanObject,
    mut v_declName_1450_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = 0;
    v___x_1452_ = l_Lean_Environment_findAsync_x3f(v_env_1449_, v_declName_1450_, v___x_1451_);
    if leanh::lean_obj_tag(v___x_1452_) == 1 {
        let mut v_val_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_1454_: u8 = 0;
        v_val_1453_ = leanh::lean_ctor_get(v___x_1452_, 0);
        leanh::lean_inc(v_val_1453_);
        leanh::lean_dec_ref_known(v___x_1452_, 1);
        v_kind_1454_ = leanh::lean_ctor_get_uint8(
            v_val_1453_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        );
        leanh::lean_dec(v_val_1453_);
        if v_kind_1454_ == 7 {
            let mut v___x_1455_: u8 = 0;
            v___x_1455_ = 1;
            return v___x_1455_;
        } else {
            return v___x_1451_;
        }
    } else {
        leanh::lean_dec(v___x_1452_);
        return v___x_1451_;
    }
}
pub unsafe fn l_Lean_isRecCore___boxed(
    mut v_env_1456_: *mut leanh::LeanObject,
    mut v_declName_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_isRecCore(v_env_1456_, v_declName_1457_);
    v_r_1459_ = leanh::lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Lean_isRec___redArg___lam__0(
    mut v_declName_1460_: *mut leanh::LeanObject,
    mut v_toPure_1461_: *mut leanh::LeanObject,
    mut v_____do__lift_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_isRecCore(v_____do__lift_1462_, v_declName_1460_);
    v___x_1464_ = leanh::lean_box((v___x_1463_) as usize);
    v___x_1465_ =
        leanh::lean_apply_2(v_toPure_1461_, leanh::lean_box(0), v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_isRec___redArg(
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_inst_1467_: *mut leanh::LeanObject,
    mut v_declName_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1469_ = leanh::lean_ctor_get(v_inst_1466_, 0);
    leanh::lean_inc_ref(v_toApplicative_1469_);
    v_toBind_1470_ = leanh::lean_ctor_get(v_inst_1466_, 1);
    leanh::lean_inc(v_toBind_1470_);
    leanh::lean_dec_ref(v_inst_1466_);
    v_getEnv_1471_ = leanh::lean_ctor_get(v_inst_1467_, 0);
    leanh::lean_inc(v_getEnv_1471_);
    leanh::lean_dec_ref(v_inst_1467_);
    v_toPure_1472_ = leanh::lean_ctor_get(v_toApplicative_1469_, 1);
    leanh::lean_inc(v_toPure_1472_);
    leanh::lean_dec_ref(v_toApplicative_1469_);
    v___f_1473_ = leanh::lean_alloc_closure(
        l_Lean_isRec___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1473_, 0, v_declName_1468_);
    leanh::lean_closure_set(v___f_1473_, 1, v_toPure_1472_);
    v___x_1474_ = leanh::lean_apply_4(
        v_toBind_1470_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1471_,
        v___f_1473_,
    );
    return v___x_1474_;
}
pub unsafe fn l_Lean_isRec(
    mut v_m_1475_: *mut leanh::LeanObject,
    mut v_inst_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_declName_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_isRec___redArg(v_inst_1476_, v_inst_1477_, v_declName_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_withoutModifyingEnv___redArg___lam__0(
    mut v_inst_1480_: *mut leanh::LeanObject,
    mut v_inst_1481_: *mut leanh::LeanObject,
    mut v_inst_1482_: *mut leanh::LeanObject,
    mut v_x_1483_: *mut leanh::LeanObject,
    mut v_____do__lift_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1487_: *mut leanh::LeanObject,
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v_inst_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1491_ = leanh::lean_ctor_get(v_inst_1487_, 1);
    leanh::lean_inc(v_toBind_1491_);
    v_getEnv_1492_ = leanh::lean_ctor_get(v_inst_1488_, 0);
    leanh::lean_inc(v_getEnv_1492_);
    v___f_1493_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1493_, 0, v_inst_1487_);
    leanh::lean_closure_set(v___f_1493_, 1, v_inst_1489_);
    leanh::lean_closure_set(v___f_1493_, 2, v_inst_1488_);
    leanh::lean_closure_set(v___f_1493_, 3, v_x_1490_);
    v___x_1494_ = leanh::lean_apply_4(
        v_toBind_1491_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1492_,
        v___f_1493_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_withoutModifyingEnv(
    mut v_m_1495_: *mut leanh::LeanObject,
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_inst_1497_: *mut leanh::LeanObject,
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_00_u03b1_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1501_ = leanh::lean_ctor_get(v_inst_1496_, 1);
    leanh::lean_inc(v_toBind_1501_);
    v_getEnv_1502_ = leanh::lean_ctor_get(v_inst_1497_, 0);
    leanh::lean_inc(v_getEnv_1502_);
    v___f_1503_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1503_, 0, v_inst_1496_);
    leanh::lean_closure_set(v___f_1503_, 1, v_inst_1498_);
    leanh::lean_closure_set(v___f_1503_, 2, v_inst_1497_);
    leanh::lean_closure_set(v___f_1503_, 3, v_x_1500_);
    v___x_1504_ = leanh::lean_apply_4(
        v_toBind_1501_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1502_,
        v___f_1503_,
    );
    return v___x_1504_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0(
    mut v_x_1505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1506_ = leanh::lean_ctor_get(v_x_1505_, 0);
    leanh::lean_inc(v_fst_1506_);
    return v_fst_1506_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(v_x_1507_);
    leanh::lean_dec_ref(v_x_1507_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__1(
    mut v_a_1509_: *mut leanh::LeanObject,
    mut v_toPure_1510_: *mut leanh::LeanObject,
    mut v_____do__lift_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1512_, 0, v_a_1509_);
    leanh::lean_ctor_set(v___x_1512_, 1, v_____do__lift_1511_);
    v___x_1513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    v___x_1514_ =
        leanh::lean_apply_2(v_toPure_1510_, leanh::lean_box(0), v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__2(
    mut v_toPure_1515_: *mut leanh::LeanObject,
    mut v_toBind_1516_: *mut leanh::LeanObject,
    mut v_getEnv_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1519_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1519_, 0, v_a_1518_);
    leanh::lean_closure_set(v___f_1519_, 1, v_toPure_1515_);
    v___x_1520_ = leanh::lean_apply_4(
        v_toBind_1516_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1517_,
        v___f_1519_,
    );
    return v___x_1520_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__3(
    mut v_toPure_1521_: *mut leanh::LeanObject,
    mut v_e_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1523_ = leanh::lean_ctor_get(v_e_1522_, 0);
    leanh::lean_inc(v_a_1523_);
    leanh::lean_dec_ref(v_e_1522_);
    v___x_1524_ = leanh::lean_apply_2(v_toPure_1521_, leanh::lean_box(0), v_a_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4(
    mut v___x_1525_: *mut leanh::LeanObject,
    mut v_x_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_1525_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(
    mut v___x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(v___x_1527_, v_x_1528_);
    leanh::lean_dec(v_x_1528_);
    leanh::lean_dec(v___x_1527_);
    return v_res_1529_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__5(
    mut v_toFunctor_1530_: *mut leanh::LeanObject,
    mut v_toBind_1531_: *mut leanh::LeanObject,
    mut v_x_1532_: *mut leanh::LeanObject,
    mut v___f_1533_: *mut leanh::LeanObject,
    mut v_inst_1534_: *mut leanh::LeanObject,
    mut v_inst_1535_: *mut leanh::LeanObject,
    mut v___f_1536_: *mut leanh::LeanObject,
    mut v___f_1537_: *mut leanh::LeanObject,
    mut v_env_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1539_ = leanh::lean_ctor_get(v_toFunctor_1530_, 0);
    leanh::lean_inc(v_map_1539_);
    leanh::lean_dec_ref(v_toFunctor_1530_);
    leanh::lean_inc(v_toBind_1531_);
    v___x_1540_ = leanh::lean_apply_4(
        v_toBind_1531_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_1532_,
        v___f_1533_,
    );
    v___x_1541_ = l_Lean_setEnv___redArg(v_inst_1534_, v_env_1538_);
    v___f_1542_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1542_, 0, v___x_1541_);
    v_y_1543_ = leanh::lean_apply_4(
        v_inst_1535_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1540_,
        v___f_1542_,
    );
    v___x_1544_ = leanh::lean_apply_4(
        v_map_1539_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1536_,
        v_y_1543_,
    );
    v___x_1545_ = leanh::lean_apply_4(
        v_toBind_1531_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1544_,
        v___f_1537_,
    );
    return v___x_1545_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg(
    mut v_inst_1547_: *mut leanh::LeanObject,
    mut v_inst_1548_: *mut leanh::LeanObject,
    mut v_inst_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1551_ = leanh::lean_ctor_get(v_inst_1547_, 0);
    leanh::lean_inc_ref(v_toApplicative_1551_);
    v_toBind_1552_ = leanh::lean_ctor_get(v_inst_1547_, 1);
    leanh::lean_inc_n(v_toBind_1552_, 3);
    leanh::lean_dec_ref(v_inst_1547_);
    v_getEnv_1553_ = leanh::lean_ctor_get(v_inst_1548_, 0);
    leanh::lean_inc_n(v_getEnv_1553_, 2);
    v_toFunctor_1554_ = leanh::lean_ctor_get(v_toApplicative_1551_, 0);
    leanh::lean_inc_ref(v_toFunctor_1554_);
    v_toPure_1555_ = leanh::lean_ctor_get(v_toApplicative_1551_, 1);
    leanh::lean_inc_n(v_toPure_1555_, 2);
    leanh::lean_dec_ref(v_toApplicative_1551_);
    v___f_1556_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1557_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1557_, 0, v_toPure_1555_);
    leanh::lean_closure_set(v___f_1557_, 1, v_toBind_1552_);
    leanh::lean_closure_set(v___f_1557_, 2, v_getEnv_1553_);
    v___f_1558_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1558_, 0, v_toPure_1555_);
    v___f_1559_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_1559_, 0, v_toFunctor_1554_);
    leanh::lean_closure_set(v___f_1559_, 1, v_toBind_1552_);
    leanh::lean_closure_set(v___f_1559_, 2, v_x_1550_);
    leanh::lean_closure_set(v___f_1559_, 3, v___f_1557_);
    leanh::lean_closure_set(v___f_1559_, 4, v_inst_1548_);
    leanh::lean_closure_set(v___f_1559_, 5, v_inst_1549_);
    leanh::lean_closure_set(v___f_1559_, 6, v___f_1556_);
    leanh::lean_closure_set(v___f_1559_, 7, v___f_1558_);
    v___x_1560_ = leanh::lean_apply_4(
        v_toBind_1552_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1553_,
        v___f_1559_,
    );
    return v___x_1560_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27(
    mut v_m_1561_: *mut leanh::LeanObject,
    mut v_inst_1562_: *mut leanh::LeanObject,
    mut v_inst_1563_: *mut leanh::LeanObject,
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_00_u03b1_1565_: *mut leanh::LeanObject,
    mut v_x_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1567_ = leanh::lean_ctor_get(v_inst_1562_, 0);
    leanh::lean_inc_ref(v_toApplicative_1567_);
    v_toBind_1568_ = leanh::lean_ctor_get(v_inst_1562_, 1);
    leanh::lean_inc_n(v_toBind_1568_, 3);
    leanh::lean_dec_ref(v_inst_1562_);
    v_getEnv_1569_ = leanh::lean_ctor_get(v_inst_1563_, 0);
    leanh::lean_inc_n(v_getEnv_1569_, 2);
    v_toFunctor_1570_ = leanh::lean_ctor_get(v_toApplicative_1567_, 0);
    leanh::lean_inc_ref(v_toFunctor_1570_);
    v_toPure_1571_ = leanh::lean_ctor_get(v_toApplicative_1567_, 1);
    leanh::lean_inc_n(v_toPure_1571_, 2);
    leanh::lean_dec_ref(v_toApplicative_1567_);
    v___f_1572_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1573_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1573_, 0, v_toPure_1571_);
    leanh::lean_closure_set(v___f_1573_, 1, v_toBind_1568_);
    leanh::lean_closure_set(v___f_1573_, 2, v_getEnv_1569_);
    v___f_1574_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1574_, 0, v_toPure_1571_);
    v___f_1575_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_1575_, 0, v_toFunctor_1570_);
    leanh::lean_closure_set(v___f_1575_, 1, v_toBind_1568_);
    leanh::lean_closure_set(v___f_1575_, 2, v_x_1566_);
    leanh::lean_closure_set(v___f_1575_, 3, v___f_1573_);
    leanh::lean_closure_set(v___f_1575_, 4, v_inst_1563_);
    leanh::lean_closure_set(v___f_1575_, 5, v_inst_1564_);
    leanh::lean_closure_set(v___f_1575_, 6, v___f_1572_);
    leanh::lean_closure_set(v___f_1575_, 7, v___f_1574_);
    v___x_1576_ = leanh::lean_apply_4(
        v_toBind_1568_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1569_,
        v___f_1575_,
    );
    return v___x_1576_;
}
pub unsafe fn l_Lean_matchConst___redArg___lam__0(
    mut v_declName_1577_: *mut leanh::LeanObject,
    mut v_failK_1578_: *mut leanh::LeanObject,
    mut v_k_1579_: *mut leanh::LeanObject,
    mut v_us_1580_: *mut leanh::LeanObject,
    mut v_____do__lift_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1582_ = 0;
    v___x_1583_ = l_Lean_Environment_find_x3f(v_____do__lift_1581_, v_declName_1577_, v___x_1582_);
    if leanh::lean_obj_tag(v___x_1583_) == 0 {
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_us_1580_);
        leanh::lean_dec(v_k_1579_);
        v___x_1584_ = leanh::lean_box(0);
        v___x_1585_ = leanh::lean_apply_1(v_failK_1578_, v___x_1584_);
        return v___x_1585_;
    } else {
        let mut v_val_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_failK_1578_);
        v_val_1586_ = leanh::lean_ctor_get(v___x_1583_, 0);
        leanh::lean_inc(v_val_1586_);
        leanh::lean_dec_ref_known(v___x_1583_, 1);
        v___x_1587_ = leanh::lean_apply_2(v_k_1579_, v_val_1586_, v_us_1580_);
        return v___x_1587_;
    }
}
pub unsafe fn l_Lean_matchConst___redArg(
    mut v_inst_1588_: *mut leanh::LeanObject,
    mut v_inst_1589_: *mut leanh::LeanObject,
    mut v_e_1590_: *mut leanh::LeanObject,
    mut v_failK_1591_: *mut leanh::LeanObject,
    mut v_k_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1590_) == 4 {
        let mut v_toBind_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1593_ = leanh::lean_ctor_get(v_inst_1588_, 1);
        leanh::lean_inc(v_toBind_1593_);
        leanh::lean_dec_ref(v_inst_1588_);
        v_declName_1594_ = leanh::lean_ctor_get(v_e_1590_, 0);
        leanh::lean_inc(v_declName_1594_);
        v_us_1595_ = leanh::lean_ctor_get(v_e_1590_, 1);
        leanh::lean_inc(v_us_1595_);
        leanh::lean_dec_ref_known(v_e_1590_, 2);
        v_getEnv_1596_ = leanh::lean_ctor_get(v_inst_1589_, 0);
        leanh::lean_inc(v_getEnv_1596_);
        leanh::lean_dec_ref(v_inst_1589_);
        v___f_1597_ = leanh::lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1597_, 0, v_declName_1594_);
        leanh::lean_closure_set(v___f_1597_, 1, v_failK_1591_);
        leanh::lean_closure_set(v___f_1597_, 2, v_k_1592_);
        leanh::lean_closure_set(v___f_1597_, 3, v_us_1595_);
        v___x_1598_ = leanh::lean_apply_4(
            v_toBind_1593_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1596_,
            v___f_1597_,
        );
        return v___x_1598_;
    } else {
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1592_);
        leanh::lean_dec_ref(v_e_1590_);
        leanh::lean_dec_ref(v_inst_1589_);
        leanh::lean_dec_ref(v_inst_1588_);
        v___x_1599_ = leanh::lean_box(0);
        v___x_1600_ = leanh::lean_apply_1(v_failK_1591_, v___x_1599_);
        return v___x_1600_;
    }
}
pub unsafe fn l_Lean_matchConst(
    mut v_m_1601_: *mut leanh::LeanObject,
    mut v_00_u03b1_1602_: *mut leanh::LeanObject,
    mut v_inst_1603_: *mut leanh::LeanObject,
    mut v_inst_1604_: *mut leanh::LeanObject,
    mut v_e_1605_: *mut leanh::LeanObject,
    mut v_failK_1606_: *mut leanh::LeanObject,
    mut v_k_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1605_) == 4 {
        let mut v_toBind_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1608_ = leanh::lean_ctor_get(v_inst_1603_, 1);
        leanh::lean_inc(v_toBind_1608_);
        leanh::lean_dec_ref(v_inst_1603_);
        v_declName_1609_ = leanh::lean_ctor_get(v_e_1605_, 0);
        leanh::lean_inc(v_declName_1609_);
        v_us_1610_ = leanh::lean_ctor_get(v_e_1605_, 1);
        leanh::lean_inc(v_us_1610_);
        leanh::lean_dec_ref_known(v_e_1605_, 2);
        v_getEnv_1611_ = leanh::lean_ctor_get(v_inst_1604_, 0);
        leanh::lean_inc(v_getEnv_1611_);
        leanh::lean_dec_ref(v_inst_1604_);
        v___f_1612_ = leanh::lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1612_, 0, v_declName_1609_);
        leanh::lean_closure_set(v___f_1612_, 1, v_failK_1606_);
        leanh::lean_closure_set(v___f_1612_, 2, v_k_1607_);
        leanh::lean_closure_set(v___f_1612_, 3, v_us_1610_);
        v___x_1613_ = leanh::lean_apply_4(
            v_toBind_1608_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1611_,
            v___f_1612_,
        );
        return v___x_1613_;
    } else {
        let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1607_);
        leanh::lean_dec_ref(v_e_1605_);
        leanh::lean_dec_ref(v_inst_1604_);
        leanh::lean_dec_ref(v_inst_1603_);
        v___x_1614_ = leanh::lean_box(0);
        v___x_1615_ = leanh::lean_apply_1(v_failK_1606_, v___x_1614_);
        return v___x_1615_;
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg___lam__0(
    mut v_declName_1616_: *mut leanh::LeanObject,
    mut v_failK_1617_: *mut leanh::LeanObject,
    mut v_k_1618_: *mut leanh::LeanObject,
    mut v_us_1619_: *mut leanh::LeanObject,
    mut v_____do__lift_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = 0;
    v___x_1622_ = l_Lean_Environment_find_x3f(v_____do__lift_1620_, v_declName_1616_, v___x_1621_);
    if leanh::lean_obj_tag(v___x_1622_) == 0 {
        let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_us_1619_);
        leanh::lean_dec(v_k_1618_);
        v___x_1623_ = leanh::lean_box(0);
        v___x_1624_ = leanh::lean_apply_1(v_failK_1617_, v___x_1623_);
        return v___x_1624_;
    } else {
        let mut v_val_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1625_ = leanh::lean_ctor_get(v___x_1622_, 0);
        leanh::lean_inc(v_val_1625_);
        leanh::lean_dec_ref_known(v___x_1622_, 1);
        if leanh::lean_obj_tag(v_val_1625_) == 5 {
            let mut v_val_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_failK_1617_);
            v_val_1626_ = leanh::lean_ctor_get(v_val_1625_, 0);
            leanh::lean_inc_ref(v_val_1626_);
            leanh::lean_dec_ref_known(v_val_1625_, 1);
            v___x_1627_ = leanh::lean_apply_2(v_k_1618_, v_val_1626_, v_us_1619_);
            return v___x_1627_;
        } else {
            let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_1625_);
            leanh::lean_dec(v_us_1619_);
            leanh::lean_dec(v_k_1618_);
            v___x_1628_ = leanh::lean_box(0);
            v___x_1629_ = leanh::lean_apply_1(v_failK_1617_, v___x_1628_);
            return v___x_1629_;
        }
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg(
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_inst_1631_: *mut leanh::LeanObject,
    mut v_e_1632_: *mut leanh::LeanObject,
    mut v_failK_1633_: *mut leanh::LeanObject,
    mut v_k_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1632_) == 4 {
        let mut v_toBind_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1635_ = leanh::lean_ctor_get(v_inst_1630_, 1);
        leanh::lean_inc(v_toBind_1635_);
        leanh::lean_dec_ref(v_inst_1630_);
        v_declName_1636_ = leanh::lean_ctor_get(v_e_1632_, 0);
        leanh::lean_inc(v_declName_1636_);
        v_us_1637_ = leanh::lean_ctor_get(v_e_1632_, 1);
        leanh::lean_inc(v_us_1637_);
        leanh::lean_dec_ref_known(v_e_1632_, 2);
        v_getEnv_1638_ = leanh::lean_ctor_get(v_inst_1631_, 0);
        leanh::lean_inc(v_getEnv_1638_);
        leanh::lean_dec_ref(v_inst_1631_);
        v___f_1639_ = leanh::lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1639_, 0, v_declName_1636_);
        leanh::lean_closure_set(v___f_1639_, 1, v_failK_1633_);
        leanh::lean_closure_set(v___f_1639_, 2, v_k_1634_);
        leanh::lean_closure_set(v___f_1639_, 3, v_us_1637_);
        v___x_1640_ = leanh::lean_apply_4(
            v_toBind_1635_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1638_,
            v___f_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1634_);
        leanh::lean_dec_ref(v_e_1632_);
        leanh::lean_dec_ref(v_inst_1631_);
        leanh::lean_dec_ref(v_inst_1630_);
        v___x_1641_ = leanh::lean_box(0);
        v___x_1642_ = leanh::lean_apply_1(v_failK_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l_Lean_matchConstInduct(
    mut v_m_1643_: *mut leanh::LeanObject,
    mut v_00_u03b1_1644_: *mut leanh::LeanObject,
    mut v_inst_1645_: *mut leanh::LeanObject,
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_e_1647_: *mut leanh::LeanObject,
    mut v_failK_1648_: *mut leanh::LeanObject,
    mut v_k_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1647_) == 4 {
        let mut v_toBind_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1650_ = leanh::lean_ctor_get(v_inst_1645_, 1);
        leanh::lean_inc(v_toBind_1650_);
        leanh::lean_dec_ref(v_inst_1645_);
        v_declName_1651_ = leanh::lean_ctor_get(v_e_1647_, 0);
        leanh::lean_inc(v_declName_1651_);
        v_us_1652_ = leanh::lean_ctor_get(v_e_1647_, 1);
        leanh::lean_inc(v_us_1652_);
        leanh::lean_dec_ref_known(v_e_1647_, 2);
        v_getEnv_1653_ = leanh::lean_ctor_get(v_inst_1646_, 0);
        leanh::lean_inc(v_getEnv_1653_);
        leanh::lean_dec_ref(v_inst_1646_);
        v___f_1654_ = leanh::lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1654_, 0, v_declName_1651_);
        leanh::lean_closure_set(v___f_1654_, 1, v_failK_1648_);
        leanh::lean_closure_set(v___f_1654_, 2, v_k_1649_);
        leanh::lean_closure_set(v___f_1654_, 3, v_us_1652_);
        v___x_1655_ = leanh::lean_apply_4(
            v_toBind_1650_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1653_,
            v___f_1654_,
        );
        return v___x_1655_;
    } else {
        let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1649_);
        leanh::lean_dec_ref(v_e_1647_);
        leanh::lean_dec_ref(v_inst_1646_);
        leanh::lean_dec_ref(v_inst_1645_);
        v___x_1656_ = leanh::lean_box(0);
        v___x_1657_ = leanh::lean_apply_1(v_failK_1648_, v___x_1656_);
        return v___x_1657_;
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg___lam__0(
    mut v_declName_1658_: *mut leanh::LeanObject,
    mut v_failK_1659_: *mut leanh::LeanObject,
    mut v_k_1660_: *mut leanh::LeanObject,
    mut v_us_1661_: *mut leanh::LeanObject,
    mut v_____do__lift_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = 0;
    v___x_1664_ = l_Lean_Environment_find_x3f(v_____do__lift_1662_, v_declName_1658_, v___x_1663_);
    if leanh::lean_obj_tag(v___x_1664_) == 0 {
        let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_us_1661_);
        leanh::lean_dec(v_k_1660_);
        v___x_1665_ = leanh::lean_box(0);
        v___x_1666_ = leanh::lean_apply_1(v_failK_1659_, v___x_1665_);
        return v___x_1666_;
    } else {
        let mut v_val_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1667_ = leanh::lean_ctor_get(v___x_1664_, 0);
        leanh::lean_inc(v_val_1667_);
        leanh::lean_dec_ref_known(v___x_1664_, 1);
        if leanh::lean_obj_tag(v_val_1667_) == 6 {
            let mut v_val_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_failK_1659_);
            v_val_1668_ = leanh::lean_ctor_get(v_val_1667_, 0);
            leanh::lean_inc_ref(v_val_1668_);
            leanh::lean_dec_ref_known(v_val_1667_, 1);
            v___x_1669_ = leanh::lean_apply_2(v_k_1660_, v_val_1668_, v_us_1661_);
            return v___x_1669_;
        } else {
            let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_1667_);
            leanh::lean_dec(v_us_1661_);
            leanh::lean_dec(v_k_1660_);
            v___x_1670_ = leanh::lean_box(0);
            v___x_1671_ = leanh::lean_apply_1(v_failK_1659_, v___x_1670_);
            return v___x_1671_;
        }
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg(
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_e_1674_: *mut leanh::LeanObject,
    mut v_failK_1675_: *mut leanh::LeanObject,
    mut v_k_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1674_) == 4 {
        let mut v_toBind_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1677_ = leanh::lean_ctor_get(v_inst_1672_, 1);
        leanh::lean_inc(v_toBind_1677_);
        leanh::lean_dec_ref(v_inst_1672_);
        v_declName_1678_ = leanh::lean_ctor_get(v_e_1674_, 0);
        leanh::lean_inc(v_declName_1678_);
        v_us_1679_ = leanh::lean_ctor_get(v_e_1674_, 1);
        leanh::lean_inc(v_us_1679_);
        leanh::lean_dec_ref_known(v_e_1674_, 2);
        v_getEnv_1680_ = leanh::lean_ctor_get(v_inst_1673_, 0);
        leanh::lean_inc(v_getEnv_1680_);
        leanh::lean_dec_ref(v_inst_1673_);
        v___f_1681_ = leanh::lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1681_, 0, v_declName_1678_);
        leanh::lean_closure_set(v___f_1681_, 1, v_failK_1675_);
        leanh::lean_closure_set(v___f_1681_, 2, v_k_1676_);
        leanh::lean_closure_set(v___f_1681_, 3, v_us_1679_);
        v___x_1682_ = leanh::lean_apply_4(
            v_toBind_1677_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1680_,
            v___f_1681_,
        );
        return v___x_1682_;
    } else {
        let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1676_);
        leanh::lean_dec_ref(v_e_1674_);
        leanh::lean_dec_ref(v_inst_1673_);
        leanh::lean_dec_ref(v_inst_1672_);
        v___x_1683_ = leanh::lean_box(0);
        v___x_1684_ = leanh::lean_apply_1(v_failK_1675_, v___x_1683_);
        return v___x_1684_;
    }
}
pub unsafe fn l_Lean_matchConstCtor(
    mut v_m_1685_: *mut leanh::LeanObject,
    mut v_00_u03b1_1686_: *mut leanh::LeanObject,
    mut v_inst_1687_: *mut leanh::LeanObject,
    mut v_inst_1688_: *mut leanh::LeanObject,
    mut v_e_1689_: *mut leanh::LeanObject,
    mut v_failK_1690_: *mut leanh::LeanObject,
    mut v_k_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1689_) == 4 {
        let mut v_toBind_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1692_ = leanh::lean_ctor_get(v_inst_1687_, 1);
        leanh::lean_inc(v_toBind_1692_);
        leanh::lean_dec_ref(v_inst_1687_);
        v_declName_1693_ = leanh::lean_ctor_get(v_e_1689_, 0);
        leanh::lean_inc(v_declName_1693_);
        v_us_1694_ = leanh::lean_ctor_get(v_e_1689_, 1);
        leanh::lean_inc(v_us_1694_);
        leanh::lean_dec_ref_known(v_e_1689_, 2);
        v_getEnv_1695_ = leanh::lean_ctor_get(v_inst_1688_, 0);
        leanh::lean_inc(v_getEnv_1695_);
        leanh::lean_dec_ref(v_inst_1688_);
        v___f_1696_ = leanh::lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1696_, 0, v_declName_1693_);
        leanh::lean_closure_set(v___f_1696_, 1, v_failK_1690_);
        leanh::lean_closure_set(v___f_1696_, 2, v_k_1691_);
        leanh::lean_closure_set(v___f_1696_, 3, v_us_1694_);
        v___x_1697_ = leanh::lean_apply_4(
            v_toBind_1692_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1695_,
            v___f_1696_,
        );
        return v___x_1697_;
    } else {
        let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1691_);
        leanh::lean_dec_ref(v_e_1689_);
        leanh::lean_dec_ref(v_inst_1688_);
        leanh::lean_dec_ref(v_inst_1687_);
        v___x_1698_ = leanh::lean_box(0);
        v___x_1699_ = leanh::lean_apply_1(v_failK_1690_, v___x_1698_);
        return v___x_1699_;
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg___lam__0(
    mut v_declName_1700_: *mut leanh::LeanObject,
    mut v_failK_1701_: *mut leanh::LeanObject,
    mut v_k_1702_: *mut leanh::LeanObject,
    mut v_us_1703_: *mut leanh::LeanObject,
    mut v_____do__lift_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = 0;
    v___x_1706_ = l_Lean_Environment_find_x3f(v_____do__lift_1704_, v_declName_1700_, v___x_1705_);
    if leanh::lean_obj_tag(v___x_1706_) == 0 {
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_us_1703_);
        leanh::lean_dec(v_k_1702_);
        v___x_1707_ = leanh::lean_box(0);
        v___x_1708_ = leanh::lean_apply_1(v_failK_1701_, v___x_1707_);
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1709_ = leanh::lean_ctor_get(v___x_1706_, 0);
        leanh::lean_inc(v_val_1709_);
        leanh::lean_dec_ref_known(v___x_1706_, 1);
        if leanh::lean_obj_tag(v_val_1709_) == 7 {
            let mut v_val_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_failK_1701_);
            v_val_1710_ = leanh::lean_ctor_get(v_val_1709_, 0);
            leanh::lean_inc_ref(v_val_1710_);
            leanh::lean_dec_ref_known(v_val_1709_, 1);
            v___x_1711_ = leanh::lean_apply_2(v_k_1702_, v_val_1710_, v_us_1703_);
            return v___x_1711_;
        } else {
            let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_1709_);
            leanh::lean_dec(v_us_1703_);
            leanh::lean_dec(v_k_1702_);
            v___x_1712_ = leanh::lean_box(0);
            v___x_1713_ = leanh::lean_apply_1(v_failK_1701_, v___x_1712_);
            return v___x_1713_;
        }
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg(
    mut v_inst_1714_: *mut leanh::LeanObject,
    mut v_inst_1715_: *mut leanh::LeanObject,
    mut v_e_1716_: *mut leanh::LeanObject,
    mut v_failK_1717_: *mut leanh::LeanObject,
    mut v_k_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1716_) == 4 {
        let mut v_toBind_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1719_ = leanh::lean_ctor_get(v_inst_1714_, 1);
        leanh::lean_inc(v_toBind_1719_);
        leanh::lean_dec_ref(v_inst_1714_);
        v_declName_1720_ = leanh::lean_ctor_get(v_e_1716_, 0);
        leanh::lean_inc(v_declName_1720_);
        v_us_1721_ = leanh::lean_ctor_get(v_e_1716_, 1);
        leanh::lean_inc(v_us_1721_);
        leanh::lean_dec_ref_known(v_e_1716_, 2);
        v_getEnv_1722_ = leanh::lean_ctor_get(v_inst_1715_, 0);
        leanh::lean_inc(v_getEnv_1722_);
        leanh::lean_dec_ref(v_inst_1715_);
        v___f_1723_ = leanh::lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1723_, 0, v_declName_1720_);
        leanh::lean_closure_set(v___f_1723_, 1, v_failK_1717_);
        leanh::lean_closure_set(v___f_1723_, 2, v_k_1718_);
        leanh::lean_closure_set(v___f_1723_, 3, v_us_1721_);
        v___x_1724_ = leanh::lean_apply_4(
            v_toBind_1719_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1722_,
            v___f_1723_,
        );
        return v___x_1724_;
    } else {
        let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1718_);
        leanh::lean_dec_ref(v_e_1716_);
        leanh::lean_dec_ref(v_inst_1715_);
        leanh::lean_dec_ref(v_inst_1714_);
        v___x_1725_ = leanh::lean_box(0);
        v___x_1726_ = leanh::lean_apply_1(v_failK_1717_, v___x_1725_);
        return v___x_1726_;
    }
}
pub unsafe fn l_Lean_matchConstRec(
    mut v_m_1727_: *mut leanh::LeanObject,
    mut v_00_u03b1_1728_: *mut leanh::LeanObject,
    mut v_inst_1729_: *mut leanh::LeanObject,
    mut v_inst_1730_: *mut leanh::LeanObject,
    mut v_e_1731_: *mut leanh::LeanObject,
    mut v_failK_1732_: *mut leanh::LeanObject,
    mut v_k_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_1731_) == 4 {
        let mut v_toBind_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1734_ = leanh::lean_ctor_get(v_inst_1729_, 1);
        leanh::lean_inc(v_toBind_1734_);
        leanh::lean_dec_ref(v_inst_1729_);
        v_declName_1735_ = leanh::lean_ctor_get(v_e_1731_, 0);
        leanh::lean_inc(v_declName_1735_);
        v_us_1736_ = leanh::lean_ctor_get(v_e_1731_, 1);
        leanh::lean_inc(v_us_1736_);
        leanh::lean_dec_ref_known(v_e_1731_, 2);
        v_getEnv_1737_ = leanh::lean_ctor_get(v_inst_1730_, 0);
        leanh::lean_inc(v_getEnv_1737_);
        leanh::lean_dec_ref(v_inst_1730_);
        v___f_1738_ = leanh::lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1738_, 0, v_declName_1735_);
        leanh::lean_closure_set(v___f_1738_, 1, v_failK_1732_);
        leanh::lean_closure_set(v___f_1738_, 2, v_k_1733_);
        leanh::lean_closure_set(v___f_1738_, 3, v_us_1736_);
        v___x_1739_ = leanh::lean_apply_4(
            v_toBind_1734_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_1737_,
            v___f_1738_,
        );
        return v___x_1739_;
    } else {
        let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1733_);
        leanh::lean_dec_ref(v_e_1731_);
        leanh::lean_dec_ref(v_inst_1730_);
        leanh::lean_dec_ref(v_inst_1729_);
        v___x_1740_ = leanh::lean_box(0);
        v___x_1741_ = leanh::lean_apply_1(v_failK_1732_, v___x_1740_);
        return v___x_1741_;
    }
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0(
    mut v_constName_1742_: *mut leanh::LeanObject,
    mut v_skipRealize_1743_: u8,
    mut v_toPure_1744_: *mut leanh::LeanObject,
    mut v_____do__lift_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ =
        l_Lean_Environment_contains(v_____do__lift_1745_, v_constName_1742_, v_skipRealize_1743_);
    v___x_1747_ = leanh::lean_box((v___x_1746_) as usize);
    v___x_1748_ =
        leanh::lean_apply_2(v_toPure_1744_, leanh::lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0___boxed(
    mut v_constName_1749_: *mut leanh::LeanObject,
    mut v_skipRealize_1750_: *mut leanh::LeanObject,
    mut v_toPure_1751_: *mut leanh::LeanObject,
    mut v_____do__lift_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1753_: u8 = 0;
    let mut v_res_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1753_ = (leanh::lean_unbox(v_skipRealize_1750_) as u8);
    v_res_1754_ = l_Lean_hasConst___redArg___lam__0(
        v_constName_1749_,
        v_skipRealize_boxed_1753_,
        v_toPure_1751_,
        v_____do__lift_1752_,
    );
    return v_res_1754_;
}
pub unsafe fn l_Lean_hasConst___redArg(
    mut v_inst_1755_: *mut leanh::LeanObject,
    mut v_inst_1756_: *mut leanh::LeanObject,
    mut v_constName_1757_: *mut leanh::LeanObject,
    mut v_skipRealize_1758_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1759_ = leanh::lean_ctor_get(v_inst_1755_, 0);
    leanh::lean_inc_ref(v_toApplicative_1759_);
    v_toBind_1760_ = leanh::lean_ctor_get(v_inst_1755_, 1);
    leanh::lean_inc(v_toBind_1760_);
    leanh::lean_dec_ref(v_inst_1755_);
    v_getEnv_1761_ = leanh::lean_ctor_get(v_inst_1756_, 0);
    leanh::lean_inc(v_getEnv_1761_);
    leanh::lean_dec_ref(v_inst_1756_);
    v_toPure_1762_ = leanh::lean_ctor_get(v_toApplicative_1759_, 1);
    leanh::lean_inc(v_toPure_1762_);
    leanh::lean_dec_ref(v_toApplicative_1759_);
    v___x_1763_ = leanh::lean_box((v_skipRealize_1758_) as usize);
    v___f_1764_ = leanh::lean_alloc_closure(
        l_Lean_hasConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1764_, 0, v_constName_1757_);
    leanh::lean_closure_set(v___f_1764_, 1, v___x_1763_);
    leanh::lean_closure_set(v___f_1764_, 2, v_toPure_1762_);
    v___x_1765_ = leanh::lean_apply_4(
        v_toBind_1760_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1761_,
        v___f_1764_,
    );
    return v___x_1765_;
}
pub unsafe fn l_Lean_hasConst___redArg___boxed(
    mut v_inst_1766_: *mut leanh::LeanObject,
    mut v_inst_1767_: *mut leanh::LeanObject,
    mut v_constName_1768_: *mut leanh::LeanObject,
    mut v_skipRealize_1769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1770_: u8 = 0;
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1770_ = (leanh::lean_unbox(v_skipRealize_1769_) as u8);
    v_res_1771_ = l_Lean_hasConst___redArg(
        v_inst_1766_,
        v_inst_1767_,
        v_constName_1768_,
        v_skipRealize_boxed_1770_,
    );
    return v_res_1771_;
}
pub unsafe fn l_Lean_hasConst(
    mut v_m_1772_: *mut leanh::LeanObject,
    mut v_inst_1773_: *mut leanh::LeanObject,
    mut v_inst_1774_: *mut leanh::LeanObject,
    mut v_constName_1775_: *mut leanh::LeanObject,
    mut v_skipRealize_1776_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_hasConst___redArg(
        v_inst_1773_,
        v_inst_1774_,
        v_constName_1775_,
        v_skipRealize_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_hasConst___boxed(
    mut v_m_1778_: *mut leanh::LeanObject,
    mut v_inst_1779_: *mut leanh::LeanObject,
    mut v_inst_1780_: *mut leanh::LeanObject,
    mut v_constName_1781_: *mut leanh::LeanObject,
    mut v_skipRealize_1782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1783_: u8 = 0;
    let mut v_res_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1783_ = (leanh::lean_unbox(v_skipRealize_1782_) as u8);
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
    mut v_constName_1785_: *mut leanh::LeanObject,
    mut v_inst_1786_: *mut leanh::LeanObject,
    mut v_inst_1787_: *mut leanh::LeanObject,
    mut v_inst_1788_: *mut leanh::LeanObject,
    mut v_toPure_1789_: *mut leanh::LeanObject,
    mut v_____do__lift_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = 0;
    leanh::lean_inc(v_constName_1785_);
    v___x_1792_ = l_Lean_Environment_find_x3f(v_____do__lift_1790_, v_constName_1785_, v___x_1791_);
    if leanh::lean_obj_tag(v___x_1792_) == 0 {
        let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1789_);
        v___x_1793_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1786_,
            v_inst_1787_,
            v_inst_1788_,
            v_constName_1785_,
        );
        return v___x_1793_;
    } else {
        let mut v_val_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1788_);
        leanh::lean_dec_ref(v_inst_1787_);
        leanh::lean_dec_ref(v_inst_1786_);
        leanh::lean_dec(v_constName_1785_);
        v_val_1794_ = leanh::lean_ctor_get(v___x_1792_, 0);
        leanh::lean_inc(v_val_1794_);
        leanh::lean_dec_ref_known(v___x_1792_, 1);
        v___x_1795_ =
            leanh::lean_apply_2(v_toPure_1789_, leanh::lean_box(0), v_val_1794_);
        return v___x_1795_;
    }
}
pub unsafe fn l_Lean_getConstInfo___redArg(
    mut v_inst_1796_: *mut leanh::LeanObject,
    mut v_inst_1797_: *mut leanh::LeanObject,
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_constName_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1800_ = leanh::lean_ctor_get(v_inst_1796_, 0);
    v_toBind_1801_ = leanh::lean_ctor_get(v_inst_1796_, 1);
    leanh::lean_inc(v_toBind_1801_);
    v_getEnv_1802_ = leanh::lean_ctor_get(v_inst_1797_, 0);
    leanh::lean_inc(v_getEnv_1802_);
    v_toPure_1803_ = leanh::lean_ctor_get(v_toApplicative_1800_, 1);
    leanh::lean_inc(v_toPure_1803_);
    v___f_1804_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfo___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1804_, 0, v_constName_1799_);
    leanh::lean_closure_set(v___f_1804_, 1, v_inst_1796_);
    leanh::lean_closure_set(v___f_1804_, 2, v_inst_1797_);
    leanh::lean_closure_set(v___f_1804_, 3, v_inst_1798_);
    leanh::lean_closure_set(v___f_1804_, 4, v_toPure_1803_);
    v___x_1805_ = leanh::lean_apply_4(
        v_toBind_1801_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1802_,
        v___f_1804_,
    );
    return v___x_1805_;
}
pub unsafe fn l_Lean_getConstInfo(
    mut v_m_1806_: *mut leanh::LeanObject,
    mut v_inst_1807_: *mut leanh::LeanObject,
    mut v_inst_1808_: *mut leanh::LeanObject,
    mut v_inst_1809_: *mut leanh::LeanObject,
    mut v_constName_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ =
        l_Lean_getConstInfo___redArg(v_inst_1807_, v_inst_1808_, v_inst_1809_, v_constName_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Lean_getConstVal___redArg___lam__0(
    mut v_constName_1812_: *mut leanh::LeanObject,
    mut v_inst_1813_: *mut leanh::LeanObject,
    mut v_inst_1814_: *mut leanh::LeanObject,
    mut v_inst_1815_: *mut leanh::LeanObject,
    mut v_toPure_1816_: *mut leanh::LeanObject,
    mut v_____do__lift_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = 0;
    leanh::lean_inc(v_constName_1812_);
    v___x_1819_ =
        l_Lean_Environment_findConstVal_x3f(v_____do__lift_1817_, v_constName_1812_, v___x_1818_);
    if leanh::lean_obj_tag(v___x_1819_) == 0 {
        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1816_);
        v___x_1820_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1813_,
            v_inst_1814_,
            v_inst_1815_,
            v_constName_1812_,
        );
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1815_);
        leanh::lean_dec_ref(v_inst_1814_);
        leanh::lean_dec_ref(v_inst_1813_);
        leanh::lean_dec(v_constName_1812_);
        v_val_1821_ = leanh::lean_ctor_get(v___x_1819_, 0);
        leanh::lean_inc(v_val_1821_);
        leanh::lean_dec_ref_known(v___x_1819_, 1);
        v___x_1822_ =
            leanh::lean_apply_2(v_toPure_1816_, leanh::lean_box(0), v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l_Lean_getConstVal___redArg(
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_inst_1824_: *mut leanh::LeanObject,
    mut v_inst_1825_: *mut leanh::LeanObject,
    mut v_constName_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1827_ = leanh::lean_ctor_get(v_inst_1823_, 0);
    v_toBind_1828_ = leanh::lean_ctor_get(v_inst_1823_, 1);
    leanh::lean_inc(v_toBind_1828_);
    v_getEnv_1829_ = leanh::lean_ctor_get(v_inst_1824_, 0);
    leanh::lean_inc(v_getEnv_1829_);
    v_toPure_1830_ = leanh::lean_ctor_get(v_toApplicative_1827_, 1);
    leanh::lean_inc(v_toPure_1830_);
    v___f_1831_ = leanh::lean_alloc_closure(
        l_Lean_getConstVal___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1831_, 0, v_constName_1826_);
    leanh::lean_closure_set(v___f_1831_, 1, v_inst_1823_);
    leanh::lean_closure_set(v___f_1831_, 2, v_inst_1824_);
    leanh::lean_closure_set(v___f_1831_, 3, v_inst_1825_);
    leanh::lean_closure_set(v___f_1831_, 4, v_toPure_1830_);
    v___x_1832_ = leanh::lean_apply_4(
        v_toBind_1828_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1829_,
        v___f_1831_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Lean_getConstVal(
    mut v_m_1833_: *mut leanh::LeanObject,
    mut v_inst_1834_: *mut leanh::LeanObject,
    mut v_inst_1835_: *mut leanh::LeanObject,
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_constName_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ =
        l_Lean_getConstVal___redArg(v_inst_1834_, v_inst_1835_, v_inst_1836_, v_constName_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0(
    mut v_constName_1839_: *mut leanh::LeanObject,
    mut v_skipRealize_1840_: u8,
    mut v_inst_1841_: *mut leanh::LeanObject,
    mut v_inst_1842_: *mut leanh::LeanObject,
    mut v_inst_1843_: *mut leanh::LeanObject,
    mut v_toPure_1844_: *mut leanh::LeanObject,
    mut v_____do__lift_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_constName_1839_);
    v___x_1846_ = l_Lean_Environment_findAsync_x3f(
        v_____do__lift_1845_,
        v_constName_1839_,
        v_skipRealize_1840_,
    );
    if leanh::lean_obj_tag(v___x_1846_) == 0 {
        let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1844_);
        v___x_1847_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1841_,
            v_inst_1842_,
            v_inst_1843_,
            v_constName_1839_,
        );
        return v___x_1847_;
    } else {
        let mut v_val_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1843_);
        leanh::lean_dec_ref(v_inst_1842_);
        leanh::lean_dec_ref(v_inst_1841_);
        leanh::lean_dec(v_constName_1839_);
        v_val_1848_ = leanh::lean_ctor_get(v___x_1846_, 0);
        leanh::lean_inc(v_val_1848_);
        leanh::lean_dec_ref_known(v___x_1846_, 1);
        v___x_1849_ =
            leanh::lean_apply_2(v_toPure_1844_, leanh::lean_box(0), v_val_1848_);
        return v___x_1849_;
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(
    mut v_constName_1850_: *mut leanh::LeanObject,
    mut v_skipRealize_1851_: *mut leanh::LeanObject,
    mut v_inst_1852_: *mut leanh::LeanObject,
    mut v_inst_1853_: *mut leanh::LeanObject,
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_toPure_1855_: *mut leanh::LeanObject,
    mut v_____do__lift_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1857_: u8 = 0;
    let mut v_res_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1857_ = (leanh::lean_unbox(v_skipRealize_1851_) as u8);
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
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_inst_1860_: *mut leanh::LeanObject,
    mut v_inst_1861_: *mut leanh::LeanObject,
    mut v_constName_1862_: *mut leanh::LeanObject,
    mut v_skipRealize_1863_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = leanh::lean_ctor_get(v_inst_1859_, 0);
    v_toBind_1865_ = leanh::lean_ctor_get(v_inst_1859_, 1);
    leanh::lean_inc(v_toBind_1865_);
    v_getEnv_1866_ = leanh::lean_ctor_get(v_inst_1860_, 0);
    leanh::lean_inc(v_getEnv_1866_);
    v_toPure_1867_ = leanh::lean_ctor_get(v_toApplicative_1864_, 1);
    leanh::lean_inc(v_toPure_1867_);
    v___x_1868_ = leanh::lean_box((v_skipRealize_1863_) as usize);
    v___f_1869_ = leanh::lean_alloc_closure(
        l_Lean_getAsyncConstInfo___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1869_, 0, v_constName_1862_);
    leanh::lean_closure_set(v___f_1869_, 1, v___x_1868_);
    leanh::lean_closure_set(v___f_1869_, 2, v_inst_1859_);
    leanh::lean_closure_set(v___f_1869_, 3, v_inst_1860_);
    leanh::lean_closure_set(v___f_1869_, 4, v_inst_1861_);
    leanh::lean_closure_set(v___f_1869_, 5, v_toPure_1867_);
    v___x_1870_ = leanh::lean_apply_4(
        v_toBind_1865_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1866_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___boxed(
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_constName_1874_: *mut leanh::LeanObject,
    mut v_skipRealize_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1876_: u8 = 0;
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1876_ = (leanh::lean_unbox(v_skipRealize_1875_) as u8);
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
    mut v_m_1878_: *mut leanh::LeanObject,
    mut v_inst_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_inst_1881_: *mut leanh::LeanObject,
    mut v_constName_1882_: *mut leanh::LeanObject,
    mut v_skipRealize_1883_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_inst_1887_: *mut leanh::LeanObject,
    mut v_inst_1888_: *mut leanh::LeanObject,
    mut v_constName_1889_: *mut leanh::LeanObject,
    mut v_skipRealize_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_1891_: u8 = 0;
    let mut v_res_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1891_ = (leanh::lean_unbox(v_skipRealize_1890_) as u8);
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
    mut v_msg_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = leanh::lean_box(0);
    v___x_1895_ = lean_panic_fn_borrowed(v___x_1894_, v_msg_1893_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lean_isInductiveCore_x3f___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1900_ = leanh::lean_unsigned_to_nat(11);
    v___x_1901_ = leanh::lean_unsigned_to_nat(105);
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
    mut v_env_1905_: *mut leanh::LeanObject,
    mut v_declName_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v_kind_1913_: u8 = 0;
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1907_ = 0;
                v___x_1908_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1905_, v_declName_1906_, v___x_1907_);
                if leanh::lean_obj_tag(v___x_1908_) == 1 {
                    v_val_1909_ = leanh::lean_ctor_get(v___x_1908_, 0);
                    v_isSharedCheck_1922_ = (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v___x_1911_ = v___x_1908_;
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1909_);
                        leanh::lean_dec(v___x_1908_);
                        v___x_1911_ = leanh::lean_box(0);
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1908_);
                    v___x_1923_ = leanh::lean_box(0);
                    return v___x_1923_;
                }
            }
            1 => {
                v_kind_1913_ = leanh::lean_ctor_get_uint8(
                    v_val_1909_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_1913_ == 5 {
                    v___x_1914_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1909_);
                    if leanh::lean_obj_tag(v___x_1914_) == 5 {
                        v_val_1915_ = leanh::lean_ctor_get(v___x_1914_, 0);
                        leanh::lean_inc_ref(v_val_1915_);
                        leanh::lean_dec_ref_known(v___x_1914_, 1);
                        if v_isShared_1912_ == 0 {
                            leanh::lean_ctor_set(v___x_1911_, 0, v_val_1915_);
                            v___x_1917_ = v___x_1911_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1918_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
                            v___x_1917_ = v_reuseFailAlloc_1918_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1914_);
                        leanh::lean_del_object(v___x_1911_);
                        v___x_1919_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3_once),
                            _init_l_Lean_isInductiveCore_x3f___closed__3,
                        );
                        v___x_1920_ =
                            l_panic___at___00Lean_isInductiveCore_x3f_spec__0(v___x_1919_);
                        return v___x_1920_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1911_);
                    leanh::lean_dec(v_val_1909_);
                    v___x_1921_ = leanh::lean_box(0);
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
    mut v_declName_1924_: *mut leanh::LeanObject,
    mut v_toPure_1925_: *mut leanh::LeanObject,
    mut v_____do__lift_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_isInductiveCore_x3f(v_____do__lift_1926_, v_declName_1924_);
    v___x_1928_ =
        leanh::lean_apply_2(v_toPure_1925_, leanh::lean_box(0), v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lean_isInductive_x3f___redArg(
    mut v_inst_1929_: *mut leanh::LeanObject,
    mut v_inst_1930_: *mut leanh::LeanObject,
    mut v_declName_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1932_ = leanh::lean_ctor_get(v_inst_1929_, 0);
    leanh::lean_inc_ref(v_toApplicative_1932_);
    v_toBind_1933_ = leanh::lean_ctor_get(v_inst_1929_, 1);
    leanh::lean_inc(v_toBind_1933_);
    leanh::lean_dec_ref(v_inst_1929_);
    v_getEnv_1934_ = leanh::lean_ctor_get(v_inst_1930_, 0);
    leanh::lean_inc(v_getEnv_1934_);
    leanh::lean_dec_ref(v_inst_1930_);
    v_toPure_1935_ = leanh::lean_ctor_get(v_toApplicative_1932_, 1);
    leanh::lean_inc(v_toPure_1935_);
    leanh::lean_dec_ref(v_toApplicative_1932_);
    v___f_1936_ = leanh::lean_alloc_closure(
        l_Lean_isInductive_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1936_, 0, v_declName_1931_);
    leanh::lean_closure_set(v___f_1936_, 1, v_toPure_1935_);
    v___x_1937_ = leanh::lean_apply_4(
        v_toBind_1933_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1934_,
        v___f_1936_,
    );
    return v___x_1937_;
}
pub unsafe fn l_Lean_isInductive_x3f(
    mut v_m_1938_: *mut leanh::LeanObject,
    mut v_inst_1939_: *mut leanh::LeanObject,
    mut v_inst_1940_: *mut leanh::LeanObject,
    mut v_declName_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_isInductive_x3f___redArg(v_inst_1939_, v_inst_1940_, v_declName_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1945_ = leanh::lean_unsigned_to_nat(11);
    v___x_1946_ = leanh::lean_unsigned_to_nat(115);
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
    mut v_toPure_1950_: *mut leanh::LeanObject,
    mut v_constName_1951_: *mut leanh::LeanObject,
    mut v___x_1952_: *mut leanh::LeanObject,
    mut v_____do__lift_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v_kind_1963_: u8 = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1958_) == 1 {
                    v_val_1959_ = leanh::lean_ctor_get(v___x_1958_, 0);
                    v_isSharedCheck_1972_ = (!leanh::lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_1972_ == 0 {
                        v___x_1961_ = v___x_1958_;
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1959_);
                        leanh::lean_dec(v___x_1958_);
                        v___x_1961_ = leanh::lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1958_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = leanh::lean_box(0);
                v___x_1956_ = leanh::lean_apply_2(
                    v_toPure_1950_,
                    leanh::lean_box(0),
                    v___x_1955_,
                );
                return v___x_1956_;
            }
            2 => {
                v_kind_1963_ = leanh::lean_ctor_get_uint8(
                    v_val_1959_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_1963_ == 0 {
                    v___x_1964_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1959_);
                    if leanh::lean_obj_tag(v___x_1964_) == 1 {
                        v_val_1965_ = leanh::lean_ctor_get(v___x_1964_, 0);
                        leanh::lean_inc_ref(v_val_1965_);
                        leanh::lean_dec_ref_known(v___x_1964_, 1);
                        if v_isShared_1962_ == 0 {
                            leanh::lean_ctor_set(v___x_1961_, 0, v_val_1965_);
                            v___x_1967_ = v___x_1961_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1969_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_val_1965_);
                            v___x_1967_ = v_reuseFailAlloc_1969_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1964_);
                        leanh::lean_del_object(v___x_1961_);
                        leanh::lean_dec(v_toPure_1950_);
                        v___x_1970_ = leanh::lean_obj_once(
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
                    leanh::lean_del_object(v___x_1961_);
                    leanh::lean_dec(v_val_1959_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1968_ = leanh::lean_apply_2(
                    v_toPure_1950_,
                    leanh::lean_box(0),
                    v___x_1967_,
                );
                return v___x_1968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isDefn_x3f___redArg___lam__0___boxed(
    mut v_toPure_1973_: *mut leanh::LeanObject,
    mut v_constName_1974_: *mut leanh::LeanObject,
    mut v___x_1975_: *mut leanh::LeanObject,
    mut v_____do__lift_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_isDefn_x3f___redArg___lam__0(
        v_toPure_1973_,
        v_constName_1974_,
        v___x_1975_,
        v_____do__lift_1976_,
    );
    leanh::lean_dec(v___x_1975_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_isDefn_x3f___redArg(
    mut v_inst_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_constName_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1981_ = leanh::lean_ctor_get(v_inst_1978_, 0);
    v_toBind_1982_ = leanh::lean_ctor_get(v_inst_1978_, 1);
    leanh::lean_inc(v_toBind_1982_);
    v_getEnv_1983_ = leanh::lean_ctor_get(v_inst_1979_, 0);
    leanh::lean_inc(v_getEnv_1983_);
    leanh::lean_dec_ref(v_inst_1979_);
    v_toPure_1984_ = leanh::lean_ctor_get(v_toApplicative_1981_, 1);
    leanh::lean_inc(v_toPure_1984_);
    v___x_1985_ = leanh::lean_box(0);
    v___x_1986_ = l_instInhabitedOfMonad___redArg(v_inst_1978_, v___x_1985_);
    v___f_1987_ = leanh::lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1987_, 0, v_toPure_1984_);
    leanh::lean_closure_set(v___f_1987_, 1, v_constName_1980_);
    leanh::lean_closure_set(v___f_1987_, 2, v___x_1986_);
    v___x_1988_ = leanh::lean_apply_4(
        v_toBind_1982_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1983_,
        v___f_1987_,
    );
    return v___x_1988_;
}
pub unsafe fn l_Lean_isDefn_x3f(
    mut v_m_1989_: *mut leanh::LeanObject,
    mut v_inst_1990_: *mut leanh::LeanObject,
    mut v_inst_1991_: *mut leanh::LeanObject,
    mut v_constName_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1993_ = l_Lean_isDefn_x3f___redArg(v_inst_1990_, v_inst_1991_, v_constName_1992_);
    return v___x_1993_;
}
pub unsafe fn _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1996_ = leanh::lean_unsigned_to_nat(11);
    v___x_1997_ = leanh::lean_unsigned_to_nat(122);
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
    mut v_toPure_2001_: *mut leanh::LeanObject,
    mut v_constName_2002_: *mut leanh::LeanObject,
    mut v___x_2003_: *mut leanh::LeanObject,
    mut v_____do__lift_2004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v_kind_2014_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2009_) == 1 {
                    v_val_2010_ = leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2023_ = (!leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2010_);
                        leanh::lean_dec(v___x_2009_);
                        v___x_2012_ = leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2009_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2006_ = leanh::lean_box(0);
                v___x_2007_ = leanh::lean_apply_2(
                    v_toPure_2001_,
                    leanh::lean_box(0),
                    v___x_2006_,
                );
                return v___x_2007_;
            }
            2 => {
                v_kind_2014_ = leanh::lean_ctor_get_uint8(
                    v_val_2010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_2014_ == 6 {
                    v___x_2015_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2010_);
                    if leanh::lean_obj_tag(v___x_2015_) == 6 {
                        v_val_2016_ = leanh::lean_ctor_get(v___x_2015_, 0);
                        leanh::lean_inc_ref(v_val_2016_);
                        leanh::lean_dec_ref_known(v___x_2015_, 1);
                        if v_isShared_2013_ == 0 {
                            leanh::lean_ctor_set(v___x_2012_, 0, v_val_2016_);
                            v___x_2018_ = v___x_2012_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2020_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_val_2016_);
                            v___x_2018_ = v_reuseFailAlloc_2020_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2015_);
                        leanh::lean_del_object(v___x_2012_);
                        leanh::lean_dec(v_toPure_2001_);
                        v___x_2021_ = leanh::lean_obj_once(
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
                    leanh::lean_del_object(v___x_2012_);
                    leanh::lean_dec(v_val_2010_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2019_ = leanh::lean_apply_2(
                    v_toPure_2001_,
                    leanh::lean_box(0),
                    v___x_2018_,
                );
                return v___x_2019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isCtor_x3f___redArg___lam__0___boxed(
    mut v_toPure_2024_: *mut leanh::LeanObject,
    mut v_constName_2025_: *mut leanh::LeanObject,
    mut v___x_2026_: *mut leanh::LeanObject,
    mut v_____do__lift_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lean_isCtor_x3f___redArg___lam__0(
        v_toPure_2024_,
        v_constName_2025_,
        v___x_2026_,
        v_____do__lift_2027_,
    );
    leanh::lean_dec(v___x_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Lean_isCtor_x3f___redArg(
    mut v_inst_2029_: *mut leanh::LeanObject,
    mut v_inst_2030_: *mut leanh::LeanObject,
    mut v_constName_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2032_ = leanh::lean_ctor_get(v_inst_2029_, 0);
    v_toBind_2033_ = leanh::lean_ctor_get(v_inst_2029_, 1);
    leanh::lean_inc(v_toBind_2033_);
    v_getEnv_2034_ = leanh::lean_ctor_get(v_inst_2030_, 0);
    leanh::lean_inc(v_getEnv_2034_);
    leanh::lean_dec_ref(v_inst_2030_);
    v_toPure_2035_ = leanh::lean_ctor_get(v_toApplicative_2032_, 1);
    leanh::lean_inc(v_toPure_2035_);
    v___x_2036_ = leanh::lean_box(0);
    v___x_2037_ = l_instInhabitedOfMonad___redArg(v_inst_2029_, v___x_2036_);
    v___f_2038_ = leanh::lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2038_, 0, v_toPure_2035_);
    leanh::lean_closure_set(v___f_2038_, 1, v_constName_2031_);
    leanh::lean_closure_set(v___f_2038_, 2, v___x_2037_);
    v___x_2039_ = leanh::lean_apply_4(
        v_toBind_2033_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2034_,
        v___f_2038_,
    );
    return v___x_2039_;
}
pub unsafe fn l_Lean_isCtor_x3f(
    mut v_m_2040_: *mut leanh::LeanObject,
    mut v_inst_2041_: *mut leanh::LeanObject,
    mut v_inst_2042_: *mut leanh::LeanObject,
    mut v_constName_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Lean_isCtor_x3f___redArg(v_inst_2041_, v_inst_2042_, v_constName_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_2047_ = leanh::lean_unsigned_to_nat(11);
    v___x_2048_ = leanh::lean_unsigned_to_nat(129);
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
    mut v_toPure_2052_: *mut leanh::LeanObject,
    mut v_constName_2053_: *mut leanh::LeanObject,
    mut v___x_2054_: *mut leanh::LeanObject,
    mut v_____do__lift_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_kind_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2060_) == 1 {
                    v_val_2061_ = leanh::lean_ctor_get(v___x_2060_, 0);
                    v_isSharedCheck_2074_ = (!leanh::lean_is_exclusive(v___x_2060_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2063_ = v___x_2060_;
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2061_);
                        leanh::lean_dec(v___x_2060_);
                        v___x_2063_ = leanh::lean_box(0);
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2060_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2057_ = leanh::lean_box(0);
                v___x_2058_ = leanh::lean_apply_2(
                    v_toPure_2052_,
                    leanh::lean_box(0),
                    v___x_2057_,
                );
                return v___x_2058_;
            }
            2 => {
                v_kind_2065_ = leanh::lean_ctor_get_uint8(
                    v_val_2061_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_2065_ == 7 {
                    v___x_2066_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2061_);
                    if leanh::lean_obj_tag(v___x_2066_) == 7 {
                        v_val_2067_ = leanh::lean_ctor_get(v___x_2066_, 0);
                        leanh::lean_inc_ref(v_val_2067_);
                        leanh::lean_dec_ref_known(v___x_2066_, 1);
                        if v_isShared_2064_ == 0 {
                            leanh::lean_ctor_set(v___x_2063_, 0, v_val_2067_);
                            v___x_2069_ = v___x_2063_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2071_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2067_);
                            v___x_2069_ = v_reuseFailAlloc_2071_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2066_);
                        leanh::lean_del_object(v___x_2063_);
                        leanh::lean_dec(v_toPure_2052_);
                        v___x_2072_ = leanh::lean_obj_once(
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
                    leanh::lean_del_object(v___x_2063_);
                    leanh::lean_dec(v_val_2061_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2070_ = leanh::lean_apply_2(
                    v_toPure_2052_,
                    leanh::lean_box(0),
                    v___x_2069_,
                );
                return v___x_2070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isRec_x3f___redArg___lam__0___boxed(
    mut v_toPure_2075_: *mut leanh::LeanObject,
    mut v_constName_2076_: *mut leanh::LeanObject,
    mut v___x_2077_: *mut leanh::LeanObject,
    mut v_____do__lift_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_isRec_x3f___redArg___lam__0(
        v_toPure_2075_,
        v_constName_2076_,
        v___x_2077_,
        v_____do__lift_2078_,
    );
    leanh::lean_dec(v___x_2077_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_isRec_x3f___redArg(
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
    mut v_constName_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2083_ = leanh::lean_ctor_get(v_inst_2080_, 0);
    v_toBind_2084_ = leanh::lean_ctor_get(v_inst_2080_, 1);
    leanh::lean_inc(v_toBind_2084_);
    v_getEnv_2085_ = leanh::lean_ctor_get(v_inst_2081_, 0);
    leanh::lean_inc(v_getEnv_2085_);
    leanh::lean_dec_ref(v_inst_2081_);
    v_toPure_2086_ = leanh::lean_ctor_get(v_toApplicative_2083_, 1);
    leanh::lean_inc(v_toPure_2086_);
    v___x_2087_ = leanh::lean_box(0);
    v___x_2088_ = l_instInhabitedOfMonad___redArg(v_inst_2080_, v___x_2087_);
    v___f_2089_ = leanh::lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2089_, 0, v_toPure_2086_);
    leanh::lean_closure_set(v___f_2089_, 1, v_constName_2082_);
    leanh::lean_closure_set(v___f_2089_, 2, v___x_2088_);
    v___x_2090_ = leanh::lean_apply_4(
        v_toBind_2084_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2085_,
        v___f_2089_,
    );
    return v___x_2090_;
}
pub unsafe fn l_Lean_isRec_x3f(
    mut v_m_2091_: *mut leanh::LeanObject,
    mut v_inst_2092_: *mut leanh::LeanObject,
    mut v_inst_2093_: *mut leanh::LeanObject,
    mut v_constName_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_isRec_x3f___redArg(v_inst_2092_, v_inst_2093_, v_constName_2094_);
    return v___x_2095_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg___lam__0(
    mut v_constName_2097_: *mut leanh::LeanObject,
    mut v_toPure_2098_: *mut leanh::LeanObject,
    mut v_info_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_levelParams_2100_ = leanh::lean_ctor_get(v_info_2099_, 1);
    leanh::lean_inc(v_levelParams_2100_);
    leanh::lean_dec_ref(v_info_2099_);
    v___x_2101_ = l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0;
    v___x_2102_ = leanh::lean_box(0);
    v___x_2103_ = l_List_mapTR_loop___redArg(v___x_2101_, v_levelParams_2100_, v___x_2102_);
    v___x_2104_ = l_Lean_mkConst(v_constName_2097_, v___x_2103_);
    v___x_2105_ =
        leanh::lean_apply_2(v_toPure_2098_, leanh::lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg(
    mut v_inst_2106_: *mut leanh::LeanObject,
    mut v_inst_2107_: *mut leanh::LeanObject,
    mut v_inst_2108_: *mut leanh::LeanObject,
    mut v_constName_2109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2110_ = leanh::lean_ctor_get(v_inst_2106_, 0);
    v_toBind_2111_ = leanh::lean_ctor_get(v_inst_2106_, 1);
    leanh::lean_inc(v_toBind_2111_);
    v_toPure_2112_ = leanh::lean_ctor_get(v_toApplicative_2110_, 1);
    leanh::lean_inc(v_toPure_2112_);
    leanh::lean_inc(v_constName_2109_);
    v___x_2113_ =
        l_Lean_getConstVal___redArg(v_inst_2106_, v_inst_2107_, v_inst_2108_, v_constName_2109_);
    v___f_2114_ = leanh::lean_alloc_closure(
        l_Lean_mkConstWithLevelParams___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2114_, 0, v_constName_2109_);
    leanh::lean_closure_set(v___f_2114_, 1, v_toPure_2112_);
    v___x_2115_ = leanh::lean_apply_4(
        v_toBind_2111_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2113_,
        v___f_2114_,
    );
    return v___x_2115_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams(
    mut v_m_2116_: *mut leanh::LeanObject,
    mut v_inst_2117_: *mut leanh::LeanObject,
    mut v_inst_2118_: *mut leanh::LeanObject,
    mut v_inst_2119_: *mut leanh::LeanObject,
    mut v_constName_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_mkConstWithLevelParams___redArg(
        v_inst_2117_,
        v_inst_2118_,
        v_inst_2119_,
        v_constName_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__0;
    v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__2;
    v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg___lam__0(
    mut v_constName_2128_: *mut leanh::LeanObject,
    mut v_inst_2129_: *mut leanh::LeanObject,
    mut v_inst_2130_: *mut leanh::LeanObject,
    mut v_toPure_2131_: *mut leanh::LeanObject,
    mut v_____do__lift_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2132_) == 0 {
        let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: u8 = 0;
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2131_);
        v___x_2133_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2134_ = 0;
        v___x_2135_ = l_Lean_MessageData_ofConstName(v_constName_2128_, v___x_2134_);
        v___x_2136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2136_, 0, v___x_2133_);
        leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
        v___x_2137_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3,
        );
        v___x_2138_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
        leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
        v___x_2139_ = l_Lean_throwError___redArg(v_inst_2129_, v_inst_2130_, v___x_2138_);
        return v___x_2139_;
    } else {
        let mut v_val_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2130_);
        leanh::lean_dec_ref(v_inst_2129_);
        leanh::lean_dec(v_constName_2128_);
        v_val_2140_ = leanh::lean_ctor_get(v_____do__lift_2132_, 0);
        leanh::lean_inc(v_val_2140_);
        leanh::lean_dec_ref_known(v_____do__lift_2132_, 1);
        v___x_2141_ =
            leanh::lean_apply_2(v_toPure_2131_, leanh::lean_box(0), v_val_2140_);
        return v___x_2141_;
    }
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg(
    mut v_inst_2142_: *mut leanh::LeanObject,
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_inst_2144_: *mut leanh::LeanObject,
    mut v_constName_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2146_ = leanh::lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2147_ = leanh::lean_ctor_get(v_inst_2142_, 1);
    leanh::lean_inc_n(v_toBind_2147_, 2);
    v_getEnv_2148_ = leanh::lean_ctor_get(v_inst_2143_, 0);
    leanh::lean_inc(v_getEnv_2148_);
    leanh::lean_dec_ref(v_inst_2143_);
    v_toPure_2149_ = leanh::lean_ctor_get(v_toApplicative_2146_, 1);
    leanh::lean_inc_n(v_toPure_2149_, 2);
    v___x_2150_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_inst_2142_);
    leanh::lean_inc(v_constName_2145_);
    v___f_2151_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfoDefn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2151_, 0, v_constName_2145_);
    leanh::lean_closure_set(v___f_2151_, 1, v_inst_2142_);
    leanh::lean_closure_set(v___f_2151_, 2, v_inst_2144_);
    leanh::lean_closure_set(v___f_2151_, 3, v_toPure_2149_);
    v___x_2152_ = l_instInhabitedOfMonad___redArg(v_inst_2142_, v___x_2150_);
    v___f_2153_ = leanh::lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2153_, 0, v_toPure_2149_);
    leanh::lean_closure_set(v___f_2153_, 1, v_constName_2145_);
    leanh::lean_closure_set(v___f_2153_, 2, v___x_2152_);
    v___x_2154_ = leanh::lean_apply_4(
        v_toBind_2147_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2148_,
        v___f_2153_,
    );
    v___x_2155_ = leanh::lean_apply_4(
        v_toBind_2147_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2154_,
        v___f_2151_,
    );
    return v___x_2155_;
}
pub unsafe fn l_Lean_getConstInfoDefn(
    mut v_m_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
    mut v_inst_2158_: *mut leanh::LeanObject,
    mut v_inst_2159_: *mut leanh::LeanObject,
    mut v_constName_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_getConstInfoDefn___redArg(
        v_inst_2157_,
        v_inst_2158_,
        v_inst_2159_,
        v_constName_2160_,
    );
    return v___x_2161_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = l_Lean_getConstInfoInduct___redArg___lam__0___closed__0;
    v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__0(
    mut v_constName_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_inst_2167_: *mut leanh::LeanObject,
    mut v_toPure_2168_: *mut leanh::LeanObject,
    mut v_____do__lift_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2169_) == 0 {
        let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: u8 = 0;
        let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2168_);
        v___x_2170_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2171_ = 0;
        v___x_2172_ = l_Lean_MessageData_ofConstName(v_constName_2165_, v___x_2171_);
        v___x_2173_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2173_, 0, v___x_2170_);
        leanh::lean_ctor_set(v___x_2173_, 1, v___x_2172_);
        v___x_2174_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1,
        );
        v___x_2175_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2175_, 0, v___x_2173_);
        leanh::lean_ctor_set(v___x_2175_, 1, v___x_2174_);
        v___x_2176_ = l_Lean_throwError___redArg(v_inst_2166_, v_inst_2167_, v___x_2175_);
        return v___x_2176_;
    } else {
        let mut v_val_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2167_);
        leanh::lean_dec_ref(v_inst_2166_);
        leanh::lean_dec(v_constName_2165_);
        v_val_2177_ = leanh::lean_ctor_get(v_____do__lift_2169_, 0);
        leanh::lean_inc(v_val_2177_);
        leanh::lean_dec_ref_known(v_____do__lift_2169_, 1);
        v___x_2178_ =
            leanh::lean_apply_2(v_toPure_2168_, leanh::lean_box(0), v_val_2177_);
        return v___x_2178_;
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__1(
    mut v_constName_2179_: *mut leanh::LeanObject,
    mut v_toPure_2180_: *mut leanh::LeanObject,
    mut v_____do__lift_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_isInductiveCore_x3f(v_____do__lift_2181_, v_constName_2179_);
    v___x_2183_ =
        leanh::lean_apply_2(v_toPure_2180_, leanh::lean_box(0), v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg(
    mut v_inst_2184_: *mut leanh::LeanObject,
    mut v_inst_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_constName_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2188_ = leanh::lean_ctor_get(v_inst_2184_, 0);
    v_toBind_2189_ = leanh::lean_ctor_get(v_inst_2184_, 1);
    leanh::lean_inc_n(v_toBind_2189_, 2);
    v_getEnv_2190_ = leanh::lean_ctor_get(v_inst_2185_, 0);
    leanh::lean_inc(v_getEnv_2190_);
    leanh::lean_dec_ref(v_inst_2185_);
    v_toPure_2191_ = leanh::lean_ctor_get(v_toApplicative_2188_, 1);
    leanh::lean_inc_n(v_toPure_2191_, 2);
    leanh::lean_inc(v_constName_2187_);
    v___f_2192_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2192_, 0, v_constName_2187_);
    leanh::lean_closure_set(v___f_2192_, 1, v_inst_2184_);
    leanh::lean_closure_set(v___f_2192_, 2, v_inst_2186_);
    leanh::lean_closure_set(v___f_2192_, 3, v_toPure_2191_);
    v___f_2193_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2193_, 0, v_constName_2187_);
    leanh::lean_closure_set(v___f_2193_, 1, v_toPure_2191_);
    v___x_2194_ = leanh::lean_apply_4(
        v_toBind_2189_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2190_,
        v___f_2193_,
    );
    v___x_2195_ = leanh::lean_apply_4(
        v_toBind_2189_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2194_,
        v___f_2192_,
    );
    return v___x_2195_;
}
pub unsafe fn l_Lean_getConstInfoInduct(
    mut v_m_2196_: *mut leanh::LeanObject,
    mut v_inst_2197_: *mut leanh::LeanObject,
    mut v_inst_2198_: *mut leanh::LeanObject,
    mut v_inst_2199_: *mut leanh::LeanObject,
    mut v_constName_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Lean_getConstInfoInduct___redArg(
        v_inst_2197_,
        v_inst_2198_,
        v_inst_2199_,
        v_constName_2200_,
    );
    return v___x_2201_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Lean_getConstInfoCtor___redArg___lam__0___closed__0;
    v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg___lam__0(
    mut v_constName_2205_: *mut leanh::LeanObject,
    mut v_inst_2206_: *mut leanh::LeanObject,
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_toPure_2208_: *mut leanh::LeanObject,
    mut v_____do__lift_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2209_) == 0 {
        let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: u8 = 0;
        let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2208_);
        v___x_2210_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2211_ = 0;
        v___x_2212_ = l_Lean_MessageData_ofConstName(v_constName_2205_, v___x_2211_);
        v___x_2213_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2213_, 0, v___x_2210_);
        leanh::lean_ctor_set(v___x_2213_, 1, v___x_2212_);
        v___x_2214_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1,
        );
        v___x_2215_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2215_, 0, v___x_2213_);
        leanh::lean_ctor_set(v___x_2215_, 1, v___x_2214_);
        v___x_2216_ = l_Lean_throwError___redArg(v_inst_2206_, v_inst_2207_, v___x_2215_);
        return v___x_2216_;
    } else {
        let mut v_val_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2207_);
        leanh::lean_dec_ref(v_inst_2206_);
        leanh::lean_dec(v_constName_2205_);
        v_val_2217_ = leanh::lean_ctor_get(v_____do__lift_2209_, 0);
        leanh::lean_inc(v_val_2217_);
        leanh::lean_dec_ref_known(v_____do__lift_2209_, 1);
        v___x_2218_ =
            leanh::lean_apply_2(v_toPure_2208_, leanh::lean_box(0), v_val_2217_);
        return v___x_2218_;
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg(
    mut v_inst_2219_: *mut leanh::LeanObject,
    mut v_inst_2220_: *mut leanh::LeanObject,
    mut v_inst_2221_: *mut leanh::LeanObject,
    mut v_constName_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2223_ = leanh::lean_ctor_get(v_inst_2219_, 0);
    v_toBind_2224_ = leanh::lean_ctor_get(v_inst_2219_, 1);
    leanh::lean_inc_n(v_toBind_2224_, 2);
    v_getEnv_2225_ = leanh::lean_ctor_get(v_inst_2220_, 0);
    leanh::lean_inc(v_getEnv_2225_);
    leanh::lean_dec_ref(v_inst_2220_);
    v_toPure_2226_ = leanh::lean_ctor_get(v_toApplicative_2223_, 1);
    leanh::lean_inc_n(v_toPure_2226_, 2);
    v___x_2227_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_inst_2219_);
    leanh::lean_inc(v_constName_2222_);
    v___f_2228_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfoCtor___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2228_, 0, v_constName_2222_);
    leanh::lean_closure_set(v___f_2228_, 1, v_inst_2219_);
    leanh::lean_closure_set(v___f_2228_, 2, v_inst_2221_);
    leanh::lean_closure_set(v___f_2228_, 3, v_toPure_2226_);
    v___x_2229_ = l_instInhabitedOfMonad___redArg(v_inst_2219_, v___x_2227_);
    v___f_2230_ = leanh::lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2230_, 0, v_toPure_2226_);
    leanh::lean_closure_set(v___f_2230_, 1, v_constName_2222_);
    leanh::lean_closure_set(v___f_2230_, 2, v___x_2229_);
    v___x_2231_ = leanh::lean_apply_4(
        v_toBind_2224_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2225_,
        v___f_2230_,
    );
    v___x_2232_ = leanh::lean_apply_4(
        v_toBind_2224_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2231_,
        v___f_2228_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_getConstInfoCtor(
    mut v_m_2233_: *mut leanh::LeanObject,
    mut v_inst_2234_: *mut leanh::LeanObject,
    mut v_inst_2235_: *mut leanh::LeanObject,
    mut v_inst_2236_: *mut leanh::LeanObject,
    mut v_constName_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = l_Lean_getConstInfoCtor___redArg(
        v_inst_2234_,
        v_inst_2235_,
        v_inst_2236_,
        v_constName_2237_,
    );
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_getConstInfoRec___redArg___lam__0___closed__0;
    v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
    return v___x_2241_;
}
pub unsafe fn l_Lean_getConstInfoRec___redArg___lam__0(
    mut v_constName_2242_: *mut leanh::LeanObject,
    mut v_inst_2243_: *mut leanh::LeanObject,
    mut v_inst_2244_: *mut leanh::LeanObject,
    mut v_toPure_2245_: *mut leanh::LeanObject,
    mut v_____do__lift_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2246_) == 0 {
        let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: u8 = 0;
        let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2245_);
        v___x_2247_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2248_ = 0;
        v___x_2249_ = l_Lean_MessageData_ofConstName(v_constName_2242_, v___x_2248_);
        v___x_2250_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2250_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
        v___x_2251_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1,
        );
        v___x_2252_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2252_, 0, v___x_2250_);
        leanh::lean_ctor_set(v___x_2252_, 1, v___x_2251_);
        v___x_2253_ = l_Lean_throwError___redArg(v_inst_2243_, v_inst_2244_, v___x_2252_);
        return v___x_2253_;
    } else {
        let mut v_val_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2244_);
        leanh::lean_dec_ref(v_inst_2243_);
        leanh::lean_dec(v_constName_2242_);
        v_val_2254_ = leanh::lean_ctor_get(v_____do__lift_2246_, 0);
        leanh::lean_inc(v_val_2254_);
        leanh::lean_dec_ref_known(v_____do__lift_2246_, 1);
        v___x_2255_ =
            leanh::lean_apply_2(v_toPure_2245_, leanh::lean_box(0), v_val_2254_);
        return v___x_2255_;
    }
}
pub unsafe fn l_Lean_getConstInfoRec___redArg(
    mut v_inst_2256_: *mut leanh::LeanObject,
    mut v_inst_2257_: *mut leanh::LeanObject,
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_constName_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2260_ = leanh::lean_ctor_get(v_inst_2256_, 0);
    v_toBind_2261_ = leanh::lean_ctor_get(v_inst_2256_, 1);
    leanh::lean_inc_n(v_toBind_2261_, 2);
    v_getEnv_2262_ = leanh::lean_ctor_get(v_inst_2257_, 0);
    leanh::lean_inc(v_getEnv_2262_);
    leanh::lean_dec_ref(v_inst_2257_);
    v_toPure_2263_ = leanh::lean_ctor_get(v_toApplicative_2260_, 1);
    leanh::lean_inc_n(v_toPure_2263_, 2);
    v___x_2264_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_inst_2256_);
    leanh::lean_inc(v_constName_2259_);
    v___f_2265_ = leanh::lean_alloc_closure(
        l_Lean_getConstInfoRec___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2265_, 0, v_constName_2259_);
    leanh::lean_closure_set(v___f_2265_, 1, v_inst_2256_);
    leanh::lean_closure_set(v___f_2265_, 2, v_inst_2258_);
    leanh::lean_closure_set(v___f_2265_, 3, v_toPure_2263_);
    v___x_2266_ = l_instInhabitedOfMonad___redArg(v_inst_2256_, v___x_2264_);
    v___f_2267_ = leanh::lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2267_, 0, v_toPure_2263_);
    leanh::lean_closure_set(v___f_2267_, 1, v_constName_2259_);
    leanh::lean_closure_set(v___f_2267_, 2, v___x_2266_);
    v___x_2268_ = leanh::lean_apply_4(
        v_toBind_2261_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2262_,
        v___f_2267_,
    );
    v___x_2269_ = leanh::lean_apply_4(
        v_toBind_2261_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2268_,
        v___f_2265_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_getConstInfoRec(
    mut v_m_2270_: *mut leanh::LeanObject,
    mut v_inst_2271_: *mut leanh::LeanObject,
    mut v_inst_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_constName_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_getConstInfoRec___redArg(
        v_inst_2271_,
        v_inst_2272_,
        v_inst_2273_,
        v_constName_2274_,
    );
    return v___x_2275_;
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__0(
    mut v_k_2276_: *mut leanh::LeanObject,
    mut v_val_2277_: *mut leanh::LeanObject,
    mut v_us_2278_: *mut leanh::LeanObject,
    mut v_failK_2279_: *mut leanh::LeanObject,
    mut v_____do__lift_2280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2280_) == 6 {
        let mut v_val_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_failK_2279_);
        v_val_2281_ = leanh::lean_ctor_get(v_____do__lift_2280_, 0);
        leanh::lean_inc_ref(v_val_2281_);
        leanh::lean_dec_ref_known(v_____do__lift_2280_, 1);
        v___x_2282_ = leanh::lean_apply_3(v_k_2276_, v_val_2277_, v_us_2278_, v_val_2281_);
        return v___x_2282_;
    } else {
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_____do__lift_2280_);
        leanh::lean_dec(v_us_2278_);
        leanh::lean_dec_ref(v_val_2277_);
        leanh::lean_dec(v_k_2276_);
        v___x_2283_ = leanh::lean_box(0);
        v___x_2284_ = leanh::lean_apply_1(v_failK_2279_, v___x_2283_);
        return v___x_2284_;
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__1(
    mut v_declName_2285_: *mut leanh::LeanObject,
    mut v_failK_2286_: *mut leanh::LeanObject,
    mut v_k_2287_: *mut leanh::LeanObject,
    mut v_us_2288_: *mut leanh::LeanObject,
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_inst_2290_: *mut leanh::LeanObject,
    mut v_inst_2291_: *mut leanh::LeanObject,
    mut v_toBind_2292_: *mut leanh::LeanObject,
    mut v_____do__lift_2293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2298_) == 0 {
                    leanh::lean_dec(v_toBind_2292_);
                    leanh::lean_dec_ref(v_inst_2291_);
                    leanh::lean_dec_ref(v_inst_2290_);
                    leanh::lean_dec_ref(v_inst_2289_);
                    leanh::lean_dec(v_us_2288_);
                    leanh::lean_dec(v_k_2287_);
                    v___x_2299_ = leanh::lean_box(0);
                    v___x_2300_ = leanh::lean_apply_1(v_failK_2286_, v___x_2299_);
                    return v___x_2300_;
                } else {
                    v_val_2301_ = leanh::lean_ctor_get(v___x_2298_, 0);
                    leanh::lean_inc(v_val_2301_);
                    leanh::lean_dec_ref_known(v___x_2298_, 1);
                    if leanh::lean_obj_tag(v_val_2301_) == 5 {
                        v_val_2302_ = leanh::lean_ctor_get(v_val_2301_, 0);
                        leanh::lean_inc_ref(v_val_2302_);
                        leanh::lean_dec_ref_known(v_val_2301_, 1);
                        v_ctors_2303_ = leanh::lean_ctor_get(v_val_2302_, 4);
                        if leanh::lean_obj_tag(v_ctors_2303_) == 1 {
                            v_tail_2304_ = leanh::lean_ctor_get(v_ctors_2303_, 1);
                            if leanh::lean_obj_tag(v_tail_2304_) == 0 {
                                v_head_2305_ = leanh::lean_ctor_get(v_ctors_2303_, 0);
                                leanh::lean_inc(v_head_2305_);
                                v___f_2306_ = leanh::lean_alloc_closure(
                                    l_Lean_matchConstStructure___redArg___lam__0
                                        as *mut core::ffi::c_void,
                                    5,
                                    4,
                                );
                                leanh::lean_closure_set(v___f_2306_, 0, v_k_2287_);
                                leanh::lean_closure_set(v___f_2306_, 1, v_val_2302_);
                                leanh::lean_closure_set(v___f_2306_, 2, v_us_2288_);
                                leanh::lean_closure_set(v___f_2306_, 3, v_failK_2286_);
                                v___x_2307_ = l_Lean_getConstInfo___redArg(
                                    v_inst_2289_,
                                    v_inst_2290_,
                                    v_inst_2291_,
                                    v_head_2305_,
                                );
                                v___x_2308_ = leanh::lean_apply_4(
                                    v_toBind_2292_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2307_,
                                    v___f_2306_,
                                );
                                return v___x_2308_;
                            } else {
                                leanh::lean_dec_ref(v_val_2302_);
                                leanh::lean_dec(v_toBind_2292_);
                                leanh::lean_dec_ref(v_inst_2291_);
                                leanh::lean_dec_ref(v_inst_2290_);
                                leanh::lean_dec_ref(v_inst_2289_);
                                leanh::lean_dec(v_us_2288_);
                                leanh::lean_dec(v_k_2287_);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_val_2302_);
                            leanh::lean_dec(v_toBind_2292_);
                            leanh::lean_dec_ref(v_inst_2291_);
                            leanh::lean_dec_ref(v_inst_2290_);
                            leanh::lean_dec_ref(v_inst_2289_);
                            leanh::lean_dec(v_us_2288_);
                            leanh::lean_dec(v_k_2287_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_2301_);
                        leanh::lean_dec(v_toBind_2292_);
                        leanh::lean_dec_ref(v_inst_2291_);
                        leanh::lean_dec_ref(v_inst_2290_);
                        leanh::lean_dec_ref(v_inst_2289_);
                        leanh::lean_dec(v_us_2288_);
                        leanh::lean_dec(v_k_2287_);
                        v___x_2309_ = leanh::lean_box(0);
                        v___x_2310_ = leanh::lean_apply_1(v_failK_2286_, v___x_2309_);
                        return v___x_2310_;
                    }
                }
            }
            1 => {
                v___x_2295_ = leanh::lean_box(0);
                v___x_2296_ = leanh::lean_apply_1(v_failK_2286_, v___x_2295_);
                return v___x_2296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg(
    mut v_inst_2311_: *mut leanh::LeanObject,
    mut v_inst_2312_: *mut leanh::LeanObject,
    mut v_inst_2313_: *mut leanh::LeanObject,
    mut v_e_2314_: *mut leanh::LeanObject,
    mut v_failK_2315_: *mut leanh::LeanObject,
    mut v_k_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_2314_) == 4 {
        let mut v_toBind_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2317_ = leanh::lean_ctor_get(v_inst_2311_, 1);
        leanh::lean_inc_n(v_toBind_2317_, 2);
        v_declName_2318_ = leanh::lean_ctor_get(v_e_2314_, 0);
        leanh::lean_inc(v_declName_2318_);
        v_us_2319_ = leanh::lean_ctor_get(v_e_2314_, 1);
        leanh::lean_inc(v_us_2319_);
        leanh::lean_dec_ref_known(v_e_2314_, 2);
        v_getEnv_2320_ = leanh::lean_ctor_get(v_inst_2312_, 0);
        leanh::lean_inc(v_getEnv_2320_);
        v___f_2321_ = leanh::lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_2321_, 0, v_declName_2318_);
        leanh::lean_closure_set(v___f_2321_, 1, v_failK_2315_);
        leanh::lean_closure_set(v___f_2321_, 2, v_k_2316_);
        leanh::lean_closure_set(v___f_2321_, 3, v_us_2319_);
        leanh::lean_closure_set(v___f_2321_, 4, v_inst_2311_);
        leanh::lean_closure_set(v___f_2321_, 5, v_inst_2312_);
        leanh::lean_closure_set(v___f_2321_, 6, v_inst_2313_);
        leanh::lean_closure_set(v___f_2321_, 7, v_toBind_2317_);
        v___x_2322_ = leanh::lean_apply_4(
            v_toBind_2317_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2320_,
            v___f_2321_,
        );
        return v___x_2322_;
    } else {
        let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_2316_);
        leanh::lean_dec_ref(v_e_2314_);
        leanh::lean_dec_ref(v_inst_2313_);
        leanh::lean_dec_ref(v_inst_2312_);
        leanh::lean_dec_ref(v_inst_2311_);
        v___x_2323_ = leanh::lean_box(0);
        v___x_2324_ = leanh::lean_apply_1(v_failK_2315_, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_matchConstStructure(
    mut v_m_2325_: *mut leanh::LeanObject,
    mut v_00_u03b1_2326_: *mut leanh::LeanObject,
    mut v_inst_2327_: *mut leanh::LeanObject,
    mut v_inst_2328_: *mut leanh::LeanObject,
    mut v_inst_2329_: *mut leanh::LeanObject,
    mut v_e_2330_: *mut leanh::LeanObject,
    mut v_failK_2331_: *mut leanh::LeanObject,
    mut v_k_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_2330_) == 4 {
        let mut v_toBind_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2333_ = leanh::lean_ctor_get(v_inst_2327_, 1);
        leanh::lean_inc_n(v_toBind_2333_, 2);
        v_declName_2334_ = leanh::lean_ctor_get(v_e_2330_, 0);
        leanh::lean_inc(v_declName_2334_);
        v_us_2335_ = leanh::lean_ctor_get(v_e_2330_, 1);
        leanh::lean_inc(v_us_2335_);
        leanh::lean_dec_ref_known(v_e_2330_, 2);
        v_getEnv_2336_ = leanh::lean_ctor_get(v_inst_2328_, 0);
        leanh::lean_inc(v_getEnv_2336_);
        v___f_2337_ = leanh::lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_2337_, 0, v_declName_2334_);
        leanh::lean_closure_set(v___f_2337_, 1, v_failK_2331_);
        leanh::lean_closure_set(v___f_2337_, 2, v_k_2332_);
        leanh::lean_closure_set(v___f_2337_, 3, v_us_2335_);
        leanh::lean_closure_set(v___f_2337_, 4, v_inst_2327_);
        leanh::lean_closure_set(v___f_2337_, 5, v_inst_2328_);
        leanh::lean_closure_set(v___f_2337_, 6, v_inst_2329_);
        leanh::lean_closure_set(v___f_2337_, 7, v_toBind_2333_);
        v___x_2338_ = leanh::lean_apply_4(
            v_toBind_2333_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2336_,
            v___f_2337_,
        );
        return v___x_2338_;
    } else {
        let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_2332_);
        leanh::lean_dec_ref(v_e_2330_);
        leanh::lean_dec_ref(v_inst_2329_);
        leanh::lean_dec_ref(v_inst_2328_);
        leanh::lean_dec_ref(v_inst_2327_);
        v___x_2339_ = leanh::lean_box(0);
        v___x_2340_ = leanh::lean_apply_1(v_failK_2331_, v___x_2339_);
        return v___x_2340_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg___lam__1(
    mut v_declName_2341_: *mut leanh::LeanObject,
    mut v_failK_2342_: *mut leanh::LeanObject,
    mut v_k_2343_: *mut leanh::LeanObject,
    mut v_us_2344_: *mut leanh::LeanObject,
    mut v_inst_2345_: *mut leanh::LeanObject,
    mut v_inst_2346_: *mut leanh::LeanObject,
    mut v_inst_2347_: *mut leanh::LeanObject,
    mut v_toBind_2348_: *mut leanh::LeanObject,
    mut v_____do__lift_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_2362_: u8 = 0;
    let mut v_numIndices_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v_tail_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2357_) == 0 {
                    leanh::lean_dec(v_toBind_2348_);
                    leanh::lean_dec_ref(v_inst_2347_);
                    leanh::lean_dec_ref(v_inst_2346_);
                    leanh::lean_dec_ref(v_inst_2345_);
                    leanh::lean_dec(v_us_2344_);
                    leanh::lean_dec(v_k_2343_);
                    v___x_2358_ = leanh::lean_box(0);
                    v___x_2359_ = leanh::lean_apply_1(v_failK_2342_, v___x_2358_);
                    return v___x_2359_;
                } else {
                    v_val_2360_ = leanh::lean_ctor_get(v___x_2357_, 0);
                    leanh::lean_inc(v_val_2360_);
                    leanh::lean_dec_ref_known(v___x_2357_, 1);
                    if leanh::lean_obj_tag(v_val_2360_) == 5 {
                        v_val_2361_ = leanh::lean_ctor_get(v_val_2360_, 0);
                        leanh::lean_inc_ref(v_val_2361_);
                        leanh::lean_dec_ref_known(v_val_2360_, 1);
                        v_isRec_2362_ = leanh::lean_ctor_get_uint8(
                            v_val_2361_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        );
                        if v_isRec_2362_ == 0 {
                            v_numIndices_2363_ = leanh::lean_ctor_get(v_val_2361_, 2);
                            v_ctors_2364_ = leanh::lean_ctor_get(v_val_2361_, 4);
                            v___x_2365_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2366_ = lean_nat_dec_eq(v_numIndices_2363_, v___x_2365_);
                            if v___x_2366_ == 0 {
                                leanh::lean_dec_ref(v_val_2361_);
                                leanh::lean_dec(v_toBind_2348_);
                                leanh::lean_dec_ref(v_inst_2347_);
                                leanh::lean_dec_ref(v_inst_2346_);
                                leanh::lean_dec_ref(v_inst_2345_);
                                leanh::lean_dec(v_us_2344_);
                                leanh::lean_dec(v_k_2343_);
                                state = 1;
                                continue;
                            } else {
                                if leanh::lean_obj_tag(v_ctors_2364_) == 1 {
                                    v_tail_2367_ = leanh::lean_ctor_get(v_ctors_2364_, 1);
                                    if leanh::lean_obj_tag(v_tail_2367_) == 0 {
                                        v_head_2368_ =
                                            leanh::lean_ctor_get(v_ctors_2364_, 0);
                                        leanh::lean_inc(v_head_2368_);
                                        v___f_2369_ = leanh::lean_alloc_closure(
                                            l_Lean_matchConstStructure___redArg___lam__0
                                                as *mut core::ffi::c_void,
                                            5,
                                            4,
                                        );
                                        leanh::lean_closure_set(v___f_2369_, 0, v_k_2343_);
                                        leanh::lean_closure_set(v___f_2369_, 1, v_val_2361_);
                                        leanh::lean_closure_set(v___f_2369_, 2, v_us_2344_);
                                        leanh::lean_closure_set(
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
                                        v___x_2371_ = leanh::lean_apply_4(
                                            v_toBind_2348_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_2370_,
                                            v___f_2369_,
                                        );
                                        return v___x_2371_;
                                    } else {
                                        leanh::lean_dec_ref(v_val_2361_);
                                        leanh::lean_dec(v_toBind_2348_);
                                        leanh::lean_dec_ref(v_inst_2347_);
                                        leanh::lean_dec_ref(v_inst_2346_);
                                        leanh::lean_dec_ref(v_inst_2345_);
                                        leanh::lean_dec(v_us_2344_);
                                        leanh::lean_dec(v_k_2343_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_val_2361_);
                                    leanh::lean_dec(v_toBind_2348_);
                                    leanh::lean_dec_ref(v_inst_2347_);
                                    leanh::lean_dec_ref(v_inst_2346_);
                                    leanh::lean_dec_ref(v_inst_2345_);
                                    leanh::lean_dec(v_us_2344_);
                                    leanh::lean_dec(v_k_2343_);
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_val_2361_);
                            leanh::lean_dec(v_toBind_2348_);
                            leanh::lean_dec_ref(v_inst_2347_);
                            leanh::lean_dec_ref(v_inst_2346_);
                            leanh::lean_dec_ref(v_inst_2345_);
                            leanh::lean_dec(v_us_2344_);
                            leanh::lean_dec(v_k_2343_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_2360_);
                        leanh::lean_dec(v_toBind_2348_);
                        leanh::lean_dec_ref(v_inst_2347_);
                        leanh::lean_dec_ref(v_inst_2346_);
                        leanh::lean_dec_ref(v_inst_2345_);
                        leanh::lean_dec(v_us_2344_);
                        leanh::lean_dec(v_k_2343_);
                        v___x_2372_ = leanh::lean_box(0);
                        v___x_2373_ = leanh::lean_apply_1(v_failK_2342_, v___x_2372_);
                        return v___x_2373_;
                    }
                }
            }
            1 => {
                v___x_2351_ = leanh::lean_box(0);
                v___x_2352_ = leanh::lean_apply_1(v_failK_2342_, v___x_2351_);
                return v___x_2352_;
            }
            2 => {
                v___x_2354_ = leanh::lean_box(0);
                v___x_2355_ = leanh::lean_apply_1(v_failK_2342_, v___x_2354_);
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg(
    mut v_inst_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_inst_2376_: *mut leanh::LeanObject,
    mut v_e_2377_: *mut leanh::LeanObject,
    mut v_failK_2378_: *mut leanh::LeanObject,
    mut v_k_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_2377_) == 4 {
        let mut v_toBind_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2380_ = leanh::lean_ctor_get(v_inst_2374_, 1);
        leanh::lean_inc_n(v_toBind_2380_, 2);
        v_declName_2381_ = leanh::lean_ctor_get(v_e_2377_, 0);
        leanh::lean_inc(v_declName_2381_);
        v_us_2382_ = leanh::lean_ctor_get(v_e_2377_, 1);
        leanh::lean_inc(v_us_2382_);
        leanh::lean_dec_ref_known(v_e_2377_, 2);
        v_getEnv_2383_ = leanh::lean_ctor_get(v_inst_2375_, 0);
        leanh::lean_inc(v_getEnv_2383_);
        v___f_2384_ = leanh::lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_2384_, 0, v_declName_2381_);
        leanh::lean_closure_set(v___f_2384_, 1, v_failK_2378_);
        leanh::lean_closure_set(v___f_2384_, 2, v_k_2379_);
        leanh::lean_closure_set(v___f_2384_, 3, v_us_2382_);
        leanh::lean_closure_set(v___f_2384_, 4, v_inst_2374_);
        leanh::lean_closure_set(v___f_2384_, 5, v_inst_2375_);
        leanh::lean_closure_set(v___f_2384_, 6, v_inst_2376_);
        leanh::lean_closure_set(v___f_2384_, 7, v_toBind_2380_);
        v___x_2385_ = leanh::lean_apply_4(
            v_toBind_2380_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2383_,
            v___f_2384_,
        );
        return v___x_2385_;
    } else {
        let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_2379_);
        leanh::lean_dec_ref(v_e_2377_);
        leanh::lean_dec_ref(v_inst_2376_);
        leanh::lean_dec_ref(v_inst_2375_);
        leanh::lean_dec_ref(v_inst_2374_);
        v___x_2386_ = leanh::lean_box(0);
        v___x_2387_ = leanh::lean_apply_1(v_failK_2378_, v___x_2386_);
        return v___x_2387_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure(
    mut v_m_2388_: *mut leanh::LeanObject,
    mut v_00_u03b1_2389_: *mut leanh::LeanObject,
    mut v_inst_2390_: *mut leanh::LeanObject,
    mut v_inst_2391_: *mut leanh::LeanObject,
    mut v_inst_2392_: *mut leanh::LeanObject,
    mut v_e_2393_: *mut leanh::LeanObject,
    mut v_failK_2394_: *mut leanh::LeanObject,
    mut v_k_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_2393_) == 4 {
        let mut v_toBind_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2396_ = leanh::lean_ctor_get(v_inst_2390_, 1);
        leanh::lean_inc_n(v_toBind_2396_, 2);
        v_declName_2397_ = leanh::lean_ctor_get(v_e_2393_, 0);
        leanh::lean_inc(v_declName_2397_);
        v_us_2398_ = leanh::lean_ctor_get(v_e_2393_, 1);
        leanh::lean_inc(v_us_2398_);
        leanh::lean_dec_ref_known(v_e_2393_, 2);
        v_getEnv_2399_ = leanh::lean_ctor_get(v_inst_2391_, 0);
        leanh::lean_inc(v_getEnv_2399_);
        v___f_2400_ = leanh::lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_2400_, 0, v_declName_2397_);
        leanh::lean_closure_set(v___f_2400_, 1, v_failK_2394_);
        leanh::lean_closure_set(v___f_2400_, 2, v_k_2395_);
        leanh::lean_closure_set(v___f_2400_, 3, v_us_2398_);
        leanh::lean_closure_set(v___f_2400_, 4, v_inst_2390_);
        leanh::lean_closure_set(v___f_2400_, 5, v_inst_2391_);
        leanh::lean_closure_set(v___f_2400_, 6, v_inst_2392_);
        leanh::lean_closure_set(v___f_2400_, 7, v_toBind_2396_);
        v___x_2401_ = leanh::lean_apply_4(
            v_toBind_2396_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2399_,
            v___f_2400_,
        );
        return v___x_2401_;
    } else {
        let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_2395_);
        leanh::lean_dec_ref(v_e_2393_);
        leanh::lean_dec_ref(v_inst_2392_);
        leanh::lean_dec_ref(v_inst_2391_);
        leanh::lean_dec_ref(v_inst_2390_);
        v___x_2402_ = leanh::lean_box(0);
        v___x_2403_ = leanh::lean_apply_1(v_failK_2394_, v___x_2402_);
        return v___x_2403_;
    }
}
pub unsafe fn l_Lean_hasCompileError___boxed(
    mut v_env_2406_: *mut leanh::LeanObject,
    mut v_constName_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = lean_has_compile_error(v_env_2406_, v_constName_2407_);
    v_r_2409_ = leanh::lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__0(
    mut v_____do__lift_2410_: *mut leanh::LeanObject,
    mut v_constName_2411_: *mut leanh::LeanObject,
    mut v_checkMeta_2412_: u8,
    mut v_inst_2413_: *mut leanh::LeanObject,
    mut v_inst_2414_: *mut leanh::LeanObject,
    mut v___x_2415_: *mut leanh::LeanObject,
    mut v_____do__lift_2416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_____do__lift_2419_: *mut leanh::LeanObject,
    mut v_constName_2420_: *mut leanh::LeanObject,
    mut v_checkMeta_2421_: *mut leanh::LeanObject,
    mut v_inst_2422_: *mut leanh::LeanObject,
    mut v_inst_2423_: *mut leanh::LeanObject,
    mut v___x_2424_: *mut leanh::LeanObject,
    mut v_____do__lift_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2426_: u8 = 0;
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2426_ = (leanh::lean_unbox(v_checkMeta_2421_) as u8);
    v_res_2427_ = l_Lean_evalConst___redArg___lam__0(
        v_____do__lift_2419_,
        v_constName_2420_,
        v_checkMeta_boxed_2426_,
        v_inst_2422_,
        v_inst_2423_,
        v___x_2424_,
        v_____do__lift_2425_,
    );
    leanh::lean_dec_ref(v_____do__lift_2425_);
    leanh::lean_dec(v_constName_2420_);
    leanh::lean_dec_ref(v_____do__lift_2419_);
    return v_res_2427_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1(
    mut v_constName_2428_: *mut leanh::LeanObject,
    mut v_checkMeta_2429_: u8,
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_inst_2431_: *mut leanh::LeanObject,
    mut v___x_2432_: *mut leanh::LeanObject,
    mut v_toBind_2433_: *mut leanh::LeanObject,
    mut v_inst_2434_: *mut leanh::LeanObject,
    mut v_____do__lift_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ = leanh::lean_box((v_checkMeta_2429_) as usize);
    v___f_2437_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2437_, 0, v_____do__lift_2435_);
    leanh::lean_closure_set(v___f_2437_, 1, v_constName_2428_);
    leanh::lean_closure_set(v___f_2437_, 2, v___x_2436_);
    leanh::lean_closure_set(v___f_2437_, 3, v_inst_2430_);
    leanh::lean_closure_set(v___f_2437_, 4, v_inst_2431_);
    leanh::lean_closure_set(v___f_2437_, 5, v___x_2432_);
    v___x_2438_ = leanh::lean_apply_4(
        v_toBind_2433_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2434_,
        v___f_2437_,
    );
    return v___x_2438_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1___boxed(
    mut v_constName_2439_: *mut leanh::LeanObject,
    mut v_checkMeta_2440_: *mut leanh::LeanObject,
    mut v_inst_2441_: *mut leanh::LeanObject,
    mut v_inst_2442_: *mut leanh::LeanObject,
    mut v___x_2443_: *mut leanh::LeanObject,
    mut v_toBind_2444_: *mut leanh::LeanObject,
    mut v_inst_2445_: *mut leanh::LeanObject,
    mut v_____do__lift_2446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2447_: u8 = 0;
    let mut v_res_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2447_ = (leanh::lean_unbox(v_checkMeta_2440_) as u8);
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
    mut v_toBind_2449_: *mut leanh::LeanObject,
    mut v_getEnv_2450_: *mut leanh::LeanObject,
    mut v___f_2451_: *mut leanh::LeanObject,
    mut v_____r_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = leanh::lean_apply_4(
        v_toBind_2449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2450_,
        v___f_2451_,
    );
    return v___x_2453_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__3(
    mut v_constName_2454_: *mut leanh::LeanObject,
    mut v_toBind_2455_: *mut leanh::LeanObject,
    mut v_getEnv_2456_: *mut leanh::LeanObject,
    mut v___f_2457_: *mut leanh::LeanObject,
    mut v_inst_2458_: *mut leanh::LeanObject,
    mut v___f_2459_: *mut leanh::LeanObject,
    mut v_____do__lift_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2461_: u8 = 0;
    v___x_2461_ = lean_has_compile_error(v_____do__lift_2460_, v_constName_2454_);
    if v___x_2461_ == 0 {
        let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2459_);
        leanh::lean_dec_ref(v_inst_2458_);
        v___x_2462_ = leanh::lean_apply_4(
            v_toBind_2455_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2456_,
            v___f_2457_,
        );
        return v___x_2462_;
    } else {
        let mut v_toMonadExceptOf_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2457_);
        leanh::lean_dec(v_getEnv_2456_);
        v_toMonadExceptOf_2463_ = leanh::lean_ctor_get(v_inst_2458_, 0);
        leanh::lean_inc_ref(v_toMonadExceptOf_2463_);
        leanh::lean_dec_ref(v_inst_2458_);
        v___x_2464_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_2463_);
        v___x_2465_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_2464_);
        v___x_2466_ = leanh::lean_apply_4(
            v_toBind_2455_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2465_,
            v___f_2459_,
        );
        return v___x_2466_;
    }
}
pub unsafe fn l_Lean_evalConst___redArg(
    mut v_inst_2468_: *mut leanh::LeanObject,
    mut v_inst_2469_: *mut leanh::LeanObject,
    mut v_inst_2470_: *mut leanh::LeanObject,
    mut v_inst_2471_: *mut leanh::LeanObject,
    mut v_constName_2472_: *mut leanh::LeanObject,
    mut v_checkMeta_2473_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2474_ = leanh::lean_ctor_get(v_inst_2468_, 1);
    leanh::lean_inc_n(v_toBind_2474_, 4);
    v_getEnv_2475_ = leanh::lean_ctor_get(v_inst_2469_, 0);
    leanh::lean_inc_n(v_getEnv_2475_, 3);
    leanh::lean_dec_ref(v_inst_2469_);
    v___x_2476_ = l_Lean_evalConst___redArg___closed__0;
    v___x_2477_ = leanh::lean_box((v_checkMeta_2473_) as usize);
    leanh::lean_inc_ref(v_inst_2470_);
    leanh::lean_inc(v_constName_2472_);
    v___f_2478_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2478_, 0, v_constName_2472_);
    leanh::lean_closure_set(v___f_2478_, 1, v___x_2477_);
    leanh::lean_closure_set(v___f_2478_, 2, v_inst_2468_);
    leanh::lean_closure_set(v___f_2478_, 3, v_inst_2470_);
    leanh::lean_closure_set(v___f_2478_, 4, v___x_2476_);
    leanh::lean_closure_set(v___f_2478_, 5, v_toBind_2474_);
    leanh::lean_closure_set(v___f_2478_, 6, v_inst_2471_);
    leanh::lean_inc_ref(v___f_2478_);
    v___f_2479_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2479_, 0, v_toBind_2474_);
    leanh::lean_closure_set(v___f_2479_, 1, v_getEnv_2475_);
    leanh::lean_closure_set(v___f_2479_, 2, v___f_2478_);
    v___f_2480_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2480_, 0, v_constName_2472_);
    leanh::lean_closure_set(v___f_2480_, 1, v_toBind_2474_);
    leanh::lean_closure_set(v___f_2480_, 2, v_getEnv_2475_);
    leanh::lean_closure_set(v___f_2480_, 3, v___f_2478_);
    leanh::lean_closure_set(v___f_2480_, 4, v_inst_2470_);
    leanh::lean_closure_set(v___f_2480_, 5, v___f_2479_);
    v___x_2481_ = leanh::lean_apply_4(
        v_toBind_2474_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2475_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_evalConst___redArg___boxed(
    mut v_inst_2482_: *mut leanh::LeanObject,
    mut v_inst_2483_: *mut leanh::LeanObject,
    mut v_inst_2484_: *mut leanh::LeanObject,
    mut v_inst_2485_: *mut leanh::LeanObject,
    mut v_constName_2486_: *mut leanh::LeanObject,
    mut v_checkMeta_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2488_: u8 = 0;
    let mut v_res_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2488_ = (leanh::lean_unbox(v_checkMeta_2487_) as u8);
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
    mut v_m_2490_: *mut leanh::LeanObject,
    mut v_inst_2491_: *mut leanh::LeanObject,
    mut v_inst_2492_: *mut leanh::LeanObject,
    mut v_inst_2493_: *mut leanh::LeanObject,
    mut v_inst_2494_: *mut leanh::LeanObject,
    mut v_00_u03b1_2495_: *mut leanh::LeanObject,
    mut v_constName_2496_: *mut leanh::LeanObject,
    mut v_checkMeta_2497_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_inst_2501_: *mut leanh::LeanObject,
    mut v_inst_2502_: *mut leanh::LeanObject,
    mut v_inst_2503_: *mut leanh::LeanObject,
    mut v_00_u03b1_2504_: *mut leanh::LeanObject,
    mut v_constName_2505_: *mut leanh::LeanObject,
    mut v_checkMeta_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2507_: u8 = 0;
    let mut v_res_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2507_ = (leanh::lean_unbox(v_checkMeta_2506_) as u8);
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
    mut v_____do__lift_2509_: *mut leanh::LeanObject,
    mut v_typeName_2510_: *mut leanh::LeanObject,
    mut v_constName_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
    mut v___x_2514_: *mut leanh::LeanObject,
    mut v_____do__lift_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_____do__lift_2518_: *mut leanh::LeanObject,
    mut v_typeName_2519_: *mut leanh::LeanObject,
    mut v_constName_2520_: *mut leanh::LeanObject,
    mut v_inst_2521_: *mut leanh::LeanObject,
    mut v_inst_2522_: *mut leanh::LeanObject,
    mut v___x_2523_: *mut leanh::LeanObject,
    mut v_____do__lift_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_evalConstCheck___redArg___lam__0(
        v_____do__lift_2518_,
        v_typeName_2519_,
        v_constName_2520_,
        v_inst_2521_,
        v_inst_2522_,
        v___x_2523_,
        v_____do__lift_2524_,
    );
    leanh::lean_dec_ref(v_____do__lift_2524_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg___lam__1(
    mut v_typeName_2526_: *mut leanh::LeanObject,
    mut v_constName_2527_: *mut leanh::LeanObject,
    mut v_inst_2528_: *mut leanh::LeanObject,
    mut v_inst_2529_: *mut leanh::LeanObject,
    mut v___x_2530_: *mut leanh::LeanObject,
    mut v_toBind_2531_: *mut leanh::LeanObject,
    mut v_inst_2532_: *mut leanh::LeanObject,
    mut v_____do__lift_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2534_ = leanh::lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2534_, 0, v_____do__lift_2533_);
    leanh::lean_closure_set(v___f_2534_, 1, v_typeName_2526_);
    leanh::lean_closure_set(v___f_2534_, 2, v_constName_2527_);
    leanh::lean_closure_set(v___f_2534_, 3, v_inst_2528_);
    leanh::lean_closure_set(v___f_2534_, 4, v_inst_2529_);
    leanh::lean_closure_set(v___f_2534_, 5, v___x_2530_);
    v___x_2535_ = leanh::lean_apply_4(
        v_toBind_2531_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2532_,
        v___f_2534_,
    );
    return v___x_2535_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg(
    mut v_inst_2536_: *mut leanh::LeanObject,
    mut v_inst_2537_: *mut leanh::LeanObject,
    mut v_inst_2538_: *mut leanh::LeanObject,
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_typeName_2540_: *mut leanh::LeanObject,
    mut v_constName_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2542_ = leanh::lean_ctor_get(v_inst_2536_, 1);
    leanh::lean_inc_n(v_toBind_2542_, 4);
    v_getEnv_2543_ = leanh::lean_ctor_get(v_inst_2537_, 0);
    leanh::lean_inc_n(v_getEnv_2543_, 3);
    leanh::lean_dec_ref(v_inst_2537_);
    v___x_2544_ = l_Lean_evalConst___redArg___closed__0;
    leanh::lean_inc_ref(v_inst_2538_);
    leanh::lean_inc(v_constName_2541_);
    v___f_2545_ = leanh::lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2545_, 0, v_typeName_2540_);
    leanh::lean_closure_set(v___f_2545_, 1, v_constName_2541_);
    leanh::lean_closure_set(v___f_2545_, 2, v_inst_2536_);
    leanh::lean_closure_set(v___f_2545_, 3, v_inst_2538_);
    leanh::lean_closure_set(v___f_2545_, 4, v___x_2544_);
    leanh::lean_closure_set(v___f_2545_, 5, v_toBind_2542_);
    leanh::lean_closure_set(v___f_2545_, 6, v_inst_2539_);
    leanh::lean_inc_ref(v___f_2545_);
    v___f_2546_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2546_, 0, v_toBind_2542_);
    leanh::lean_closure_set(v___f_2546_, 1, v_getEnv_2543_);
    leanh::lean_closure_set(v___f_2546_, 2, v___f_2545_);
    v___f_2547_ = leanh::lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2547_, 0, v_constName_2541_);
    leanh::lean_closure_set(v___f_2547_, 1, v_toBind_2542_);
    leanh::lean_closure_set(v___f_2547_, 2, v_getEnv_2543_);
    leanh::lean_closure_set(v___f_2547_, 3, v___f_2545_);
    leanh::lean_closure_set(v___f_2547_, 4, v_inst_2538_);
    leanh::lean_closure_set(v___f_2547_, 5, v___f_2546_);
    v___x_2548_ = leanh::lean_apply_4(
        v_toBind_2542_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2543_,
        v___f_2547_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_evalConstCheck(
    mut v_m_2549_: *mut leanh::LeanObject,
    mut v_inst_2550_: *mut leanh::LeanObject,
    mut v_inst_2551_: *mut leanh::LeanObject,
    mut v_inst_2552_: *mut leanh::LeanObject,
    mut v_inst_2553_: *mut leanh::LeanObject,
    mut v_00_u03b1_2554_: *mut leanh::LeanObject,
    mut v_typeName_2555_: *mut leanh::LeanObject,
    mut v_constName_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_2558_: *mut leanh::LeanObject,
    mut v_val_2559_: *mut leanh::LeanObject,
    mut v_toPure_2560_: *mut leanh::LeanObject,
    mut v_____do__lift_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_2561_);
    v___x_2563_ = lean_array_get(v___x_2558_, v___x_2562_, v_val_2559_);
    leanh::lean_dec_ref(v___x_2562_);
    v___x_2564_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    v___x_2565_ =
        leanh::lean_apply_2(v_toPure_2560_, leanh::lean_box(0), v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(
    mut v___x_2566_: *mut leanh::LeanObject,
    mut v_val_2567_: *mut leanh::LeanObject,
    mut v_toPure_2568_: *mut leanh::LeanObject,
    mut v_____do__lift_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Lean_findModuleOf_x3f___redArg___lam__0(
        v___x_2566_,
        v_val_2567_,
        v_toPure_2568_,
        v_____do__lift_2569_,
    );
    leanh::lean_dec_ref(v_____do__lift_2569_);
    leanh::lean_dec(v_val_2567_);
    leanh::lean_dec(v___x_2566_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1(
    mut v_declName_2571_: *mut leanh::LeanObject,
    mut v_toPure_2572_: *mut leanh::LeanObject,
    mut v___x_2573_: *mut leanh::LeanObject,
    mut v_toBind_2574_: *mut leanh::LeanObject,
    mut v_getEnv_2575_: *mut leanh::LeanObject,
    mut v_____do__lift_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2576_, v_declName_2571_);
    if leanh::lean_obj_tag(v___x_2577_) == 0 {
        let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_getEnv_2575_);
        leanh::lean_dec(v_toBind_2574_);
        leanh::lean_dec(v___x_2573_);
        v___x_2578_ = leanh::lean_box(0);
        v___x_2579_ =
            leanh::lean_apply_2(v_toPure_2572_, leanh::lean_box(0), v___x_2578_);
        return v___x_2579_;
    } else {
        let mut v_val_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2580_ = leanh::lean_ctor_get(v___x_2577_, 0);
        leanh::lean_inc(v_val_2580_);
        leanh::lean_dec_ref_known(v___x_2577_, 1);
        v___f_2581_ = leanh::lean_alloc_closure(
            l_Lean_findModuleOf_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_2581_, 0, v___x_2573_);
        leanh::lean_closure_set(v___f_2581_, 1, v_val_2580_);
        leanh::lean_closure_set(v___f_2581_, 2, v_toPure_2572_);
        v___x_2582_ = leanh::lean_apply_4(
            v_toBind_2574_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_2575_,
            v___f_2581_,
        );
        return v___x_2582_;
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(
    mut v_declName_2583_: *mut leanh::LeanObject,
    mut v_toPure_2584_: *mut leanh::LeanObject,
    mut v___x_2585_: *mut leanh::LeanObject,
    mut v_toBind_2586_: *mut leanh::LeanObject,
    mut v_getEnv_2587_: *mut leanh::LeanObject,
    mut v_____do__lift_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_Lean_findModuleOf_x3f___redArg___lam__1(
        v_declName_2583_,
        v_toPure_2584_,
        v___x_2585_,
        v_toBind_2586_,
        v_getEnv_2587_,
        v_____do__lift_2588_,
    );
    leanh::lean_dec_ref(v_____do__lift_2588_);
    leanh::lean_dec(v_declName_2583_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__2(
    mut v_inst_2590_: *mut leanh::LeanObject,
    mut v_declName_2591_: *mut leanh::LeanObject,
    mut v_toPure_2592_: *mut leanh::LeanObject,
    mut v___x_2593_: *mut leanh::LeanObject,
    mut v_toBind_2594_: *mut leanh::LeanObject,
    mut v_____r_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getEnv_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_2596_ = leanh::lean_ctor_get(v_inst_2590_, 0);
    leanh::lean_inc_n(v_getEnv_2596_, 2);
    leanh::lean_dec_ref(v_inst_2590_);
    leanh::lean_inc(v_toBind_2594_);
    v___f_2597_ = leanh::lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2597_, 0, v_declName_2591_);
    leanh::lean_closure_set(v___f_2597_, 1, v_toPure_2592_);
    leanh::lean_closure_set(v___f_2597_, 2, v___x_2593_);
    leanh::lean_closure_set(v___f_2597_, 3, v_toBind_2594_);
    leanh::lean_closure_set(v___f_2597_, 4, v_getEnv_2596_);
    v___x_2598_ = leanh::lean_apply_4(
        v_toBind_2594_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2596_,
        v___f_2597_,
    );
    return v___x_2598_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg(
    mut v_inst_2599_: *mut leanh::LeanObject,
    mut v_inst_2600_: *mut leanh::LeanObject,
    mut v_inst_2601_: *mut leanh::LeanObject,
    mut v_declName_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2603_ = leanh::lean_ctor_get(v_inst_2599_, 0);
    v_toFunctor_2604_ = leanh::lean_ctor_get(v_toApplicative_2603_, 0);
    v_toBind_2605_ = leanh::lean_ctor_get(v_inst_2599_, 1);
    leanh::lean_inc_n(v_toBind_2605_, 2);
    v_toPure_2606_ = leanh::lean_ctor_get(v_toApplicative_2603_, 1);
    v_mapConst_2607_ = leanh::lean_ctor_get(v_toFunctor_2604_, 1);
    leanh::lean_inc(v_mapConst_2607_);
    v___x_2608_ = leanh::lean_box(0);
    leanh::lean_inc(v_toPure_2606_);
    leanh::lean_inc(v_declName_2602_);
    leanh::lean_inc_ref(v_inst_2600_);
    v___f_2609_ = leanh::lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2609_, 0, v_inst_2600_);
    leanh::lean_closure_set(v___f_2609_, 1, v_declName_2602_);
    leanh::lean_closure_set(v___f_2609_, 2, v_toPure_2606_);
    leanh::lean_closure_set(v___f_2609_, 3, v___x_2608_);
    leanh::lean_closure_set(v___f_2609_, 4, v_toBind_2605_);
    v___x_2610_ =
        l_Lean_getConstInfo___redArg(v_inst_2599_, v_inst_2600_, v_inst_2601_, v_declName_2602_);
    v___x_2611_ = leanh::lean_box(0);
    v___x_2612_ = leanh::lean_apply_4(
        v_mapConst_2607_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2611_,
        v___x_2610_,
    );
    v___x_2613_ = leanh::lean_apply_4(
        v_toBind_2605_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2612_,
        v___f_2609_,
    );
    return v___x_2613_;
}
pub unsafe fn l_Lean_findModuleOf_x3f(
    mut v_m_2614_: *mut leanh::LeanObject,
    mut v_inst_2615_: *mut leanh::LeanObject,
    mut v_inst_2616_: *mut leanh::LeanObject,
    mut v_inst_2617_: *mut leanh::LeanObject,
    mut v_declName_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_findModuleOf_x3f___redArg(
        v_inst_2615_,
        v_inst_2616_,
        v_inst_2617_,
        v_declName_2618_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0(
    mut v___x_2620_: *mut leanh::LeanObject,
    mut v_toPure_2621_: *mut leanh::LeanObject,
    mut v_isUnsafe_2622_: u8,
    mut v_____x_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_2623_) == 6 {
        let mut v_val_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2626_: u8 = 0;
        let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2624_ = leanh::lean_ctor_get(v_____x_2623_, 0);
        v_numFields_2625_ = leanh::lean_ctor_get(v_val_2624_, 4);
        v___x_2626_ = lean_nat_dec_eq(v_numFields_2625_, v___x_2620_);
        v___x_2627_ = leanh::lean_box((v___x_2626_) as usize);
        v___x_2628_ =
            leanh::lean_apply_2(v_toPure_2621_, leanh::lean_box(0), v___x_2627_);
        return v___x_2628_;
    } else {
        let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2629_ = leanh::lean_box((v_isUnsafe_2622_) as usize);
        v___x_2630_ =
            leanh::lean_apply_2(v_toPure_2621_, leanh::lean_box(0), v___x_2629_);
        return v___x_2630_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0___boxed(
    mut v___x_2631_: *mut leanh::LeanObject,
    mut v_toPure_2632_: *mut leanh::LeanObject,
    mut v_isUnsafe_2633_: *mut leanh::LeanObject,
    mut v_____x_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isUnsafe_boxed_2635_: u8 = 0;
    let mut v_res_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2635_ = (leanh::lean_unbox(v_isUnsafe_2633_) as u8);
    v_res_2636_ = l_Lean_isEnumType___redArg___lam__0(
        v___x_2631_,
        v_toPure_2632_,
        v_isUnsafe_boxed_2635_,
        v_____x_2634_,
    );
    leanh::lean_dec_ref(v_____x_2634_);
    leanh::lean_dec(v___x_2631_);
    return v_res_2636_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__1(
    mut v_inst_2637_: *mut leanh::LeanObject,
    mut v_inst_2638_: *mut leanh::LeanObject,
    mut v_inst_2639_: *mut leanh::LeanObject,
    mut v_toBind_2640_: *mut leanh::LeanObject,
    mut v___f_2641_: *mut leanh::LeanObject,
    mut v_ctorName_2642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ =
        l_Lean_getConstInfo___redArg(v_inst_2637_, v_inst_2638_, v_inst_2639_, v_ctorName_2642_);
    v___x_2644_ = leanh::lean_apply_4(
        v_toBind_2640_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2643_,
        v___f_2641_,
    );
    return v___x_2644_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__2(
    mut v_toPure_2645_: *mut leanh::LeanObject,
    mut v_inst_2646_: *mut leanh::LeanObject,
    mut v_inst_2647_: *mut leanh::LeanObject,
    mut v_inst_2648_: *mut leanh::LeanObject,
    mut v_toBind_2649_: *mut leanh::LeanObject,
    mut v_____do__lift_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2650_) == 5 {
        let mut v_val_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toConstantVal_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numParams_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numIndices_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ctors_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isRec_2656_: u8 = 0;
        let mut v_isUnsafe_2657_: u8 = 0;
        let mut v_type_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2659_: u8 = 0;
        v_val_2651_ = leanh::lean_ctor_get(v_____do__lift_2650_, 0);
        leanh::lean_inc_ref(v_val_2651_);
        leanh::lean_dec_ref_known(v_____do__lift_2650_, 1);
        v_toConstantVal_2652_ = leanh::lean_ctor_get(v_val_2651_, 0);
        v_numParams_2653_ = leanh::lean_ctor_get(v_val_2651_, 1);
        leanh::lean_inc(v_numParams_2653_);
        v_numIndices_2654_ = leanh::lean_ctor_get(v_val_2651_, 2);
        leanh::lean_inc(v_numIndices_2654_);
        v_ctors_2655_ = leanh::lean_ctor_get(v_val_2651_, 4);
        leanh::lean_inc(v_ctors_2655_);
        v_isRec_2656_ = leanh::lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
        );
        v_isUnsafe_2657_ = leanh::lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 6 + 1) as u32,
        );
        v_type_2658_ = leanh::lean_ctor_get(v_toConstantVal_2652_, 2);
        v___x_2659_ = l_Lean_Expr_isProp(v_type_2658_);
        if v___x_2659_ == 0 {
            let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2662_: u8 = 0;
            v___x_2660_ = l_Lean_InductiveVal_numTypeFormers(v_val_2651_);
            leanh::lean_dec_ref(v_val_2651_);
            v___x_2661_ = leanh::lean_unsigned_to_nat(1);
            v___x_2662_ = lean_nat_dec_eq(v___x_2660_, v___x_2661_);
            leanh::lean_dec(v___x_2660_);
            if v___x_2662_ == 0 {
                let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_ctors_2655_);
                leanh::lean_dec(v_numIndices_2654_);
                leanh::lean_dec(v_numParams_2653_);
                leanh::lean_dec(v_toBind_2649_);
                leanh::lean_dec_ref(v_inst_2648_);
                leanh::lean_dec_ref(v_inst_2647_);
                leanh::lean_dec_ref(v_inst_2646_);
                v___x_2663_ = leanh::lean_box((v___x_2662_) as usize);
                v___x_2664_ = leanh::lean_apply_2(
                    v_toPure_2645_,
                    leanh::lean_box(0),
                    v___x_2663_,
                );
                return v___x_2664_;
            } else {
                let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2666_: u8 = 0;
                v___x_2665_ = leanh::lean_unsigned_to_nat(0);
                v___x_2666_ = lean_nat_dec_eq(v_numIndices_2654_, v___x_2665_);
                leanh::lean_dec(v_numIndices_2654_);
                if v___x_2666_ == 0 {
                    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_ctors_2655_);
                    leanh::lean_dec(v_numParams_2653_);
                    leanh::lean_dec(v_toBind_2649_);
                    leanh::lean_dec_ref(v_inst_2648_);
                    leanh::lean_dec_ref(v_inst_2647_);
                    leanh::lean_dec_ref(v_inst_2646_);
                    v___x_2667_ = leanh::lean_box((v___x_2666_) as usize);
                    v___x_2668_ = leanh::lean_apply_2(
                        v_toPure_2645_,
                        leanh::lean_box(0),
                        v___x_2667_,
                    );
                    return v___x_2668_;
                } else {
                    let mut v___x_2669_: u8 = 0;
                    v___x_2669_ = lean_nat_dec_eq(v_numParams_2653_, v___x_2665_);
                    leanh::lean_dec(v_numParams_2653_);
                    if v___x_2669_ == 0 {
                        let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v_ctors_2655_);
                        leanh::lean_dec(v_toBind_2649_);
                        leanh::lean_dec_ref(v_inst_2648_);
                        leanh::lean_dec_ref(v_inst_2647_);
                        leanh::lean_dec_ref(v_inst_2646_);
                        v___x_2670_ = leanh::lean_box((v___x_2669_) as usize);
                        v___x_2671_ = leanh::lean_apply_2(
                            v_toPure_2645_,
                            leanh::lean_box(0),
                            v___x_2670_,
                        );
                        return v___x_2671_;
                    } else {
                        let mut v___x_2672_: u8 = 0;
                        v___x_2672_ = l_List_isEmpty___redArg(v_ctors_2655_);
                        if v___x_2672_ == 0 {
                            if v_isRec_2656_ == 0 {
                                if v_isUnsafe_2657_ == 0 {
                                    let mut v___x_2673_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_2674_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_2675_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2676_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_2673_ =
                                        leanh::lean_box((v_isUnsafe_2657_) as usize);
                                    v___f_2674_ = leanh::lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    leanh::lean_closure_set(v___f_2674_, 0, v___x_2665_);
                                    leanh::lean_closure_set(v___f_2674_, 1, v_toPure_2645_);
                                    leanh::lean_closure_set(v___f_2674_, 2, v___x_2673_);
                                    leanh::lean_inc_ref(v_inst_2646_);
                                    v___f_2675_ = leanh::lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__1
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    leanh::lean_closure_set(v___f_2675_, 0, v_inst_2646_);
                                    leanh::lean_closure_set(v___f_2675_, 1, v_inst_2647_);
                                    leanh::lean_closure_set(v___f_2675_, 2, v_inst_2648_);
                                    leanh::lean_closure_set(v___f_2675_, 3, v_toBind_2649_);
                                    leanh::lean_closure_set(v___f_2675_, 4, v___f_2674_);
                                    v___x_2676_ = l_List_allM___redArg(
                                        v_inst_2646_,
                                        v___f_2675_,
                                        v_ctors_2655_,
                                    );
                                    return v___x_2676_;
                                } else {
                                    let mut v___x_2677_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2678_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v_ctors_2655_);
                                    leanh::lean_dec(v_toBind_2649_);
                                    leanh::lean_dec_ref(v_inst_2648_);
                                    leanh::lean_dec_ref(v_inst_2647_);
                                    leanh::lean_dec_ref(v_inst_2646_);
                                    v___x_2677_ = leanh::lean_box((v_isRec_2656_) as usize);
                                    v___x_2678_ = leanh::lean_apply_2(
                                        v_toPure_2645_,
                                        leanh::lean_box(0),
                                        v___x_2677_,
                                    );
                                    return v___x_2678_;
                                }
                            } else {
                                let mut v___x_2679_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2680_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v_ctors_2655_);
                                leanh::lean_dec(v_toBind_2649_);
                                leanh::lean_dec_ref(v_inst_2648_);
                                leanh::lean_dec_ref(v_inst_2647_);
                                leanh::lean_dec_ref(v_inst_2646_);
                                v___x_2679_ = leanh::lean_box((v___x_2672_) as usize);
                                v___x_2680_ = leanh::lean_apply_2(
                                    v_toPure_2645_,
                                    leanh::lean_box(0),
                                    v___x_2679_,
                                );
                                return v___x_2680_;
                            }
                        } else {
                            let mut v___x_2681_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2682_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v_ctors_2655_);
                            leanh::lean_dec(v_toBind_2649_);
                            leanh::lean_dec_ref(v_inst_2648_);
                            leanh::lean_dec_ref(v_inst_2647_);
                            leanh::lean_dec_ref(v_inst_2646_);
                            v___x_2681_ = leanh::lean_box((v___x_2659_) as usize);
                            v___x_2682_ = leanh::lean_apply_2(
                                v_toPure_2645_,
                                leanh::lean_box(0),
                                v___x_2681_,
                            );
                            return v___x_2682_;
                        }
                    }
                }
            }
        } else {
            let mut v___x_2683_: u8 = 0;
            let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_ctors_2655_);
            leanh::lean_dec(v_numIndices_2654_);
            leanh::lean_dec(v_numParams_2653_);
            leanh::lean_dec_ref(v_val_2651_);
            leanh::lean_dec(v_toBind_2649_);
            leanh::lean_dec_ref(v_inst_2648_);
            leanh::lean_dec_ref(v_inst_2647_);
            leanh::lean_dec_ref(v_inst_2646_);
            v___x_2683_ = 0;
            v___x_2684_ = leanh::lean_box((v___x_2683_) as usize);
            v___x_2685_ =
                leanh::lean_apply_2(v_toPure_2645_, leanh::lean_box(0), v___x_2684_);
            return v___x_2685_;
        }
    } else {
        let mut v___x_2686_: u8 = 0;
        let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_____do__lift_2650_);
        leanh::lean_dec(v_toBind_2649_);
        leanh::lean_dec_ref(v_inst_2648_);
        leanh::lean_dec_ref(v_inst_2647_);
        leanh::lean_dec_ref(v_inst_2646_);
        v___x_2686_ = 0;
        v___x_2687_ = leanh::lean_box((v___x_2686_) as usize);
        v___x_2688_ =
            leanh::lean_apply_2(v_toPure_2645_, leanh::lean_box(0), v___x_2687_);
        return v___x_2688_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg(
    mut v_inst_2689_: *mut leanh::LeanObject,
    mut v_inst_2690_: *mut leanh::LeanObject,
    mut v_inst_2691_: *mut leanh::LeanObject,
    mut v_declName_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2693_ = leanh::lean_ctor_get(v_inst_2689_, 0);
    v_toBind_2694_ = leanh::lean_ctor_get(v_inst_2689_, 1);
    leanh::lean_inc_n(v_toBind_2694_, 2);
    v_toPure_2695_ = leanh::lean_ctor_get(v_toApplicative_2693_, 1);
    leanh::lean_inc(v_toPure_2695_);
    leanh::lean_inc_ref(v_inst_2691_);
    leanh::lean_inc_ref(v_inst_2690_);
    leanh::lean_inc_ref(v_inst_2689_);
    v___x_2696_ =
        l_Lean_getConstInfo___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_declName_2692_);
    v___f_2697_ = leanh::lean_alloc_closure(
        l_Lean_isEnumType___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2697_, 0, v_toPure_2695_);
    leanh::lean_closure_set(v___f_2697_, 1, v_inst_2689_);
    leanh::lean_closure_set(v___f_2697_, 2, v_inst_2690_);
    leanh::lean_closure_set(v___f_2697_, 3, v_inst_2691_);
    leanh::lean_closure_set(v___f_2697_, 4, v_toBind_2694_);
    v___x_2698_ = leanh::lean_apply_4(
        v_toBind_2694_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2696_,
        v___f_2697_,
    );
    return v___x_2698_;
}
pub unsafe fn l_Lean_isEnumType(
    mut v_m_2699_: *mut leanh::LeanObject,
    mut v_inst_2700_: *mut leanh::LeanObject,
    mut v_inst_2701_: *mut leanh::LeanObject,
    mut v_inst_2702_: *mut leanh::LeanObject,
    mut v_declName_2703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ =
        l_Lean_isEnumType___redArg(v_inst_2700_, v_inst_2701_, v_inst_2702_, v_declName_2703_);
    return v___x_2704_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_MonadEnv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AuxRecursor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_MonadEnv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_MonadEnv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_AuxRecursor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Old(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_MonadEnv(builtin);
}