// Lean compiler output
// Module: Lean.MonadEnv
// Imports: Init.Control.Do Lean.Elab.Exception Lean.Log Lean.AuxRecursor Lean.Compiler.Old
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_nat_dec_eq, lean_panic_fn_borrowed,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_withEnv___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withEnv___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_withEnv___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withEnv___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withoutModifyingEnv_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_isInductiveCore_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__1_value: LeanStringObject<22> = LeanStringObject {
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
        76, 101, 97, 110, 46, 105, 115, 73, 110, 100, 117, 99, 116, 105, 118, 101, 67, 111, 114,
        101, 63, 0,
    ],
};
static mut l_Lean_isInductiveCore_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_isInductiveCore_x3f___closed__2_value: LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_isInductiveCore_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isInductiveCore_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_isInductiveCore_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_isInductiveCore_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_isDefn_x3f___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_isCtor_x3f___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_isRec_x3f___redArg___lam__0___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isRec_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_isRec_x3f___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_mkLevelParam as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value: LeanStringObject<2> =
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
        m_data: [96, 0],
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value: LeanStringObject<22> =
    LeanStringObject {
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
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116,
            105, 111, 110, 0,
        ],
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoDefn___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value: LeanStringObject<27> =
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
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105,
            118, 101, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoInduct___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99,
            116, 111, 114, 0,
        ],
    };
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getConstInfoCtor___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value: LeanStringObject<20> =
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
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114,
            0,
        ],
    };
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoRec___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_evalConst___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_stringToMessageData as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_evalConst___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_evalConst___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_setEnv___redArg___lam__0(
    mut v_env_1353_: *mut LeanObject,
    mut v_x_1354_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_env_1353_);
    return v_env_1353_;
}
pub unsafe fn l_Lean_setEnv___redArg___lam__0___boxed(
    mut v_env_1355_: *mut LeanObject,
    mut v_x_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1357_: *mut LeanObject = core::ptr::null_mut();
    v_res_1357_ = l_Lean_setEnv___redArg___lam__0(v_env_1355_, v_x_1356_);
    lean_dec_ref(v_x_1356_);
    lean_dec_ref(v_env_1355_);
    return v_res_1357_;
}
pub unsafe fn l_Lean_setEnv___redArg(
    mut v_inst_1358_: *mut LeanObject,
    mut v_env_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_1360_ = lean_ctor_get(v_inst_1358_, 1);
    lean_inc(v_modifyEnv_1360_);
    lean_dec_ref(v_inst_1358_);
    v___f_1361_ = lean_alloc_closure(
        l_Lean_setEnv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1361_, 0, v_env_1359_);
    v___x_1362_ = lean_apply_1(v_modifyEnv_1360_, v___f_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lean_setEnv(
    mut v_m_1363_: *mut LeanObject,
    mut v_inst_1364_: *mut LeanObject,
    mut v_env_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_setEnv___redArg(v_inst_1364_, v_env_1365_);
    return v___x_1366_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0(mut v_x_1367_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_1368_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1368_ = lean_ctor_get(v_x_1367_, 0);
    lean_inc(v_fst_1368_);
    return v_fst_1368_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__0___boxed(
    mut v_x_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1370_: *mut LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_withEnv___redArg___lam__0(v_x_1369_);
    lean_dec_ref(v_x_1369_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1(
    mut v_x_1371_: *mut LeanObject,
    mut v_____r_1372_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1371_);
    return v_x_1371_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__1___boxed(
    mut v_x_1373_: *mut LeanObject,
    mut v_____r_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_withEnv___redArg___lam__1(v_x_1373_, v_____r_1374_);
    lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2(
    mut v___x_1376_: *mut LeanObject,
    mut v_x_1377_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_1376_);
    return v___x_1376_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__2___boxed(
    mut v___x_1378_: *mut LeanObject,
    mut v_x_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1380_: *mut LeanObject = core::ptr::null_mut();
    v_res_1380_ = l_Lean_withEnv___redArg___lam__2(v___x_1378_, v_x_1379_);
    lean_dec(v_x_1379_);
    lean_dec(v___x_1378_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_withEnv___redArg___lam__3(
    mut v_toFunctor_1381_: *mut LeanObject,
    mut v_inst_1382_: *mut LeanObject,
    mut v_env_1383_: *mut LeanObject,
    mut v_toBind_1384_: *mut LeanObject,
    mut v___f_1385_: *mut LeanObject,
    mut v_inst_1386_: *mut LeanObject,
    mut v___f_1387_: *mut LeanObject,
    mut v_saved_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v_map_1389_ = lean_ctor_get(v_toFunctor_1381_, 0);
    lean_inc(v_map_1389_);
    lean_dec_ref(v_toFunctor_1381_);
    lean_inc_ref(v_inst_1382_);
    v___x_1390_ = l_Lean_setEnv___redArg(v_inst_1382_, v_env_1383_);
    v___x_1391_ = lean_apply_4(
        v_toBind_1384_,
        lean_box(0),
        lean_box(0),
        v___x_1390_,
        v___f_1385_,
    );
    v___x_1392_ = l_Lean_setEnv___redArg(v_inst_1382_, v_saved_1388_);
    v___f_1393_ = lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1393_, 0, v___x_1392_);
    v_y_1394_ = lean_apply_4(
        v_inst_1386_,
        lean_box(0),
        lean_box(0),
        v___x_1391_,
        v___f_1393_,
    );
    v___x_1395_ = lean_apply_4(
        v_map_1389_,
        lean_box(0),
        lean_box(0),
        v___f_1387_,
        v_y_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Lean_withEnv___redArg(
    mut v_inst_1397_: *mut LeanObject,
    mut v_inst_1398_: *mut LeanObject,
    mut v_inst_1399_: *mut LeanObject,
    mut v_env_1400_: *mut LeanObject,
    mut v_x_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1402_ = lean_ctor_get(v_inst_1397_, 0);
    lean_inc_ref(v_toApplicative_1402_);
    v_toBind_1403_ = lean_ctor_get(v_inst_1397_, 1);
    lean_inc_n(v_toBind_1403_, 2);
    lean_dec_ref(v_inst_1397_);
    v_getEnv_1404_ = lean_ctor_get(v_inst_1399_, 0);
    lean_inc(v_getEnv_1404_);
    v_toFunctor_1405_ = lean_ctor_get(v_toApplicative_1402_, 0);
    lean_inc_ref(v_toFunctor_1405_);
    lean_dec_ref(v_toApplicative_1402_);
    v___f_1406_ = l_Lean_withEnv___redArg___closed__0;
    v___f_1407_ = lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1407_, 0, v_x_1401_);
    v___f_1408_ = lean_alloc_closure(
        l_Lean_withEnv___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1408_, 0, v_toFunctor_1405_);
    lean_closure_set(v___f_1408_, 1, v_inst_1399_);
    lean_closure_set(v___f_1408_, 2, v_env_1400_);
    lean_closure_set(v___f_1408_, 3, v_toBind_1403_);
    lean_closure_set(v___f_1408_, 4, v___f_1407_);
    lean_closure_set(v___f_1408_, 5, v_inst_1398_);
    lean_closure_set(v___f_1408_, 6, v___f_1406_);
    v___x_1409_ = lean_apply_4(
        v_toBind_1403_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1404_,
        v___f_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lean_withEnv(
    mut v_m_1410_: *mut LeanObject,
    mut v_00_u03b1_1411_: *mut LeanObject,
    mut v_inst_1412_: *mut LeanObject,
    mut v_inst_1413_: *mut LeanObject,
    mut v_inst_1414_: *mut LeanObject,
    mut v_env_1415_: *mut LeanObject,
    mut v_x_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_env_1418_: *mut LeanObject,
    mut v_declName_1419_: *mut LeanObject,
) -> u8 {
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = 0;
    v___x_1421_ = l_Lean_Environment_findAsync_x3f(v_env_1418_, v_declName_1419_, v___x_1420_);
    if lean_obj_tag(v___x_1421_) == 1 {
        let mut v_val_1422_: *mut LeanObject = core::ptr::null_mut();
        let mut v_kind_1423_: u8 = 0;
        v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
        lean_inc(v_val_1422_);
        lean_dec_ref_known(v___x_1421_, 1);
        v_kind_1423_ = lean_ctor_get_uint8(
            v_val_1422_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        lean_dec(v_val_1422_);
        if v_kind_1423_ == 5 {
            let mut v___x_1424_: u8 = 0;
            v___x_1424_ = 1;
            return v___x_1424_;
        } else {
            return v___x_1420_;
        }
    } else {
        lean_dec(v___x_1421_);
        return v___x_1420_;
    }
}
pub unsafe fn l_Lean_isInductiveCore___boxed(
    mut v_env_1425_: *mut LeanObject,
    mut v_declName_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_isInductiveCore(v_env_1425_, v_declName_1426_);
    v_r_1428_ = lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Lean_isInductive___redArg___lam__0(
    mut v_declName_1429_: *mut LeanObject,
    mut v_toPure_1430_: *mut LeanObject,
    mut v_____do__lift_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Lean_isInductiveCore(v_____do__lift_1431_, v_declName_1429_);
    v___x_1433_ = lean_box((v___x_1432_) as usize);
    v___x_1434_ = lean_apply_2(v_toPure_1430_, lean_box(0), v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Lean_isInductive___redArg(
    mut v_inst_1435_: *mut LeanObject,
    mut v_inst_1436_: *mut LeanObject,
    mut v_declName_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1438_ = lean_ctor_get(v_inst_1435_, 0);
    lean_inc_ref(v_toApplicative_1438_);
    v_toBind_1439_ = lean_ctor_get(v_inst_1435_, 1);
    lean_inc(v_toBind_1439_);
    lean_dec_ref(v_inst_1435_);
    v_getEnv_1440_ = lean_ctor_get(v_inst_1436_, 0);
    lean_inc(v_getEnv_1440_);
    lean_dec_ref(v_inst_1436_);
    v_toPure_1441_ = lean_ctor_get(v_toApplicative_1438_, 1);
    lean_inc(v_toPure_1441_);
    lean_dec_ref(v_toApplicative_1438_);
    v___f_1442_ = lean_alloc_closure(
        l_Lean_isInductive___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1442_, 0, v_declName_1437_);
    lean_closure_set(v___f_1442_, 1, v_toPure_1441_);
    v___x_1443_ = lean_apply_4(
        v_toBind_1439_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1440_,
        v___f_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l_Lean_isInductive(
    mut v_m_1444_: *mut LeanObject,
    mut v_inst_1445_: *mut LeanObject,
    mut v_inst_1446_: *mut LeanObject,
    mut v_declName_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_isInductive___redArg(v_inst_1445_, v_inst_1446_, v_declName_1447_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_isRecCore(
    mut v_env_1449_: *mut LeanObject,
    mut v_declName_1450_: *mut LeanObject,
) -> u8 {
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = 0;
    v___x_1452_ = l_Lean_Environment_findAsync_x3f(v_env_1449_, v_declName_1450_, v___x_1451_);
    if lean_obj_tag(v___x_1452_) == 1 {
        let mut v_val_1453_: *mut LeanObject = core::ptr::null_mut();
        let mut v_kind_1454_: u8 = 0;
        v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
        lean_inc(v_val_1453_);
        lean_dec_ref_known(v___x_1452_, 1);
        v_kind_1454_ = lean_ctor_get_uint8(
            v_val_1453_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        lean_dec(v_val_1453_);
        if v_kind_1454_ == 7 {
            let mut v___x_1455_: u8 = 0;
            v___x_1455_ = 1;
            return v___x_1455_;
        } else {
            return v___x_1451_;
        }
    } else {
        lean_dec(v___x_1452_);
        return v___x_1451_;
    }
}
pub unsafe fn l_Lean_isRecCore___boxed(
    mut v_env_1456_: *mut LeanObject,
    mut v_declName_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_isRecCore(v_env_1456_, v_declName_1457_);
    v_r_1459_ = lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Lean_isRec___redArg___lam__0(
    mut v_declName_1460_: *mut LeanObject,
    mut v_toPure_1461_: *mut LeanObject,
    mut v_____do__lift_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_isRecCore(v_____do__lift_1462_, v_declName_1460_);
    v___x_1464_ = lean_box((v___x_1463_) as usize);
    v___x_1465_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_isRec___redArg(
    mut v_inst_1466_: *mut LeanObject,
    mut v_inst_1467_: *mut LeanObject,
    mut v_declName_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1469_ = lean_ctor_get(v_inst_1466_, 0);
    lean_inc_ref(v_toApplicative_1469_);
    v_toBind_1470_ = lean_ctor_get(v_inst_1466_, 1);
    lean_inc(v_toBind_1470_);
    lean_dec_ref(v_inst_1466_);
    v_getEnv_1471_ = lean_ctor_get(v_inst_1467_, 0);
    lean_inc(v_getEnv_1471_);
    lean_dec_ref(v_inst_1467_);
    v_toPure_1472_ = lean_ctor_get(v_toApplicative_1469_, 1);
    lean_inc(v_toPure_1472_);
    lean_dec_ref(v_toApplicative_1469_);
    v___f_1473_ = lean_alloc_closure(
        l_Lean_isRec___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1473_, 0, v_declName_1468_);
    lean_closure_set(v___f_1473_, 1, v_toPure_1472_);
    v___x_1474_ = lean_apply_4(
        v_toBind_1470_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1471_,
        v___f_1473_,
    );
    return v___x_1474_;
}
pub unsafe fn l_Lean_isRec(
    mut v_m_1475_: *mut LeanObject,
    mut v_inst_1476_: *mut LeanObject,
    mut v_inst_1477_: *mut LeanObject,
    mut v_declName_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_isRec___redArg(v_inst_1476_, v_inst_1477_, v_declName_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_withoutModifyingEnv___redArg___lam__0(
    mut v_inst_1480_: *mut LeanObject,
    mut v_inst_1481_: *mut LeanObject,
    mut v_inst_1482_: *mut LeanObject,
    mut v_x_1483_: *mut LeanObject,
    mut v_____do__lift_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1487_: *mut LeanObject,
    mut v_inst_1488_: *mut LeanObject,
    mut v_inst_1489_: *mut LeanObject,
    mut v_x_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1491_ = lean_ctor_get(v_inst_1487_, 1);
    lean_inc(v_toBind_1491_);
    v_getEnv_1492_ = lean_ctor_get(v_inst_1488_, 0);
    lean_inc(v_getEnv_1492_);
    v___f_1493_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1493_, 0, v_inst_1487_);
    lean_closure_set(v___f_1493_, 1, v_inst_1489_);
    lean_closure_set(v___f_1493_, 2, v_inst_1488_);
    lean_closure_set(v___f_1493_, 3, v_x_1490_);
    v___x_1494_ = lean_apply_4(
        v_toBind_1491_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1492_,
        v___f_1493_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_withoutModifyingEnv(
    mut v_m_1495_: *mut LeanObject,
    mut v_inst_1496_: *mut LeanObject,
    mut v_inst_1497_: *mut LeanObject,
    mut v_inst_1498_: *mut LeanObject,
    mut v_00_u03b1_1499_: *mut LeanObject,
    mut v_x_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1501_ = lean_ctor_get(v_inst_1496_, 1);
    lean_inc(v_toBind_1501_);
    v_getEnv_1502_ = lean_ctor_get(v_inst_1497_, 0);
    lean_inc(v_getEnv_1502_);
    v___f_1503_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1503_, 0, v_inst_1496_);
    lean_closure_set(v___f_1503_, 1, v_inst_1498_);
    lean_closure_set(v___f_1503_, 2, v_inst_1497_);
    lean_closure_set(v___f_1503_, 3, v_x_1500_);
    v___x_1504_ = lean_apply_4(
        v_toBind_1501_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1502_,
        v___f_1503_,
    );
    return v___x_1504_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0(
    mut v_x_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1506_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1506_ = lean_ctor_get(v_x_1505_, 0);
    lean_inc(v_fst_1506_);
    return v_fst_1506_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(
    mut v_x_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(v_x_1507_);
    lean_dec_ref(v_x_1507_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__1(
    mut v_a_1509_: *mut LeanObject,
    mut v_toPure_1510_: *mut LeanObject,
    mut v_____do__lift_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1512_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1512_, 0, v_a_1509_);
    lean_ctor_set(v___x_1512_, 1, v_____do__lift_1511_);
    v___x_1513_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    v___x_1514_ = lean_apply_2(v_toPure_1510_, lean_box(0), v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__2(
    mut v_toPure_1515_: *mut LeanObject,
    mut v_toBind_1516_: *mut LeanObject,
    mut v_getEnv_1517_: *mut LeanObject,
    mut v_a_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___f_1519_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1519_, 0, v_a_1518_);
    lean_closure_set(v___f_1519_, 1, v_toPure_1515_);
    v___x_1520_ = lean_apply_4(
        v_toBind_1516_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1517_,
        v___f_1519_,
    );
    return v___x_1520_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__3(
    mut v_toPure_1521_: *mut LeanObject,
    mut v_e_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v_a_1523_ = lean_ctor_get(v_e_1522_, 0);
    lean_inc(v_a_1523_);
    lean_dec_ref(v_e_1522_);
    v___x_1524_ = lean_apply_2(v_toPure_1521_, lean_box(0), v_a_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4(
    mut v___x_1525_: *mut LeanObject,
    mut v_x_1526_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_1525_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(
    mut v___x_1527_: *mut LeanObject,
    mut v_x_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1529_: *mut LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(v___x_1527_, v_x_1528_);
    lean_dec(v_x_1528_);
    lean_dec(v___x_1527_);
    return v_res_1529_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg___lam__5(
    mut v_toFunctor_1530_: *mut LeanObject,
    mut v_toBind_1531_: *mut LeanObject,
    mut v_x_1532_: *mut LeanObject,
    mut v___f_1533_: *mut LeanObject,
    mut v_inst_1534_: *mut LeanObject,
    mut v_inst_1535_: *mut LeanObject,
    mut v___f_1536_: *mut LeanObject,
    mut v___f_1537_: *mut LeanObject,
    mut v_env_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v_map_1539_ = lean_ctor_get(v_toFunctor_1530_, 0);
    lean_inc(v_map_1539_);
    lean_dec_ref(v_toFunctor_1530_);
    lean_inc(v_toBind_1531_);
    v___x_1540_ = lean_apply_4(
        v_toBind_1531_,
        lean_box(0),
        lean_box(0),
        v_x_1532_,
        v___f_1533_,
    );
    v___x_1541_ = l_Lean_setEnv___redArg(v_inst_1534_, v_env_1538_);
    v___f_1542_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1542_, 0, v___x_1541_);
    v_y_1543_ = lean_apply_4(
        v_inst_1535_,
        lean_box(0),
        lean_box(0),
        v___x_1540_,
        v___f_1542_,
    );
    v___x_1544_ = lean_apply_4(
        v_map_1539_,
        lean_box(0),
        lean_box(0),
        v___f_1536_,
        v_y_1543_,
    );
    v___x_1545_ = lean_apply_4(
        v_toBind_1531_,
        lean_box(0),
        lean_box(0),
        v___x_1544_,
        v___f_1537_,
    );
    return v___x_1545_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27___redArg(
    mut v_inst_1547_: *mut LeanObject,
    mut v_inst_1548_: *mut LeanObject,
    mut v_inst_1549_: *mut LeanObject,
    mut v_x_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1551_ = lean_ctor_get(v_inst_1547_, 0);
    lean_inc_ref(v_toApplicative_1551_);
    v_toBind_1552_ = lean_ctor_get(v_inst_1547_, 1);
    lean_inc_n(v_toBind_1552_, 3);
    lean_dec_ref(v_inst_1547_);
    v_getEnv_1553_ = lean_ctor_get(v_inst_1548_, 0);
    lean_inc_n(v_getEnv_1553_, 2);
    v_toFunctor_1554_ = lean_ctor_get(v_toApplicative_1551_, 0);
    lean_inc_ref(v_toFunctor_1554_);
    v_toPure_1555_ = lean_ctor_get(v_toApplicative_1551_, 1);
    lean_inc_n(v_toPure_1555_, 2);
    lean_dec_ref(v_toApplicative_1551_);
    v___f_1556_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1557_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1557_, 0, v_toPure_1555_);
    lean_closure_set(v___f_1557_, 1, v_toBind_1552_);
    lean_closure_set(v___f_1557_, 2, v_getEnv_1553_);
    v___f_1558_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1558_, 0, v_toPure_1555_);
    v___f_1559_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1559_, 0, v_toFunctor_1554_);
    lean_closure_set(v___f_1559_, 1, v_toBind_1552_);
    lean_closure_set(v___f_1559_, 2, v_x_1550_);
    lean_closure_set(v___f_1559_, 3, v___f_1557_);
    lean_closure_set(v___f_1559_, 4, v_inst_1548_);
    lean_closure_set(v___f_1559_, 5, v_inst_1549_);
    lean_closure_set(v___f_1559_, 6, v___f_1556_);
    lean_closure_set(v___f_1559_, 7, v___f_1558_);
    v___x_1560_ = lean_apply_4(
        v_toBind_1552_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1553_,
        v___f_1559_,
    );
    return v___x_1560_;
}
pub unsafe fn l_Lean_withoutModifyingEnv_x27(
    mut v_m_1561_: *mut LeanObject,
    mut v_inst_1562_: *mut LeanObject,
    mut v_inst_1563_: *mut LeanObject,
    mut v_inst_1564_: *mut LeanObject,
    mut v_00_u03b1_1565_: *mut LeanObject,
    mut v_x_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1567_ = lean_ctor_get(v_inst_1562_, 0);
    lean_inc_ref(v_toApplicative_1567_);
    v_toBind_1568_ = lean_ctor_get(v_inst_1562_, 1);
    lean_inc_n(v_toBind_1568_, 3);
    lean_dec_ref(v_inst_1562_);
    v_getEnv_1569_ = lean_ctor_get(v_inst_1563_, 0);
    lean_inc_n(v_getEnv_1569_, 2);
    v_toFunctor_1570_ = lean_ctor_get(v_toApplicative_1567_, 0);
    lean_inc_ref(v_toFunctor_1570_);
    v_toPure_1571_ = lean_ctor_get(v_toApplicative_1567_, 1);
    lean_inc_n(v_toPure_1571_, 2);
    lean_dec_ref(v_toApplicative_1567_);
    v___f_1572_ = l_Lean_withoutModifyingEnv_x27___redArg___closed__0;
    v___f_1573_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1573_, 0, v_toPure_1571_);
    lean_closure_set(v___f_1573_, 1, v_toBind_1568_);
    lean_closure_set(v___f_1573_, 2, v_getEnv_1569_);
    v___f_1574_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1574_, 0, v_toPure_1571_);
    v___f_1575_ = lean_alloc_closure(
        l_Lean_withoutModifyingEnv_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1575_, 0, v_toFunctor_1570_);
    lean_closure_set(v___f_1575_, 1, v_toBind_1568_);
    lean_closure_set(v___f_1575_, 2, v_x_1566_);
    lean_closure_set(v___f_1575_, 3, v___f_1573_);
    lean_closure_set(v___f_1575_, 4, v_inst_1563_);
    lean_closure_set(v___f_1575_, 5, v_inst_1564_);
    lean_closure_set(v___f_1575_, 6, v___f_1572_);
    lean_closure_set(v___f_1575_, 7, v___f_1574_);
    v___x_1576_ = lean_apply_4(
        v_toBind_1568_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1569_,
        v___f_1575_,
    );
    return v___x_1576_;
}
pub unsafe fn l_Lean_matchConst___redArg___lam__0(
    mut v_declName_1577_: *mut LeanObject,
    mut v_failK_1578_: *mut LeanObject,
    mut v_k_1579_: *mut LeanObject,
    mut v_us_1580_: *mut LeanObject,
    mut v_____do__lift_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    v___x_1582_ = 0;
    v___x_1583_ = l_Lean_Environment_find_x3f(v_____do__lift_1581_, v_declName_1577_, v___x_1582_);
    if lean_obj_tag(v___x_1583_) == 0 {
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_us_1580_);
        lean_dec(v_k_1579_);
        v___x_1584_ = lean_box(0);
        v___x_1585_ = lean_apply_1(v_failK_1578_, v___x_1584_);
        return v___x_1585_;
    } else {
        let mut v_val_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_failK_1578_);
        v_val_1586_ = lean_ctor_get(v___x_1583_, 0);
        lean_inc(v_val_1586_);
        lean_dec_ref_known(v___x_1583_, 1);
        v___x_1587_ = lean_apply_2(v_k_1579_, v_val_1586_, v_us_1580_);
        return v___x_1587_;
    }
}
pub unsafe fn l_Lean_matchConst___redArg(
    mut v_inst_1588_: *mut LeanObject,
    mut v_inst_1589_: *mut LeanObject,
    mut v_e_1590_: *mut LeanObject,
    mut v_failK_1591_: *mut LeanObject,
    mut v_k_1592_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1590_) == 4 {
        let mut v_toBind_1593_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1594_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1595_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1593_ = lean_ctor_get(v_inst_1588_, 1);
        lean_inc(v_toBind_1593_);
        lean_dec_ref(v_inst_1588_);
        v_declName_1594_ = lean_ctor_get(v_e_1590_, 0);
        lean_inc(v_declName_1594_);
        v_us_1595_ = lean_ctor_get(v_e_1590_, 1);
        lean_inc(v_us_1595_);
        lean_dec_ref_known(v_e_1590_, 2);
        v_getEnv_1596_ = lean_ctor_get(v_inst_1589_, 0);
        lean_inc(v_getEnv_1596_);
        lean_dec_ref(v_inst_1589_);
        v___f_1597_ = lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1597_, 0, v_declName_1594_);
        lean_closure_set(v___f_1597_, 1, v_failK_1591_);
        lean_closure_set(v___f_1597_, 2, v_k_1592_);
        lean_closure_set(v___f_1597_, 3, v_us_1595_);
        v___x_1598_ = lean_apply_4(
            v_toBind_1593_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1596_,
            v___f_1597_,
        );
        return v___x_1598_;
    } else {
        let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1592_);
        lean_dec_ref(v_e_1590_);
        lean_dec_ref(v_inst_1589_);
        lean_dec_ref(v_inst_1588_);
        v___x_1599_ = lean_box(0);
        v___x_1600_ = lean_apply_1(v_failK_1591_, v___x_1599_);
        return v___x_1600_;
    }
}
pub unsafe fn l_Lean_matchConst(
    mut v_m_1601_: *mut LeanObject,
    mut v_00_u03b1_1602_: *mut LeanObject,
    mut v_inst_1603_: *mut LeanObject,
    mut v_inst_1604_: *mut LeanObject,
    mut v_e_1605_: *mut LeanObject,
    mut v_failK_1606_: *mut LeanObject,
    mut v_k_1607_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1605_) == 4 {
        let mut v_toBind_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1609_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1610_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1611_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1612_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1608_ = lean_ctor_get(v_inst_1603_, 1);
        lean_inc(v_toBind_1608_);
        lean_dec_ref(v_inst_1603_);
        v_declName_1609_ = lean_ctor_get(v_e_1605_, 0);
        lean_inc(v_declName_1609_);
        v_us_1610_ = lean_ctor_get(v_e_1605_, 1);
        lean_inc(v_us_1610_);
        lean_dec_ref_known(v_e_1605_, 2);
        v_getEnv_1611_ = lean_ctor_get(v_inst_1604_, 0);
        lean_inc(v_getEnv_1611_);
        lean_dec_ref(v_inst_1604_);
        v___f_1612_ = lean_alloc_closure(
            l_Lean_matchConst___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1612_, 0, v_declName_1609_);
        lean_closure_set(v___f_1612_, 1, v_failK_1606_);
        lean_closure_set(v___f_1612_, 2, v_k_1607_);
        lean_closure_set(v___f_1612_, 3, v_us_1610_);
        v___x_1613_ = lean_apply_4(
            v_toBind_1608_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1611_,
            v___f_1612_,
        );
        return v___x_1613_;
    } else {
        let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1607_);
        lean_dec_ref(v_e_1605_);
        lean_dec_ref(v_inst_1604_);
        lean_dec_ref(v_inst_1603_);
        v___x_1614_ = lean_box(0);
        v___x_1615_ = lean_apply_1(v_failK_1606_, v___x_1614_);
        return v___x_1615_;
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg___lam__0(
    mut v_declName_1616_: *mut LeanObject,
    mut v_failK_1617_: *mut LeanObject,
    mut v_k_1618_: *mut LeanObject,
    mut v_us_1619_: *mut LeanObject,
    mut v_____do__lift_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ = 0;
    v___x_1622_ = l_Lean_Environment_find_x3f(v_____do__lift_1620_, v_declName_1616_, v___x_1621_);
    if lean_obj_tag(v___x_1622_) == 0 {
        let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_us_1619_);
        lean_dec(v_k_1618_);
        v___x_1623_ = lean_box(0);
        v___x_1624_ = lean_apply_1(v_failK_1617_, v___x_1623_);
        return v___x_1624_;
    } else {
        let mut v_val_1625_: *mut LeanObject = core::ptr::null_mut();
        v_val_1625_ = lean_ctor_get(v___x_1622_, 0);
        lean_inc(v_val_1625_);
        lean_dec_ref_known(v___x_1622_, 1);
        if lean_obj_tag(v_val_1625_) == 5 {
            let mut v_val_1626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_failK_1617_);
            v_val_1626_ = lean_ctor_get(v_val_1625_, 0);
            lean_inc_ref(v_val_1626_);
            lean_dec_ref_known(v_val_1625_, 1);
            v___x_1627_ = lean_apply_2(v_k_1618_, v_val_1626_, v_us_1619_);
            return v___x_1627_;
        } else {
            let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_1625_);
            lean_dec(v_us_1619_);
            lean_dec(v_k_1618_);
            v___x_1628_ = lean_box(0);
            v___x_1629_ = lean_apply_1(v_failK_1617_, v___x_1628_);
            return v___x_1629_;
        }
    }
}
pub unsafe fn l_Lean_matchConstInduct___redArg(
    mut v_inst_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_e_1632_: *mut LeanObject,
    mut v_failK_1633_: *mut LeanObject,
    mut v_k_1634_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1632_) == 4 {
        let mut v_toBind_1635_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1636_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1635_ = lean_ctor_get(v_inst_1630_, 1);
        lean_inc(v_toBind_1635_);
        lean_dec_ref(v_inst_1630_);
        v_declName_1636_ = lean_ctor_get(v_e_1632_, 0);
        lean_inc(v_declName_1636_);
        v_us_1637_ = lean_ctor_get(v_e_1632_, 1);
        lean_inc(v_us_1637_);
        lean_dec_ref_known(v_e_1632_, 2);
        v_getEnv_1638_ = lean_ctor_get(v_inst_1631_, 0);
        lean_inc(v_getEnv_1638_);
        lean_dec_ref(v_inst_1631_);
        v___f_1639_ = lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1639_, 0, v_declName_1636_);
        lean_closure_set(v___f_1639_, 1, v_failK_1633_);
        lean_closure_set(v___f_1639_, 2, v_k_1634_);
        lean_closure_set(v___f_1639_, 3, v_us_1637_);
        v___x_1640_ = lean_apply_4(
            v_toBind_1635_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1638_,
            v___f_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1634_);
        lean_dec_ref(v_e_1632_);
        lean_dec_ref(v_inst_1631_);
        lean_dec_ref(v_inst_1630_);
        v___x_1641_ = lean_box(0);
        v___x_1642_ = lean_apply_1(v_failK_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l_Lean_matchConstInduct(
    mut v_m_1643_: *mut LeanObject,
    mut v_00_u03b1_1644_: *mut LeanObject,
    mut v_inst_1645_: *mut LeanObject,
    mut v_inst_1646_: *mut LeanObject,
    mut v_e_1647_: *mut LeanObject,
    mut v_failK_1648_: *mut LeanObject,
    mut v_k_1649_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1647_) == 4 {
        let mut v_toBind_1650_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1651_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1650_ = lean_ctor_get(v_inst_1645_, 1);
        lean_inc(v_toBind_1650_);
        lean_dec_ref(v_inst_1645_);
        v_declName_1651_ = lean_ctor_get(v_e_1647_, 0);
        lean_inc(v_declName_1651_);
        v_us_1652_ = lean_ctor_get(v_e_1647_, 1);
        lean_inc(v_us_1652_);
        lean_dec_ref_known(v_e_1647_, 2);
        v_getEnv_1653_ = lean_ctor_get(v_inst_1646_, 0);
        lean_inc(v_getEnv_1653_);
        lean_dec_ref(v_inst_1646_);
        v___f_1654_ = lean_alloc_closure(
            l_Lean_matchConstInduct___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1654_, 0, v_declName_1651_);
        lean_closure_set(v___f_1654_, 1, v_failK_1648_);
        lean_closure_set(v___f_1654_, 2, v_k_1649_);
        lean_closure_set(v___f_1654_, 3, v_us_1652_);
        v___x_1655_ = lean_apply_4(
            v_toBind_1650_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1653_,
            v___f_1654_,
        );
        return v___x_1655_;
    } else {
        let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1649_);
        lean_dec_ref(v_e_1647_);
        lean_dec_ref(v_inst_1646_);
        lean_dec_ref(v_inst_1645_);
        v___x_1656_ = lean_box(0);
        v___x_1657_ = lean_apply_1(v_failK_1648_, v___x_1656_);
        return v___x_1657_;
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg___lam__0(
    mut v_declName_1658_: *mut LeanObject,
    mut v_failK_1659_: *mut LeanObject,
    mut v_k_1660_: *mut LeanObject,
    mut v_us_1661_: *mut LeanObject,
    mut v_____do__lift_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = 0;
    v___x_1664_ = l_Lean_Environment_find_x3f(v_____do__lift_1662_, v_declName_1658_, v___x_1663_);
    if lean_obj_tag(v___x_1664_) == 0 {
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_us_1661_);
        lean_dec(v_k_1660_);
        v___x_1665_ = lean_box(0);
        v___x_1666_ = lean_apply_1(v_failK_1659_, v___x_1665_);
        return v___x_1666_;
    } else {
        let mut v_val_1667_: *mut LeanObject = core::ptr::null_mut();
        v_val_1667_ = lean_ctor_get(v___x_1664_, 0);
        lean_inc(v_val_1667_);
        lean_dec_ref_known(v___x_1664_, 1);
        if lean_obj_tag(v_val_1667_) == 6 {
            let mut v_val_1668_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_failK_1659_);
            v_val_1668_ = lean_ctor_get(v_val_1667_, 0);
            lean_inc_ref(v_val_1668_);
            lean_dec_ref_known(v_val_1667_, 1);
            v___x_1669_ = lean_apply_2(v_k_1660_, v_val_1668_, v_us_1661_);
            return v___x_1669_;
        } else {
            let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_1667_);
            lean_dec(v_us_1661_);
            lean_dec(v_k_1660_);
            v___x_1670_ = lean_box(0);
            v___x_1671_ = lean_apply_1(v_failK_1659_, v___x_1670_);
            return v___x_1671_;
        }
    }
}
pub unsafe fn l_Lean_matchConstCtor___redArg(
    mut v_inst_1672_: *mut LeanObject,
    mut v_inst_1673_: *mut LeanObject,
    mut v_e_1674_: *mut LeanObject,
    mut v_failK_1675_: *mut LeanObject,
    mut v_k_1676_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1674_) == 4 {
        let mut v_toBind_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1679_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1677_ = lean_ctor_get(v_inst_1672_, 1);
        lean_inc(v_toBind_1677_);
        lean_dec_ref(v_inst_1672_);
        v_declName_1678_ = lean_ctor_get(v_e_1674_, 0);
        lean_inc(v_declName_1678_);
        v_us_1679_ = lean_ctor_get(v_e_1674_, 1);
        lean_inc(v_us_1679_);
        lean_dec_ref_known(v_e_1674_, 2);
        v_getEnv_1680_ = lean_ctor_get(v_inst_1673_, 0);
        lean_inc(v_getEnv_1680_);
        lean_dec_ref(v_inst_1673_);
        v___f_1681_ = lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1681_, 0, v_declName_1678_);
        lean_closure_set(v___f_1681_, 1, v_failK_1675_);
        lean_closure_set(v___f_1681_, 2, v_k_1676_);
        lean_closure_set(v___f_1681_, 3, v_us_1679_);
        v___x_1682_ = lean_apply_4(
            v_toBind_1677_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1680_,
            v___f_1681_,
        );
        return v___x_1682_;
    } else {
        let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1676_);
        lean_dec_ref(v_e_1674_);
        lean_dec_ref(v_inst_1673_);
        lean_dec_ref(v_inst_1672_);
        v___x_1683_ = lean_box(0);
        v___x_1684_ = lean_apply_1(v_failK_1675_, v___x_1683_);
        return v___x_1684_;
    }
}
pub unsafe fn l_Lean_matchConstCtor(
    mut v_m_1685_: *mut LeanObject,
    mut v_00_u03b1_1686_: *mut LeanObject,
    mut v_inst_1687_: *mut LeanObject,
    mut v_inst_1688_: *mut LeanObject,
    mut v_e_1689_: *mut LeanObject,
    mut v_failK_1690_: *mut LeanObject,
    mut v_k_1691_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1689_) == 4 {
        let mut v_toBind_1692_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1692_ = lean_ctor_get(v_inst_1687_, 1);
        lean_inc(v_toBind_1692_);
        lean_dec_ref(v_inst_1687_);
        v_declName_1693_ = lean_ctor_get(v_e_1689_, 0);
        lean_inc(v_declName_1693_);
        v_us_1694_ = lean_ctor_get(v_e_1689_, 1);
        lean_inc(v_us_1694_);
        lean_dec_ref_known(v_e_1689_, 2);
        v_getEnv_1695_ = lean_ctor_get(v_inst_1688_, 0);
        lean_inc(v_getEnv_1695_);
        lean_dec_ref(v_inst_1688_);
        v___f_1696_ = lean_alloc_closure(
            l_Lean_matchConstCtor___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1696_, 0, v_declName_1693_);
        lean_closure_set(v___f_1696_, 1, v_failK_1690_);
        lean_closure_set(v___f_1696_, 2, v_k_1691_);
        lean_closure_set(v___f_1696_, 3, v_us_1694_);
        v___x_1697_ = lean_apply_4(
            v_toBind_1692_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1695_,
            v___f_1696_,
        );
        return v___x_1697_;
    } else {
        let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1691_);
        lean_dec_ref(v_e_1689_);
        lean_dec_ref(v_inst_1688_);
        lean_dec_ref(v_inst_1687_);
        v___x_1698_ = lean_box(0);
        v___x_1699_ = lean_apply_1(v_failK_1690_, v___x_1698_);
        return v___x_1699_;
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg___lam__0(
    mut v_declName_1700_: *mut LeanObject,
    mut v_failK_1701_: *mut LeanObject,
    mut v_k_1702_: *mut LeanObject,
    mut v_us_1703_: *mut LeanObject,
    mut v_____do__lift_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1705_ = 0;
    v___x_1706_ = l_Lean_Environment_find_x3f(v_____do__lift_1704_, v_declName_1700_, v___x_1705_);
    if lean_obj_tag(v___x_1706_) == 0 {
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_us_1703_);
        lean_dec(v_k_1702_);
        v___x_1707_ = lean_box(0);
        v___x_1708_ = lean_apply_1(v_failK_1701_, v___x_1707_);
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut LeanObject = core::ptr::null_mut();
        v_val_1709_ = lean_ctor_get(v___x_1706_, 0);
        lean_inc(v_val_1709_);
        lean_dec_ref_known(v___x_1706_, 1);
        if lean_obj_tag(v_val_1709_) == 7 {
            let mut v_val_1710_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_failK_1701_);
            v_val_1710_ = lean_ctor_get(v_val_1709_, 0);
            lean_inc_ref(v_val_1710_);
            lean_dec_ref_known(v_val_1709_, 1);
            v___x_1711_ = lean_apply_2(v_k_1702_, v_val_1710_, v_us_1703_);
            return v___x_1711_;
        } else {
            let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_1709_);
            lean_dec(v_us_1703_);
            lean_dec(v_k_1702_);
            v___x_1712_ = lean_box(0);
            v___x_1713_ = lean_apply_1(v_failK_1701_, v___x_1712_);
            return v___x_1713_;
        }
    }
}
pub unsafe fn l_Lean_matchConstRec___redArg(
    mut v_inst_1714_: *mut LeanObject,
    mut v_inst_1715_: *mut LeanObject,
    mut v_e_1716_: *mut LeanObject,
    mut v_failK_1717_: *mut LeanObject,
    mut v_k_1718_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1716_) == 4 {
        let mut v_toBind_1719_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1720_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1721_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1719_ = lean_ctor_get(v_inst_1714_, 1);
        lean_inc(v_toBind_1719_);
        lean_dec_ref(v_inst_1714_);
        v_declName_1720_ = lean_ctor_get(v_e_1716_, 0);
        lean_inc(v_declName_1720_);
        v_us_1721_ = lean_ctor_get(v_e_1716_, 1);
        lean_inc(v_us_1721_);
        lean_dec_ref_known(v_e_1716_, 2);
        v_getEnv_1722_ = lean_ctor_get(v_inst_1715_, 0);
        lean_inc(v_getEnv_1722_);
        lean_dec_ref(v_inst_1715_);
        v___f_1723_ = lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1723_, 0, v_declName_1720_);
        lean_closure_set(v___f_1723_, 1, v_failK_1717_);
        lean_closure_set(v___f_1723_, 2, v_k_1718_);
        lean_closure_set(v___f_1723_, 3, v_us_1721_);
        v___x_1724_ = lean_apply_4(
            v_toBind_1719_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1722_,
            v___f_1723_,
        );
        return v___x_1724_;
    } else {
        let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1718_);
        lean_dec_ref(v_e_1716_);
        lean_dec_ref(v_inst_1715_);
        lean_dec_ref(v_inst_1714_);
        v___x_1725_ = lean_box(0);
        v___x_1726_ = lean_apply_1(v_failK_1717_, v___x_1725_);
        return v___x_1726_;
    }
}
pub unsafe fn l_Lean_matchConstRec(
    mut v_m_1727_: *mut LeanObject,
    mut v_00_u03b1_1728_: *mut LeanObject,
    mut v_inst_1729_: *mut LeanObject,
    mut v_inst_1730_: *mut LeanObject,
    mut v_e_1731_: *mut LeanObject,
    mut v_failK_1732_: *mut LeanObject,
    mut v_k_1733_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_1731_) == 4 {
        let mut v_toBind_1734_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_1736_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1734_ = lean_ctor_get(v_inst_1729_, 1);
        lean_inc(v_toBind_1734_);
        lean_dec_ref(v_inst_1729_);
        v_declName_1735_ = lean_ctor_get(v_e_1731_, 0);
        lean_inc(v_declName_1735_);
        v_us_1736_ = lean_ctor_get(v_e_1731_, 1);
        lean_inc(v_us_1736_);
        lean_dec_ref_known(v_e_1731_, 2);
        v_getEnv_1737_ = lean_ctor_get(v_inst_1730_, 0);
        lean_inc(v_getEnv_1737_);
        lean_dec_ref(v_inst_1730_);
        v___f_1738_ = lean_alloc_closure(
            l_Lean_matchConstRec___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1738_, 0, v_declName_1735_);
        lean_closure_set(v___f_1738_, 1, v_failK_1732_);
        lean_closure_set(v___f_1738_, 2, v_k_1733_);
        lean_closure_set(v___f_1738_, 3, v_us_1736_);
        v___x_1739_ = lean_apply_4(
            v_toBind_1734_,
            lean_box(0),
            lean_box(0),
            v_getEnv_1737_,
            v___f_1738_,
        );
        return v___x_1739_;
    } else {
        let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1733_);
        lean_dec_ref(v_e_1731_);
        lean_dec_ref(v_inst_1730_);
        lean_dec_ref(v_inst_1729_);
        v___x_1740_ = lean_box(0);
        v___x_1741_ = lean_apply_1(v_failK_1732_, v___x_1740_);
        return v___x_1741_;
    }
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0(
    mut v_constName_1742_: *mut LeanObject,
    mut v_skipRealize_1743_: u8,
    mut v_toPure_1744_: *mut LeanObject,
    mut v_____do__lift_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ =
        l_Lean_Environment_contains(v_____do__lift_1745_, v_constName_1742_, v_skipRealize_1743_);
    v___x_1747_ = lean_box((v___x_1746_) as usize);
    v___x_1748_ = lean_apply_2(v_toPure_1744_, lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_hasConst___redArg___lam__0___boxed(
    mut v_constName_1749_: *mut LeanObject,
    mut v_skipRealize_1750_: *mut LeanObject,
    mut v_toPure_1751_: *mut LeanObject,
    mut v_____do__lift_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1753_: u8 = 0;
    let mut v_res_1754_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1753_ = (lean_unbox(v_skipRealize_1750_) as u8);
    v_res_1754_ = l_Lean_hasConst___redArg___lam__0(
        v_constName_1749_,
        v_skipRealize_boxed_1753_,
        v_toPure_1751_,
        v_____do__lift_1752_,
    );
    return v_res_1754_;
}
pub unsafe fn l_Lean_hasConst___redArg(
    mut v_inst_1755_: *mut LeanObject,
    mut v_inst_1756_: *mut LeanObject,
    mut v_constName_1757_: *mut LeanObject,
    mut v_skipRealize_1758_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1759_ = lean_ctor_get(v_inst_1755_, 0);
    lean_inc_ref(v_toApplicative_1759_);
    v_toBind_1760_ = lean_ctor_get(v_inst_1755_, 1);
    lean_inc(v_toBind_1760_);
    lean_dec_ref(v_inst_1755_);
    v_getEnv_1761_ = lean_ctor_get(v_inst_1756_, 0);
    lean_inc(v_getEnv_1761_);
    lean_dec_ref(v_inst_1756_);
    v_toPure_1762_ = lean_ctor_get(v_toApplicative_1759_, 1);
    lean_inc(v_toPure_1762_);
    lean_dec_ref(v_toApplicative_1759_);
    v___x_1763_ = lean_box((v_skipRealize_1758_) as usize);
    v___f_1764_ = lean_alloc_closure(
        l_Lean_hasConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1764_, 0, v_constName_1757_);
    lean_closure_set(v___f_1764_, 1, v___x_1763_);
    lean_closure_set(v___f_1764_, 2, v_toPure_1762_);
    v___x_1765_ = lean_apply_4(
        v_toBind_1760_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1761_,
        v___f_1764_,
    );
    return v___x_1765_;
}
pub unsafe fn l_Lean_hasConst___redArg___boxed(
    mut v_inst_1766_: *mut LeanObject,
    mut v_inst_1767_: *mut LeanObject,
    mut v_constName_1768_: *mut LeanObject,
    mut v_skipRealize_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1770_: u8 = 0;
    let mut v_res_1771_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1770_ = (lean_unbox(v_skipRealize_1769_) as u8);
    v_res_1771_ = l_Lean_hasConst___redArg(
        v_inst_1766_,
        v_inst_1767_,
        v_constName_1768_,
        v_skipRealize_boxed_1770_,
    );
    return v_res_1771_;
}
pub unsafe fn l_Lean_hasConst(
    mut v_m_1772_: *mut LeanObject,
    mut v_inst_1773_: *mut LeanObject,
    mut v_inst_1774_: *mut LeanObject,
    mut v_constName_1775_: *mut LeanObject,
    mut v_skipRealize_1776_: u8,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_hasConst___redArg(
        v_inst_1773_,
        v_inst_1774_,
        v_constName_1775_,
        v_skipRealize_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_hasConst___boxed(
    mut v_m_1778_: *mut LeanObject,
    mut v_inst_1779_: *mut LeanObject,
    mut v_inst_1780_: *mut LeanObject,
    mut v_constName_1781_: *mut LeanObject,
    mut v_skipRealize_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1783_: u8 = 0;
    let mut v_res_1784_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1783_ = (lean_unbox(v_skipRealize_1782_) as u8);
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
    mut v_constName_1785_: *mut LeanObject,
    mut v_inst_1786_: *mut LeanObject,
    mut v_inst_1787_: *mut LeanObject,
    mut v_inst_1788_: *mut LeanObject,
    mut v_toPure_1789_: *mut LeanObject,
    mut v_____do__lift_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    v___x_1791_ = 0;
    lean_inc(v_constName_1785_);
    v___x_1792_ = l_Lean_Environment_find_x3f(v_____do__lift_1790_, v_constName_1785_, v___x_1791_);
    if lean_obj_tag(v___x_1792_) == 0 {
        let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1789_);
        v___x_1793_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1786_,
            v_inst_1787_,
            v_inst_1788_,
            v_constName_1785_,
        );
        return v___x_1793_;
    } else {
        let mut v_val_1794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1788_);
        lean_dec_ref(v_inst_1787_);
        lean_dec_ref(v_inst_1786_);
        lean_dec(v_constName_1785_);
        v_val_1794_ = lean_ctor_get(v___x_1792_, 0);
        lean_inc(v_val_1794_);
        lean_dec_ref_known(v___x_1792_, 1);
        v___x_1795_ = lean_apply_2(v_toPure_1789_, lean_box(0), v_val_1794_);
        return v___x_1795_;
    }
}
pub unsafe fn l_Lean_getConstInfo___redArg(
    mut v_inst_1796_: *mut LeanObject,
    mut v_inst_1797_: *mut LeanObject,
    mut v_inst_1798_: *mut LeanObject,
    mut v_constName_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1800_ = lean_ctor_get(v_inst_1796_, 0);
    v_toBind_1801_ = lean_ctor_get(v_inst_1796_, 1);
    lean_inc(v_toBind_1801_);
    v_getEnv_1802_ = lean_ctor_get(v_inst_1797_, 0);
    lean_inc(v_getEnv_1802_);
    v_toPure_1803_ = lean_ctor_get(v_toApplicative_1800_, 1);
    lean_inc(v_toPure_1803_);
    v___f_1804_ = lean_alloc_closure(
        l_Lean_getConstInfo___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1804_, 0, v_constName_1799_);
    lean_closure_set(v___f_1804_, 1, v_inst_1796_);
    lean_closure_set(v___f_1804_, 2, v_inst_1797_);
    lean_closure_set(v___f_1804_, 3, v_inst_1798_);
    lean_closure_set(v___f_1804_, 4, v_toPure_1803_);
    v___x_1805_ = lean_apply_4(
        v_toBind_1801_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1802_,
        v___f_1804_,
    );
    return v___x_1805_;
}
pub unsafe fn l_Lean_getConstInfo(
    mut v_m_1806_: *mut LeanObject,
    mut v_inst_1807_: *mut LeanObject,
    mut v_inst_1808_: *mut LeanObject,
    mut v_inst_1809_: *mut LeanObject,
    mut v_constName_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    v___x_1811_ =
        l_Lean_getConstInfo___redArg(v_inst_1807_, v_inst_1808_, v_inst_1809_, v_constName_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Lean_getConstVal___redArg___lam__0(
    mut v_constName_1812_: *mut LeanObject,
    mut v_inst_1813_: *mut LeanObject,
    mut v_inst_1814_: *mut LeanObject,
    mut v_inst_1815_: *mut LeanObject,
    mut v_toPure_1816_: *mut LeanObject,
    mut v_____do__lift_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818_ = 0;
    lean_inc(v_constName_1812_);
    v___x_1819_ =
        l_Lean_Environment_findConstVal_x3f(v_____do__lift_1817_, v_constName_1812_, v___x_1818_);
    if lean_obj_tag(v___x_1819_) == 0 {
        let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1816_);
        v___x_1820_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1813_,
            v_inst_1814_,
            v_inst_1815_,
            v_constName_1812_,
        );
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1815_);
        lean_dec_ref(v_inst_1814_);
        lean_dec_ref(v_inst_1813_);
        lean_dec(v_constName_1812_);
        v_val_1821_ = lean_ctor_get(v___x_1819_, 0);
        lean_inc(v_val_1821_);
        lean_dec_ref_known(v___x_1819_, 1);
        v___x_1822_ = lean_apply_2(v_toPure_1816_, lean_box(0), v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l_Lean_getConstVal___redArg(
    mut v_inst_1823_: *mut LeanObject,
    mut v_inst_1824_: *mut LeanObject,
    mut v_inst_1825_: *mut LeanObject,
    mut v_constName_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1827_ = lean_ctor_get(v_inst_1823_, 0);
    v_toBind_1828_ = lean_ctor_get(v_inst_1823_, 1);
    lean_inc(v_toBind_1828_);
    v_getEnv_1829_ = lean_ctor_get(v_inst_1824_, 0);
    lean_inc(v_getEnv_1829_);
    v_toPure_1830_ = lean_ctor_get(v_toApplicative_1827_, 1);
    lean_inc(v_toPure_1830_);
    v___f_1831_ = lean_alloc_closure(
        l_Lean_getConstVal___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1831_, 0, v_constName_1826_);
    lean_closure_set(v___f_1831_, 1, v_inst_1823_);
    lean_closure_set(v___f_1831_, 2, v_inst_1824_);
    lean_closure_set(v___f_1831_, 3, v_inst_1825_);
    lean_closure_set(v___f_1831_, 4, v_toPure_1830_);
    v___x_1832_ = lean_apply_4(
        v_toBind_1828_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1829_,
        v___f_1831_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Lean_getConstVal(
    mut v_m_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
    mut v_inst_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
    mut v_constName_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ =
        l_Lean_getConstVal___redArg(v_inst_1834_, v_inst_1835_, v_inst_1836_, v_constName_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0(
    mut v_constName_1839_: *mut LeanObject,
    mut v_skipRealize_1840_: u8,
    mut v_inst_1841_: *mut LeanObject,
    mut v_inst_1842_: *mut LeanObject,
    mut v_inst_1843_: *mut LeanObject,
    mut v_toPure_1844_: *mut LeanObject,
    mut v_____do__lift_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_constName_1839_);
    v___x_1846_ = l_Lean_Environment_findAsync_x3f(
        v_____do__lift_1845_,
        v_constName_1839_,
        v_skipRealize_1840_,
    );
    if lean_obj_tag(v___x_1846_) == 0 {
        let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1844_);
        v___x_1847_ = l_Lean_throwUnknownConstant___redArg(
            v_inst_1841_,
            v_inst_1842_,
            v_inst_1843_,
            v_constName_1839_,
        );
        return v___x_1847_;
    } else {
        let mut v_val_1848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1843_);
        lean_dec_ref(v_inst_1842_);
        lean_dec_ref(v_inst_1841_);
        lean_dec(v_constName_1839_);
        v_val_1848_ = lean_ctor_get(v___x_1846_, 0);
        lean_inc(v_val_1848_);
        lean_dec_ref_known(v___x_1846_, 1);
        v___x_1849_ = lean_apply_2(v_toPure_1844_, lean_box(0), v_val_1848_);
        return v___x_1849_;
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(
    mut v_constName_1850_: *mut LeanObject,
    mut v_skipRealize_1851_: *mut LeanObject,
    mut v_inst_1852_: *mut LeanObject,
    mut v_inst_1853_: *mut LeanObject,
    mut v_inst_1854_: *mut LeanObject,
    mut v_toPure_1855_: *mut LeanObject,
    mut v_____do__lift_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1857_: u8 = 0;
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1857_ = (lean_unbox(v_skipRealize_1851_) as u8);
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
    mut v_inst_1859_: *mut LeanObject,
    mut v_inst_1860_: *mut LeanObject,
    mut v_inst_1861_: *mut LeanObject,
    mut v_constName_1862_: *mut LeanObject,
    mut v_skipRealize_1863_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = lean_ctor_get(v_inst_1859_, 0);
    v_toBind_1865_ = lean_ctor_get(v_inst_1859_, 1);
    lean_inc(v_toBind_1865_);
    v_getEnv_1866_ = lean_ctor_get(v_inst_1860_, 0);
    lean_inc(v_getEnv_1866_);
    v_toPure_1867_ = lean_ctor_get(v_toApplicative_1864_, 1);
    lean_inc(v_toPure_1867_);
    v___x_1868_ = lean_box((v_skipRealize_1863_) as usize);
    v___f_1869_ = lean_alloc_closure(
        l_Lean_getAsyncConstInfo___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1869_, 0, v_constName_1862_);
    lean_closure_set(v___f_1869_, 1, v___x_1868_);
    lean_closure_set(v___f_1869_, 2, v_inst_1859_);
    lean_closure_set(v___f_1869_, 3, v_inst_1860_);
    lean_closure_set(v___f_1869_, 4, v_inst_1861_);
    lean_closure_set(v___f_1869_, 5, v_toPure_1867_);
    v___x_1870_ = lean_apply_4(
        v_toBind_1865_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1866_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___redArg___boxed(
    mut v_inst_1871_: *mut LeanObject,
    mut v_inst_1872_: *mut LeanObject,
    mut v_inst_1873_: *mut LeanObject,
    mut v_constName_1874_: *mut LeanObject,
    mut v_skipRealize_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1876_: u8 = 0;
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1876_ = (lean_unbox(v_skipRealize_1875_) as u8);
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
    mut v_m_1878_: *mut LeanObject,
    mut v_inst_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_inst_1881_: *mut LeanObject,
    mut v_constName_1882_: *mut LeanObject,
    mut v_skipRealize_1883_: u8,
) -> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_inst_1887_: *mut LeanObject,
    mut v_inst_1888_: *mut LeanObject,
    mut v_constName_1889_: *mut LeanObject,
    mut v_skipRealize_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1891_: u8 = 0;
    let mut v_res_1892_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1891_ = (lean_unbox(v_skipRealize_1890_) as u8);
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
    mut v_msg_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    v___x_1894_ = lean_box(0);
    v___x_1895_ = lean_panic_fn_borrowed(v___x_1894_, v_msg_1893_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lean_isInductiveCore_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    v___x_1899_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1900_ = lean_unsigned_to_nat(11);
    v___x_1901_ = lean_unsigned_to_nat(105);
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
    mut v_env_1905_: *mut LeanObject,
    mut v_declName_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v_kind_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1907_ = 0;
                v___x_1908_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1905_, v_declName_1906_, v___x_1907_);
                if lean_obj_tag(v___x_1908_) == 1 {
                    v_val_1909_ = lean_ctor_get(v___x_1908_, 0);
                    v_isSharedCheck_1922_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v___x_1911_ = v___x_1908_;
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1909_);
                        lean_dec(v___x_1908_);
                        v___x_1911_ = lean_box(0);
                        v_isShared_1912_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1908_);
                    v___x_1923_ = lean_box(0);
                    return v___x_1923_;
                }
            }
            1 => {
                v_kind_1913_ = lean_ctor_get_uint8(
                    v_val_1909_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_kind_1913_ == 5 {
                    v___x_1914_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1909_);
                    if lean_obj_tag(v___x_1914_) == 5 {
                        v_val_1915_ = lean_ctor_get(v___x_1914_, 0);
                        lean_inc_ref(v_val_1915_);
                        lean_dec_ref_known(v___x_1914_, 1);
                        if v_isShared_1912_ == 0 {
                            lean_ctor_set(v___x_1911_, 0, v_val_1915_);
                            v___x_1917_ = v___x_1911_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
                            v___x_1917_ = v_reuseFailAlloc_1918_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1914_);
                        lean_del_object(v___x_1911_);
                        v___x_1919_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_isInductiveCore_x3f___closed__3_once),
                            _init_l_Lean_isInductiveCore_x3f___closed__3,
                        );
                        v___x_1920_ =
                            l_panic___at___00Lean_isInductiveCore_x3f_spec__0(v___x_1919_);
                        return v___x_1920_;
                    }
                } else {
                    lean_del_object(v___x_1911_);
                    lean_dec(v_val_1909_);
                    v___x_1921_ = lean_box(0);
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
    mut v_declName_1924_: *mut LeanObject,
    mut v_toPure_1925_: *mut LeanObject,
    mut v_____do__lift_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_isInductiveCore_x3f(v_____do__lift_1926_, v_declName_1924_);
    v___x_1928_ = lean_apply_2(v_toPure_1925_, lean_box(0), v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lean_isInductive_x3f___redArg(
    mut v_inst_1929_: *mut LeanObject,
    mut v_inst_1930_: *mut LeanObject,
    mut v_declName_1931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1932_ = lean_ctor_get(v_inst_1929_, 0);
    lean_inc_ref(v_toApplicative_1932_);
    v_toBind_1933_ = lean_ctor_get(v_inst_1929_, 1);
    lean_inc(v_toBind_1933_);
    lean_dec_ref(v_inst_1929_);
    v_getEnv_1934_ = lean_ctor_get(v_inst_1930_, 0);
    lean_inc(v_getEnv_1934_);
    lean_dec_ref(v_inst_1930_);
    v_toPure_1935_ = lean_ctor_get(v_toApplicative_1932_, 1);
    lean_inc(v_toPure_1935_);
    lean_dec_ref(v_toApplicative_1932_);
    v___f_1936_ = lean_alloc_closure(
        l_Lean_isInductive_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1936_, 0, v_declName_1931_);
    lean_closure_set(v___f_1936_, 1, v_toPure_1935_);
    v___x_1937_ = lean_apply_4(
        v_toBind_1933_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1934_,
        v___f_1936_,
    );
    return v___x_1937_;
}
pub unsafe fn l_Lean_isInductive_x3f(
    mut v_m_1938_: *mut LeanObject,
    mut v_inst_1939_: *mut LeanObject,
    mut v_inst_1940_: *mut LeanObject,
    mut v_declName_1941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_isInductive_x3f___redArg(v_inst_1939_, v_inst_1940_, v_declName_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1945_ = lean_unsigned_to_nat(11);
    v___x_1946_ = lean_unsigned_to_nat(115);
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
    mut v_toPure_1950_: *mut LeanObject,
    mut v_constName_1951_: *mut LeanObject,
    mut v___x_1952_: *mut LeanObject,
    mut v_____do__lift_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v_kind_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1958_) == 1 {
                    v_val_1959_ = lean_ctor_get(v___x_1958_, 0);
                    v_isSharedCheck_1972_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_1972_ == 0 {
                        v___x_1961_ = v___x_1958_;
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1959_);
                        lean_dec(v___x_1958_);
                        v___x_1961_ = lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1958_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = lean_box(0);
                v___x_1956_ = lean_apply_2(v_toPure_1950_, lean_box(0), v___x_1955_);
                return v___x_1956_;
            }
            2 => {
                v_kind_1963_ = lean_ctor_get_uint8(
                    v_val_1959_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_kind_1963_ == 0 {
                    v___x_1964_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1959_);
                    if lean_obj_tag(v___x_1964_) == 1 {
                        v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
                        lean_inc_ref(v_val_1965_);
                        lean_dec_ref_known(v___x_1964_, 1);
                        if v_isShared_1962_ == 0 {
                            lean_ctor_set(v___x_1961_, 0, v_val_1965_);
                            v___x_1967_ = v___x_1961_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_val_1965_);
                            v___x_1967_ = v_reuseFailAlloc_1969_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1964_);
                        lean_del_object(v___x_1961_);
                        lean_dec(v_toPure_1950_);
                        v___x_1970_ = lean_obj_once(
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
                    lean_del_object(v___x_1961_);
                    lean_dec(v_val_1959_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1968_ = lean_apply_2(v_toPure_1950_, lean_box(0), v___x_1967_);
                return v___x_1968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isDefn_x3f___redArg___lam__0___boxed(
    mut v_toPure_1973_: *mut LeanObject,
    mut v_constName_1974_: *mut LeanObject,
    mut v___x_1975_: *mut LeanObject,
    mut v_____do__lift_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_isDefn_x3f___redArg___lam__0(
        v_toPure_1973_,
        v_constName_1974_,
        v___x_1975_,
        v_____do__lift_1976_,
    );
    lean_dec(v___x_1975_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_isDefn_x3f___redArg(
    mut v_inst_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
    mut v_constName_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1981_ = lean_ctor_get(v_inst_1978_, 0);
    v_toBind_1982_ = lean_ctor_get(v_inst_1978_, 1);
    lean_inc(v_toBind_1982_);
    v_getEnv_1983_ = lean_ctor_get(v_inst_1979_, 0);
    lean_inc(v_getEnv_1983_);
    lean_dec_ref(v_inst_1979_);
    v_toPure_1984_ = lean_ctor_get(v_toApplicative_1981_, 1);
    lean_inc(v_toPure_1984_);
    v___x_1985_ = lean_box(0);
    v___x_1986_ = l_instInhabitedOfMonad___redArg(v_inst_1978_, v___x_1985_);
    v___f_1987_ = lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1987_, 0, v_toPure_1984_);
    lean_closure_set(v___f_1987_, 1, v_constName_1980_);
    lean_closure_set(v___f_1987_, 2, v___x_1986_);
    v___x_1988_ = lean_apply_4(
        v_toBind_1982_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1983_,
        v___f_1987_,
    );
    return v___x_1988_;
}
pub unsafe fn l_Lean_isDefn_x3f(
    mut v_m_1989_: *mut LeanObject,
    mut v_inst_1990_: *mut LeanObject,
    mut v_inst_1991_: *mut LeanObject,
    mut v_constName_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1993_ = l_Lean_isDefn_x3f___redArg(v_inst_1990_, v_inst_1991_, v_constName_1992_);
    return v___x_1993_;
}
pub unsafe fn _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_1996_ = lean_unsigned_to_nat(11);
    v___x_1997_ = lean_unsigned_to_nat(122);
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
    mut v_toPure_2001_: *mut LeanObject,
    mut v_constName_2002_: *mut LeanObject,
    mut v___x_2003_: *mut LeanObject,
    mut v_____do__lift_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v_kind_2014_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2009_) == 1 {
                    v_val_2010_ = lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2023_ = (!lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2010_);
                        lean_dec(v___x_2009_);
                        v___x_2012_ = lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2023_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2009_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2006_ = lean_box(0);
                v___x_2007_ = lean_apply_2(v_toPure_2001_, lean_box(0), v___x_2006_);
                return v___x_2007_;
            }
            2 => {
                v_kind_2014_ = lean_ctor_get_uint8(
                    v_val_2010_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_kind_2014_ == 6 {
                    v___x_2015_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2010_);
                    if lean_obj_tag(v___x_2015_) == 6 {
                        v_val_2016_ = lean_ctor_get(v___x_2015_, 0);
                        lean_inc_ref(v_val_2016_);
                        lean_dec_ref_known(v___x_2015_, 1);
                        if v_isShared_2013_ == 0 {
                            lean_ctor_set(v___x_2012_, 0, v_val_2016_);
                            v___x_2018_ = v___x_2012_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_val_2016_);
                            v___x_2018_ = v_reuseFailAlloc_2020_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2015_);
                        lean_del_object(v___x_2012_);
                        lean_dec(v_toPure_2001_);
                        v___x_2021_ = lean_obj_once(
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
                    lean_del_object(v___x_2012_);
                    lean_dec(v_val_2010_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2019_ = lean_apply_2(v_toPure_2001_, lean_box(0), v___x_2018_);
                return v___x_2019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isCtor_x3f___redArg___lam__0___boxed(
    mut v_toPure_2024_: *mut LeanObject,
    mut v_constName_2025_: *mut LeanObject,
    mut v___x_2026_: *mut LeanObject,
    mut v_____do__lift_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2028_: *mut LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lean_isCtor_x3f___redArg___lam__0(
        v_toPure_2024_,
        v_constName_2025_,
        v___x_2026_,
        v_____do__lift_2027_,
    );
    lean_dec(v___x_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Lean_isCtor_x3f___redArg(
    mut v_inst_2029_: *mut LeanObject,
    mut v_inst_2030_: *mut LeanObject,
    mut v_constName_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2032_ = lean_ctor_get(v_inst_2029_, 0);
    v_toBind_2033_ = lean_ctor_get(v_inst_2029_, 1);
    lean_inc(v_toBind_2033_);
    v_getEnv_2034_ = lean_ctor_get(v_inst_2030_, 0);
    lean_inc(v_getEnv_2034_);
    lean_dec_ref(v_inst_2030_);
    v_toPure_2035_ = lean_ctor_get(v_toApplicative_2032_, 1);
    lean_inc(v_toPure_2035_);
    v___x_2036_ = lean_box(0);
    v___x_2037_ = l_instInhabitedOfMonad___redArg(v_inst_2029_, v___x_2036_);
    v___f_2038_ = lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2038_, 0, v_toPure_2035_);
    lean_closure_set(v___f_2038_, 1, v_constName_2031_);
    lean_closure_set(v___f_2038_, 2, v___x_2037_);
    v___x_2039_ = lean_apply_4(
        v_toBind_2033_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2034_,
        v___f_2038_,
    );
    return v___x_2039_;
}
pub unsafe fn l_Lean_isCtor_x3f(
    mut v_m_2040_: *mut LeanObject,
    mut v_inst_2041_: *mut LeanObject,
    mut v_inst_2042_: *mut LeanObject,
    mut v_constName_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Lean_isCtor_x3f___redArg(v_inst_2041_, v_inst_2042_, v_constName_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_isInductiveCore_x3f___closed__2;
    v___x_2047_ = lean_unsigned_to_nat(11);
    v___x_2048_ = lean_unsigned_to_nat(129);
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
    mut v_toPure_2052_: *mut LeanObject,
    mut v_constName_2053_: *mut LeanObject,
    mut v___x_2054_: *mut LeanObject,
    mut v_____do__lift_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_kind_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2060_) == 1 {
                    v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2060_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2063_ = v___x_2060_;
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2061_);
                        lean_dec(v___x_2060_);
                        v___x_2063_ = lean_box(0);
                        v_isShared_2064_ = v_isSharedCheck_2074_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2060_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2057_ = lean_box(0);
                v___x_2058_ = lean_apply_2(v_toPure_2052_, lean_box(0), v___x_2057_);
                return v___x_2058_;
            }
            2 => {
                v_kind_2065_ = lean_ctor_get_uint8(
                    v_val_2061_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_kind_2065_ == 7 {
                    v___x_2066_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2061_);
                    if lean_obj_tag(v___x_2066_) == 7 {
                        v_val_2067_ = lean_ctor_get(v___x_2066_, 0);
                        lean_inc_ref(v_val_2067_);
                        lean_dec_ref_known(v___x_2066_, 1);
                        if v_isShared_2064_ == 0 {
                            lean_ctor_set(v___x_2063_, 0, v_val_2067_);
                            v___x_2069_ = v___x_2063_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2067_);
                            v___x_2069_ = v_reuseFailAlloc_2071_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2066_);
                        lean_del_object(v___x_2063_);
                        lean_dec(v_toPure_2052_);
                        v___x_2072_ = lean_obj_once(
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
                    lean_del_object(v___x_2063_);
                    lean_dec(v_val_2061_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2070_ = lean_apply_2(v_toPure_2052_, lean_box(0), v___x_2069_);
                return v___x_2070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isRec_x3f___redArg___lam__0___boxed(
    mut v_toPure_2075_: *mut LeanObject,
    mut v_constName_2076_: *mut LeanObject,
    mut v___x_2077_: *mut LeanObject,
    mut v_____do__lift_2078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2079_: *mut LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_isRec_x3f___redArg___lam__0(
        v_toPure_2075_,
        v_constName_2076_,
        v___x_2077_,
        v_____do__lift_2078_,
    );
    lean_dec(v___x_2077_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_isRec_x3f___redArg(
    mut v_inst_2080_: *mut LeanObject,
    mut v_inst_2081_: *mut LeanObject,
    mut v_constName_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2083_ = lean_ctor_get(v_inst_2080_, 0);
    v_toBind_2084_ = lean_ctor_get(v_inst_2080_, 1);
    lean_inc(v_toBind_2084_);
    v_getEnv_2085_ = lean_ctor_get(v_inst_2081_, 0);
    lean_inc(v_getEnv_2085_);
    lean_dec_ref(v_inst_2081_);
    v_toPure_2086_ = lean_ctor_get(v_toApplicative_2083_, 1);
    lean_inc(v_toPure_2086_);
    v___x_2087_ = lean_box(0);
    v___x_2088_ = l_instInhabitedOfMonad___redArg(v_inst_2080_, v___x_2087_);
    v___f_2089_ = lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2089_, 0, v_toPure_2086_);
    lean_closure_set(v___f_2089_, 1, v_constName_2082_);
    lean_closure_set(v___f_2089_, 2, v___x_2088_);
    v___x_2090_ = lean_apply_4(
        v_toBind_2084_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2085_,
        v___f_2089_,
    );
    return v___x_2090_;
}
pub unsafe fn l_Lean_isRec_x3f(
    mut v_m_2091_: *mut LeanObject,
    mut v_inst_2092_: *mut LeanObject,
    mut v_inst_2093_: *mut LeanObject,
    mut v_constName_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_isRec_x3f___redArg(v_inst_2092_, v_inst_2093_, v_constName_2094_);
    return v___x_2095_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg___lam__0(
    mut v_constName_2097_: *mut LeanObject,
    mut v_toPure_2098_: *mut LeanObject,
    mut v_info_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v_levelParams_2100_ = lean_ctor_get(v_info_2099_, 1);
    lean_inc(v_levelParams_2100_);
    lean_dec_ref(v_info_2099_);
    v___x_2101_ = l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0;
    v___x_2102_ = lean_box(0);
    v___x_2103_ = l_List_mapTR_loop___redArg(v___x_2101_, v_levelParams_2100_, v___x_2102_);
    v___x_2104_ = l_Lean_mkConst(v_constName_2097_, v___x_2103_);
    v___x_2105_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___redArg(
    mut v_inst_2106_: *mut LeanObject,
    mut v_inst_2107_: *mut LeanObject,
    mut v_inst_2108_: *mut LeanObject,
    mut v_constName_2109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2110_ = lean_ctor_get(v_inst_2106_, 0);
    v_toBind_2111_ = lean_ctor_get(v_inst_2106_, 1);
    lean_inc(v_toBind_2111_);
    v_toPure_2112_ = lean_ctor_get(v_toApplicative_2110_, 1);
    lean_inc(v_toPure_2112_);
    lean_inc(v_constName_2109_);
    v___x_2113_ =
        l_Lean_getConstVal___redArg(v_inst_2106_, v_inst_2107_, v_inst_2108_, v_constName_2109_);
    v___f_2114_ = lean_alloc_closure(
        l_Lean_mkConstWithLevelParams___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2114_, 0, v_constName_2109_);
    lean_closure_set(v___f_2114_, 1, v_toPure_2112_);
    v___x_2115_ = lean_apply_4(
        v_toBind_2111_,
        lean_box(0),
        lean_box(0),
        v___x_2113_,
        v___f_2114_,
    );
    return v___x_2115_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams(
    mut v_m_2116_: *mut LeanObject,
    mut v_inst_2117_: *mut LeanObject,
    mut v_inst_2118_: *mut LeanObject,
    mut v_inst_2119_: *mut LeanObject,
    mut v_constName_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_mkConstWithLevelParams___redArg(
        v_inst_2117_,
        v_inst_2118_,
        v_inst_2119_,
        v_constName_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    v___x_2123_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__0;
    v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_getConstInfoDefn___redArg___lam__0___closed__2;
    v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg___lam__0(
    mut v_constName_2128_: *mut LeanObject,
    mut v_inst_2129_: *mut LeanObject,
    mut v_inst_2130_: *mut LeanObject,
    mut v_toPure_2131_: *mut LeanObject,
    mut v_____do__lift_2132_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2132_) == 0 {
        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: u8 = 0;
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2131_);
        v___x_2133_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2134_ = 0;
        v___x_2135_ = l_Lean_MessageData_ofConstName(v_constName_2128_, v___x_2134_);
        v___x_2136_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2136_, 0, v___x_2133_);
        lean_ctor_set(v___x_2136_, 1, v___x_2135_);
        v___x_2137_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3,
        );
        v___x_2138_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2138_, 0, v___x_2136_);
        lean_ctor_set(v___x_2138_, 1, v___x_2137_);
        v___x_2139_ = l_Lean_throwError___redArg(v_inst_2129_, v_inst_2130_, v___x_2138_);
        return v___x_2139_;
    } else {
        let mut v_val_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2130_);
        lean_dec_ref(v_inst_2129_);
        lean_dec(v_constName_2128_);
        v_val_2140_ = lean_ctor_get(v_____do__lift_2132_, 0);
        lean_inc(v_val_2140_);
        lean_dec_ref_known(v_____do__lift_2132_, 1);
        v___x_2141_ = lean_apply_2(v_toPure_2131_, lean_box(0), v_val_2140_);
        return v___x_2141_;
    }
}
pub unsafe fn l_Lean_getConstInfoDefn___redArg(
    mut v_inst_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_inst_2144_: *mut LeanObject,
    mut v_constName_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2146_ = lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2147_ = lean_ctor_get(v_inst_2142_, 1);
    lean_inc_n(v_toBind_2147_, 2);
    v_getEnv_2148_ = lean_ctor_get(v_inst_2143_, 0);
    lean_inc(v_getEnv_2148_);
    lean_dec_ref(v_inst_2143_);
    v_toPure_2149_ = lean_ctor_get(v_toApplicative_2146_, 1);
    lean_inc_n(v_toPure_2149_, 2);
    v___x_2150_ = lean_box(0);
    lean_inc_ref(v_inst_2142_);
    lean_inc(v_constName_2145_);
    v___f_2151_ = lean_alloc_closure(
        l_Lean_getConstInfoDefn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2151_, 0, v_constName_2145_);
    lean_closure_set(v___f_2151_, 1, v_inst_2142_);
    lean_closure_set(v___f_2151_, 2, v_inst_2144_);
    lean_closure_set(v___f_2151_, 3, v_toPure_2149_);
    v___x_2152_ = l_instInhabitedOfMonad___redArg(v_inst_2142_, v___x_2150_);
    v___f_2153_ = lean_alloc_closure(
        l_Lean_isDefn_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2153_, 0, v_toPure_2149_);
    lean_closure_set(v___f_2153_, 1, v_constName_2145_);
    lean_closure_set(v___f_2153_, 2, v___x_2152_);
    v___x_2154_ = lean_apply_4(
        v_toBind_2147_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2148_,
        v___f_2153_,
    );
    v___x_2155_ = lean_apply_4(
        v_toBind_2147_,
        lean_box(0),
        lean_box(0),
        v___x_2154_,
        v___f_2151_,
    );
    return v___x_2155_;
}
pub unsafe fn l_Lean_getConstInfoDefn(
    mut v_m_2156_: *mut LeanObject,
    mut v_inst_2157_: *mut LeanObject,
    mut v_inst_2158_: *mut LeanObject,
    mut v_inst_2159_: *mut LeanObject,
    mut v_constName_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_getConstInfoDefn___redArg(
        v_inst_2157_,
        v_inst_2158_,
        v_inst_2159_,
        v_constName_2160_,
    );
    return v___x_2161_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2163_ = l_Lean_getConstInfoInduct___redArg___lam__0___closed__0;
    v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__0(
    mut v_constName_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
    mut v_inst_2167_: *mut LeanObject,
    mut v_toPure_2168_: *mut LeanObject,
    mut v_____do__lift_2169_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2169_) == 0 {
        let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: u8 = 0;
        let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2168_);
        v___x_2170_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2171_ = 0;
        v___x_2172_ = l_Lean_MessageData_ofConstName(v_constName_2165_, v___x_2171_);
        v___x_2173_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2173_, 0, v___x_2170_);
        lean_ctor_set(v___x_2173_, 1, v___x_2172_);
        v___x_2174_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1,
        );
        v___x_2175_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2175_, 0, v___x_2173_);
        lean_ctor_set(v___x_2175_, 1, v___x_2174_);
        v___x_2176_ = l_Lean_throwError___redArg(v_inst_2166_, v_inst_2167_, v___x_2175_);
        return v___x_2176_;
    } else {
        let mut v_val_2177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2167_);
        lean_dec_ref(v_inst_2166_);
        lean_dec(v_constName_2165_);
        v_val_2177_ = lean_ctor_get(v_____do__lift_2169_, 0);
        lean_inc(v_val_2177_);
        lean_dec_ref_known(v_____do__lift_2169_, 1);
        v___x_2178_ = lean_apply_2(v_toPure_2168_, lean_box(0), v_val_2177_);
        return v___x_2178_;
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg___lam__1(
    mut v_constName_2179_: *mut LeanObject,
    mut v_toPure_2180_: *mut LeanObject,
    mut v_____do__lift_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_isInductiveCore_x3f(v_____do__lift_2181_, v_constName_2179_);
    v___x_2183_ = lean_apply_2(v_toPure_2180_, lean_box(0), v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean_getConstInfoInduct___redArg(
    mut v_inst_2184_: *mut LeanObject,
    mut v_inst_2185_: *mut LeanObject,
    mut v_inst_2186_: *mut LeanObject,
    mut v_constName_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2188_ = lean_ctor_get(v_inst_2184_, 0);
    v_toBind_2189_ = lean_ctor_get(v_inst_2184_, 1);
    lean_inc_n(v_toBind_2189_, 2);
    v_getEnv_2190_ = lean_ctor_get(v_inst_2185_, 0);
    lean_inc(v_getEnv_2190_);
    lean_dec_ref(v_inst_2185_);
    v_toPure_2191_ = lean_ctor_get(v_toApplicative_2188_, 1);
    lean_inc_n(v_toPure_2191_, 2);
    lean_inc(v_constName_2187_);
    v___f_2192_ = lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2192_, 0, v_constName_2187_);
    lean_closure_set(v___f_2192_, 1, v_inst_2184_);
    lean_closure_set(v___f_2192_, 2, v_inst_2186_);
    lean_closure_set(v___f_2192_, 3, v_toPure_2191_);
    v___f_2193_ = lean_alloc_closure(
        l_Lean_getConstInfoInduct___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2193_, 0, v_constName_2187_);
    lean_closure_set(v___f_2193_, 1, v_toPure_2191_);
    v___x_2194_ = lean_apply_4(
        v_toBind_2189_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2190_,
        v___f_2193_,
    );
    v___x_2195_ = lean_apply_4(
        v_toBind_2189_,
        lean_box(0),
        lean_box(0),
        v___x_2194_,
        v___f_2192_,
    );
    return v___x_2195_;
}
pub unsafe fn l_Lean_getConstInfoInduct(
    mut v_m_2196_: *mut LeanObject,
    mut v_inst_2197_: *mut LeanObject,
    mut v_inst_2198_: *mut LeanObject,
    mut v_inst_2199_: *mut LeanObject,
    mut v_constName_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Lean_getConstInfoInduct___redArg(
        v_inst_2197_,
        v_inst_2198_,
        v_inst_2199_,
        v_constName_2200_,
    );
    return v___x_2201_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Lean_getConstInfoCtor___redArg___lam__0___closed__0;
    v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg___lam__0(
    mut v_constName_2205_: *mut LeanObject,
    mut v_inst_2206_: *mut LeanObject,
    mut v_inst_2207_: *mut LeanObject,
    mut v_toPure_2208_: *mut LeanObject,
    mut v_____do__lift_2209_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2209_) == 0 {
        let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: u8 = 0;
        let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2208_);
        v___x_2210_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2211_ = 0;
        v___x_2212_ = l_Lean_MessageData_ofConstName(v_constName_2205_, v___x_2211_);
        v___x_2213_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2213_, 0, v___x_2210_);
        lean_ctor_set(v___x_2213_, 1, v___x_2212_);
        v___x_2214_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1,
        );
        v___x_2215_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2215_, 0, v___x_2213_);
        lean_ctor_set(v___x_2215_, 1, v___x_2214_);
        v___x_2216_ = l_Lean_throwError___redArg(v_inst_2206_, v_inst_2207_, v___x_2215_);
        return v___x_2216_;
    } else {
        let mut v_val_2217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2207_);
        lean_dec_ref(v_inst_2206_);
        lean_dec(v_constName_2205_);
        v_val_2217_ = lean_ctor_get(v_____do__lift_2209_, 0);
        lean_inc(v_val_2217_);
        lean_dec_ref_known(v_____do__lift_2209_, 1);
        v___x_2218_ = lean_apply_2(v_toPure_2208_, lean_box(0), v_val_2217_);
        return v___x_2218_;
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___redArg(
    mut v_inst_2219_: *mut LeanObject,
    mut v_inst_2220_: *mut LeanObject,
    mut v_inst_2221_: *mut LeanObject,
    mut v_constName_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2223_ = lean_ctor_get(v_inst_2219_, 0);
    v_toBind_2224_ = lean_ctor_get(v_inst_2219_, 1);
    lean_inc_n(v_toBind_2224_, 2);
    v_getEnv_2225_ = lean_ctor_get(v_inst_2220_, 0);
    lean_inc(v_getEnv_2225_);
    lean_dec_ref(v_inst_2220_);
    v_toPure_2226_ = lean_ctor_get(v_toApplicative_2223_, 1);
    lean_inc_n(v_toPure_2226_, 2);
    v___x_2227_ = lean_box(0);
    lean_inc_ref(v_inst_2219_);
    lean_inc(v_constName_2222_);
    v___f_2228_ = lean_alloc_closure(
        l_Lean_getConstInfoCtor___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2228_, 0, v_constName_2222_);
    lean_closure_set(v___f_2228_, 1, v_inst_2219_);
    lean_closure_set(v___f_2228_, 2, v_inst_2221_);
    lean_closure_set(v___f_2228_, 3, v_toPure_2226_);
    v___x_2229_ = l_instInhabitedOfMonad___redArg(v_inst_2219_, v___x_2227_);
    v___f_2230_ = lean_alloc_closure(
        l_Lean_isCtor_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2230_, 0, v_toPure_2226_);
    lean_closure_set(v___f_2230_, 1, v_constName_2222_);
    lean_closure_set(v___f_2230_, 2, v___x_2229_);
    v___x_2231_ = lean_apply_4(
        v_toBind_2224_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2225_,
        v___f_2230_,
    );
    v___x_2232_ = lean_apply_4(
        v_toBind_2224_,
        lean_box(0),
        lean_box(0),
        v___x_2231_,
        v___f_2228_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_getConstInfoCtor(
    mut v_m_2233_: *mut LeanObject,
    mut v_inst_2234_: *mut LeanObject,
    mut v_inst_2235_: *mut LeanObject,
    mut v_inst_2236_: *mut LeanObject,
    mut v_constName_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = l_Lean_getConstInfoCtor___redArg(
        v_inst_2234_,
        v_inst_2235_,
        v_inst_2236_,
        v_constName_2237_,
    );
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_getConstInfoRec___redArg___lam__0___closed__0;
    v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
    return v___x_2241_;
}
pub unsafe fn l_Lean_getConstInfoRec___redArg___lam__0(
    mut v_constName_2242_: *mut LeanObject,
    mut v_inst_2243_: *mut LeanObject,
    mut v_inst_2244_: *mut LeanObject,
    mut v_toPure_2245_: *mut LeanObject,
    mut v_____do__lift_2246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2246_) == 0 {
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: u8 = 0;
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2245_);
        v___x_2247_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1,
        );
        v___x_2248_ = 0;
        v___x_2249_ = l_Lean_MessageData_ofConstName(v_constName_2242_, v___x_2248_);
        v___x_2250_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2250_, 0, v___x_2247_);
        lean_ctor_set(v___x_2250_, 1, v___x_2249_);
        v___x_2251_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once),
            _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1,
        );
        v___x_2252_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2252_, 0, v___x_2250_);
        lean_ctor_set(v___x_2252_, 1, v___x_2251_);
        v___x_2253_ = l_Lean_throwError___redArg(v_inst_2243_, v_inst_2244_, v___x_2252_);
        return v___x_2253_;
    } else {
        let mut v_val_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2244_);
        lean_dec_ref(v_inst_2243_);
        lean_dec(v_constName_2242_);
        v_val_2254_ = lean_ctor_get(v_____do__lift_2246_, 0);
        lean_inc(v_val_2254_);
        lean_dec_ref_known(v_____do__lift_2246_, 1);
        v___x_2255_ = lean_apply_2(v_toPure_2245_, lean_box(0), v_val_2254_);
        return v___x_2255_;
    }
}
pub unsafe fn l_Lean_getConstInfoRec___redArg(
    mut v_inst_2256_: *mut LeanObject,
    mut v_inst_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
    mut v_constName_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2260_ = lean_ctor_get(v_inst_2256_, 0);
    v_toBind_2261_ = lean_ctor_get(v_inst_2256_, 1);
    lean_inc_n(v_toBind_2261_, 2);
    v_getEnv_2262_ = lean_ctor_get(v_inst_2257_, 0);
    lean_inc(v_getEnv_2262_);
    lean_dec_ref(v_inst_2257_);
    v_toPure_2263_ = lean_ctor_get(v_toApplicative_2260_, 1);
    lean_inc_n(v_toPure_2263_, 2);
    v___x_2264_ = lean_box(0);
    lean_inc_ref(v_inst_2256_);
    lean_inc(v_constName_2259_);
    v___f_2265_ = lean_alloc_closure(
        l_Lean_getConstInfoRec___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2265_, 0, v_constName_2259_);
    lean_closure_set(v___f_2265_, 1, v_inst_2256_);
    lean_closure_set(v___f_2265_, 2, v_inst_2258_);
    lean_closure_set(v___f_2265_, 3, v_toPure_2263_);
    v___x_2266_ = l_instInhabitedOfMonad___redArg(v_inst_2256_, v___x_2264_);
    v___f_2267_ = lean_alloc_closure(
        l_Lean_isRec_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2267_, 0, v_toPure_2263_);
    lean_closure_set(v___f_2267_, 1, v_constName_2259_);
    lean_closure_set(v___f_2267_, 2, v___x_2266_);
    v___x_2268_ = lean_apply_4(
        v_toBind_2261_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2262_,
        v___f_2267_,
    );
    v___x_2269_ = lean_apply_4(
        v_toBind_2261_,
        lean_box(0),
        lean_box(0),
        v___x_2268_,
        v___f_2265_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_getConstInfoRec(
    mut v_m_2270_: *mut LeanObject,
    mut v_inst_2271_: *mut LeanObject,
    mut v_inst_2272_: *mut LeanObject,
    mut v_inst_2273_: *mut LeanObject,
    mut v_constName_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_getConstInfoRec___redArg(
        v_inst_2271_,
        v_inst_2272_,
        v_inst_2273_,
        v_constName_2274_,
    );
    return v___x_2275_;
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__0(
    mut v_k_2276_: *mut LeanObject,
    mut v_val_2277_: *mut LeanObject,
    mut v_us_2278_: *mut LeanObject,
    mut v_failK_2279_: *mut LeanObject,
    mut v_____do__lift_2280_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2280_) == 6 {
        let mut v_val_2281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_failK_2279_);
        v_val_2281_ = lean_ctor_get(v_____do__lift_2280_, 0);
        lean_inc_ref(v_val_2281_);
        lean_dec_ref_known(v_____do__lift_2280_, 1);
        v___x_2282_ = lean_apply_3(v_k_2276_, v_val_2277_, v_us_2278_, v_val_2281_);
        return v___x_2282_;
    } else {
        let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____do__lift_2280_);
        lean_dec(v_us_2278_);
        lean_dec_ref(v_val_2277_);
        lean_dec(v_k_2276_);
        v___x_2283_ = lean_box(0);
        v___x_2284_ = lean_apply_1(v_failK_2279_, v___x_2283_);
        return v___x_2284_;
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg___lam__1(
    mut v_declName_2285_: *mut LeanObject,
    mut v_failK_2286_: *mut LeanObject,
    mut v_k_2287_: *mut LeanObject,
    mut v_us_2288_: *mut LeanObject,
    mut v_inst_2289_: *mut LeanObject,
    mut v_inst_2290_: *mut LeanObject,
    mut v_inst_2291_: *mut LeanObject,
    mut v_toBind_2292_: *mut LeanObject,
    mut v_____do__lift_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2298_) == 0 {
                    lean_dec(v_toBind_2292_);
                    lean_dec_ref(v_inst_2291_);
                    lean_dec_ref(v_inst_2290_);
                    lean_dec_ref(v_inst_2289_);
                    lean_dec(v_us_2288_);
                    lean_dec(v_k_2287_);
                    v___x_2299_ = lean_box(0);
                    v___x_2300_ = lean_apply_1(v_failK_2286_, v___x_2299_);
                    return v___x_2300_;
                } else {
                    v_val_2301_ = lean_ctor_get(v___x_2298_, 0);
                    lean_inc(v_val_2301_);
                    lean_dec_ref_known(v___x_2298_, 1);
                    if lean_obj_tag(v_val_2301_) == 5 {
                        v_val_2302_ = lean_ctor_get(v_val_2301_, 0);
                        lean_inc_ref(v_val_2302_);
                        lean_dec_ref_known(v_val_2301_, 1);
                        v_ctors_2303_ = lean_ctor_get(v_val_2302_, 4);
                        if lean_obj_tag(v_ctors_2303_) == 1 {
                            v_tail_2304_ = lean_ctor_get(v_ctors_2303_, 1);
                            if lean_obj_tag(v_tail_2304_) == 0 {
                                v_head_2305_ = lean_ctor_get(v_ctors_2303_, 0);
                                lean_inc(v_head_2305_);
                                v___f_2306_ = lean_alloc_closure(
                                    l_Lean_matchConstStructure___redArg___lam__0
                                        as *mut core::ffi::c_void,
                                    5,
                                    4,
                                );
                                lean_closure_set(v___f_2306_, 0, v_k_2287_);
                                lean_closure_set(v___f_2306_, 1, v_val_2302_);
                                lean_closure_set(v___f_2306_, 2, v_us_2288_);
                                lean_closure_set(v___f_2306_, 3, v_failK_2286_);
                                v___x_2307_ = l_Lean_getConstInfo___redArg(
                                    v_inst_2289_,
                                    v_inst_2290_,
                                    v_inst_2291_,
                                    v_head_2305_,
                                );
                                v___x_2308_ = lean_apply_4(
                                    v_toBind_2292_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2307_,
                                    v___f_2306_,
                                );
                                return v___x_2308_;
                            } else {
                                lean_dec_ref(v_val_2302_);
                                lean_dec(v_toBind_2292_);
                                lean_dec_ref(v_inst_2291_);
                                lean_dec_ref(v_inst_2290_);
                                lean_dec_ref(v_inst_2289_);
                                lean_dec(v_us_2288_);
                                lean_dec(v_k_2287_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_val_2302_);
                            lean_dec(v_toBind_2292_);
                            lean_dec_ref(v_inst_2291_);
                            lean_dec_ref(v_inst_2290_);
                            lean_dec_ref(v_inst_2289_);
                            lean_dec(v_us_2288_);
                            lean_dec(v_k_2287_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2301_);
                        lean_dec(v_toBind_2292_);
                        lean_dec_ref(v_inst_2291_);
                        lean_dec_ref(v_inst_2290_);
                        lean_dec_ref(v_inst_2289_);
                        lean_dec(v_us_2288_);
                        lean_dec(v_k_2287_);
                        v___x_2309_ = lean_box(0);
                        v___x_2310_ = lean_apply_1(v_failK_2286_, v___x_2309_);
                        return v___x_2310_;
                    }
                }
            }
            1 => {
                v___x_2295_ = lean_box(0);
                v___x_2296_ = lean_apply_1(v_failK_2286_, v___x_2295_);
                return v___x_2296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstStructure___redArg(
    mut v_inst_2311_: *mut LeanObject,
    mut v_inst_2312_: *mut LeanObject,
    mut v_inst_2313_: *mut LeanObject,
    mut v_e_2314_: *mut LeanObject,
    mut v_failK_2315_: *mut LeanObject,
    mut v_k_2316_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2314_) == 4 {
        let mut v_toBind_2317_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_2318_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_2319_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2317_ = lean_ctor_get(v_inst_2311_, 1);
        lean_inc_n(v_toBind_2317_, 2);
        v_declName_2318_ = lean_ctor_get(v_e_2314_, 0);
        lean_inc(v_declName_2318_);
        v_us_2319_ = lean_ctor_get(v_e_2314_, 1);
        lean_inc(v_us_2319_);
        lean_dec_ref_known(v_e_2314_, 2);
        v_getEnv_2320_ = lean_ctor_get(v_inst_2312_, 0);
        lean_inc(v_getEnv_2320_);
        v___f_2321_ = lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        lean_closure_set(v___f_2321_, 0, v_declName_2318_);
        lean_closure_set(v___f_2321_, 1, v_failK_2315_);
        lean_closure_set(v___f_2321_, 2, v_k_2316_);
        lean_closure_set(v___f_2321_, 3, v_us_2319_);
        lean_closure_set(v___f_2321_, 4, v_inst_2311_);
        lean_closure_set(v___f_2321_, 5, v_inst_2312_);
        lean_closure_set(v___f_2321_, 6, v_inst_2313_);
        lean_closure_set(v___f_2321_, 7, v_toBind_2317_);
        v___x_2322_ = lean_apply_4(
            v_toBind_2317_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2320_,
            v___f_2321_,
        );
        return v___x_2322_;
    } else {
        let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_2316_);
        lean_dec_ref(v_e_2314_);
        lean_dec_ref(v_inst_2313_);
        lean_dec_ref(v_inst_2312_);
        lean_dec_ref(v_inst_2311_);
        v___x_2323_ = lean_box(0);
        v___x_2324_ = lean_apply_1(v_failK_2315_, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_matchConstStructure(
    mut v_m_2325_: *mut LeanObject,
    mut v_00_u03b1_2326_: *mut LeanObject,
    mut v_inst_2327_: *mut LeanObject,
    mut v_inst_2328_: *mut LeanObject,
    mut v_inst_2329_: *mut LeanObject,
    mut v_e_2330_: *mut LeanObject,
    mut v_failK_2331_: *mut LeanObject,
    mut v_k_2332_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2330_) == 4 {
        let mut v_toBind_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_2334_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_2335_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2333_ = lean_ctor_get(v_inst_2327_, 1);
        lean_inc_n(v_toBind_2333_, 2);
        v_declName_2334_ = lean_ctor_get(v_e_2330_, 0);
        lean_inc(v_declName_2334_);
        v_us_2335_ = lean_ctor_get(v_e_2330_, 1);
        lean_inc(v_us_2335_);
        lean_dec_ref_known(v_e_2330_, 2);
        v_getEnv_2336_ = lean_ctor_get(v_inst_2328_, 0);
        lean_inc(v_getEnv_2336_);
        v___f_2337_ = lean_alloc_closure(
            l_Lean_matchConstStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        lean_closure_set(v___f_2337_, 0, v_declName_2334_);
        lean_closure_set(v___f_2337_, 1, v_failK_2331_);
        lean_closure_set(v___f_2337_, 2, v_k_2332_);
        lean_closure_set(v___f_2337_, 3, v_us_2335_);
        lean_closure_set(v___f_2337_, 4, v_inst_2327_);
        lean_closure_set(v___f_2337_, 5, v_inst_2328_);
        lean_closure_set(v___f_2337_, 6, v_inst_2329_);
        lean_closure_set(v___f_2337_, 7, v_toBind_2333_);
        v___x_2338_ = lean_apply_4(
            v_toBind_2333_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2336_,
            v___f_2337_,
        );
        return v___x_2338_;
    } else {
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_2332_);
        lean_dec_ref(v_e_2330_);
        lean_dec_ref(v_inst_2329_);
        lean_dec_ref(v_inst_2328_);
        lean_dec_ref(v_inst_2327_);
        v___x_2339_ = lean_box(0);
        v___x_2340_ = lean_apply_1(v_failK_2331_, v___x_2339_);
        return v___x_2340_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg___lam__1(
    mut v_declName_2341_: *mut LeanObject,
    mut v_failK_2342_: *mut LeanObject,
    mut v_k_2343_: *mut LeanObject,
    mut v_us_2344_: *mut LeanObject,
    mut v_inst_2345_: *mut LeanObject,
    mut v_inst_2346_: *mut LeanObject,
    mut v_inst_2347_: *mut LeanObject,
    mut v_toBind_2348_: *mut LeanObject,
    mut v_____do__lift_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRec_2362_: u8 = 0;
    let mut v_numIndices_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v_tail_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2357_) == 0 {
                    lean_dec(v_toBind_2348_);
                    lean_dec_ref(v_inst_2347_);
                    lean_dec_ref(v_inst_2346_);
                    lean_dec_ref(v_inst_2345_);
                    lean_dec(v_us_2344_);
                    lean_dec(v_k_2343_);
                    v___x_2358_ = lean_box(0);
                    v___x_2359_ = lean_apply_1(v_failK_2342_, v___x_2358_);
                    return v___x_2359_;
                } else {
                    v_val_2360_ = lean_ctor_get(v___x_2357_, 0);
                    lean_inc(v_val_2360_);
                    lean_dec_ref_known(v___x_2357_, 1);
                    if lean_obj_tag(v_val_2360_) == 5 {
                        v_val_2361_ = lean_ctor_get(v_val_2360_, 0);
                        lean_inc_ref(v_val_2361_);
                        lean_dec_ref_known(v_val_2360_, 1);
                        v_isRec_2362_ = lean_ctor_get_uint8(
                            v_val_2361_,
                            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                        );
                        if v_isRec_2362_ == 0 {
                            v_numIndices_2363_ = lean_ctor_get(v_val_2361_, 2);
                            v_ctors_2364_ = lean_ctor_get(v_val_2361_, 4);
                            v___x_2365_ = lean_unsigned_to_nat(0);
                            v___x_2366_ = lean_nat_dec_eq(v_numIndices_2363_, v___x_2365_);
                            if v___x_2366_ == 0 {
                                lean_dec_ref(v_val_2361_);
                                lean_dec(v_toBind_2348_);
                                lean_dec_ref(v_inst_2347_);
                                lean_dec_ref(v_inst_2346_);
                                lean_dec_ref(v_inst_2345_);
                                lean_dec(v_us_2344_);
                                lean_dec(v_k_2343_);
                                state = 1;
                                continue;
                            } else {
                                if lean_obj_tag(v_ctors_2364_) == 1 {
                                    v_tail_2367_ = lean_ctor_get(v_ctors_2364_, 1);
                                    if lean_obj_tag(v_tail_2367_) == 0 {
                                        v_head_2368_ = lean_ctor_get(v_ctors_2364_, 0);
                                        lean_inc(v_head_2368_);
                                        v___f_2369_ = lean_alloc_closure(
                                            l_Lean_matchConstStructure___redArg___lam__0
                                                as *mut core::ffi::c_void,
                                            5,
                                            4,
                                        );
                                        lean_closure_set(v___f_2369_, 0, v_k_2343_);
                                        lean_closure_set(v___f_2369_, 1, v_val_2361_);
                                        lean_closure_set(v___f_2369_, 2, v_us_2344_);
                                        lean_closure_set(v___f_2369_, 3, v_failK_2342_);
                                        v___x_2370_ = l_Lean_getConstInfo___redArg(
                                            v_inst_2345_,
                                            v_inst_2346_,
                                            v_inst_2347_,
                                            v_head_2368_,
                                        );
                                        v___x_2371_ = lean_apply_4(
                                            v_toBind_2348_,
                                            lean_box(0),
                                            lean_box(0),
                                            v___x_2370_,
                                            v___f_2369_,
                                        );
                                        return v___x_2371_;
                                    } else {
                                        lean_dec_ref(v_val_2361_);
                                        lean_dec(v_toBind_2348_);
                                        lean_dec_ref(v_inst_2347_);
                                        lean_dec_ref(v_inst_2346_);
                                        lean_dec_ref(v_inst_2345_);
                                        lean_dec(v_us_2344_);
                                        lean_dec(v_k_2343_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_val_2361_);
                                    lean_dec(v_toBind_2348_);
                                    lean_dec_ref(v_inst_2347_);
                                    lean_dec_ref(v_inst_2346_);
                                    lean_dec_ref(v_inst_2345_);
                                    lean_dec(v_us_2344_);
                                    lean_dec(v_k_2343_);
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_val_2361_);
                            lean_dec(v_toBind_2348_);
                            lean_dec_ref(v_inst_2347_);
                            lean_dec_ref(v_inst_2346_);
                            lean_dec_ref(v_inst_2345_);
                            lean_dec(v_us_2344_);
                            lean_dec(v_k_2343_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2360_);
                        lean_dec(v_toBind_2348_);
                        lean_dec_ref(v_inst_2347_);
                        lean_dec_ref(v_inst_2346_);
                        lean_dec_ref(v_inst_2345_);
                        lean_dec(v_us_2344_);
                        lean_dec(v_k_2343_);
                        v___x_2372_ = lean_box(0);
                        v___x_2373_ = lean_apply_1(v_failK_2342_, v___x_2372_);
                        return v___x_2373_;
                    }
                }
            }
            1 => {
                v___x_2351_ = lean_box(0);
                v___x_2352_ = lean_apply_1(v_failK_2342_, v___x_2351_);
                return v___x_2352_;
            }
            2 => {
                v___x_2354_ = lean_box(0);
                v___x_2355_ = lean_apply_1(v_failK_2342_, v___x_2354_);
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure___redArg(
    mut v_inst_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
    mut v_inst_2376_: *mut LeanObject,
    mut v_e_2377_: *mut LeanObject,
    mut v_failK_2378_: *mut LeanObject,
    mut v_k_2379_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2377_) == 4 {
        let mut v_toBind_2380_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_2381_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_2382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2380_ = lean_ctor_get(v_inst_2374_, 1);
        lean_inc_n(v_toBind_2380_, 2);
        v_declName_2381_ = lean_ctor_get(v_e_2377_, 0);
        lean_inc(v_declName_2381_);
        v_us_2382_ = lean_ctor_get(v_e_2377_, 1);
        lean_inc(v_us_2382_);
        lean_dec_ref_known(v_e_2377_, 2);
        v_getEnv_2383_ = lean_ctor_get(v_inst_2375_, 0);
        lean_inc(v_getEnv_2383_);
        v___f_2384_ = lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        lean_closure_set(v___f_2384_, 0, v_declName_2381_);
        lean_closure_set(v___f_2384_, 1, v_failK_2378_);
        lean_closure_set(v___f_2384_, 2, v_k_2379_);
        lean_closure_set(v___f_2384_, 3, v_us_2382_);
        lean_closure_set(v___f_2384_, 4, v_inst_2374_);
        lean_closure_set(v___f_2384_, 5, v_inst_2375_);
        lean_closure_set(v___f_2384_, 6, v_inst_2376_);
        lean_closure_set(v___f_2384_, 7, v_toBind_2380_);
        v___x_2385_ = lean_apply_4(
            v_toBind_2380_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2383_,
            v___f_2384_,
        );
        return v___x_2385_;
    } else {
        let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_2379_);
        lean_dec_ref(v_e_2377_);
        lean_dec_ref(v_inst_2376_);
        lean_dec_ref(v_inst_2375_);
        lean_dec_ref(v_inst_2374_);
        v___x_2386_ = lean_box(0);
        v___x_2387_ = lean_apply_1(v_failK_2378_, v___x_2386_);
        return v___x_2387_;
    }
}
pub unsafe fn l_Lean_matchConstNonRecStructure(
    mut v_m_2388_: *mut LeanObject,
    mut v_00_u03b1_2389_: *mut LeanObject,
    mut v_inst_2390_: *mut LeanObject,
    mut v_inst_2391_: *mut LeanObject,
    mut v_inst_2392_: *mut LeanObject,
    mut v_e_2393_: *mut LeanObject,
    mut v_failK_2394_: *mut LeanObject,
    mut v_k_2395_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2393_) == 4 {
        let mut v_toBind_2396_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_2397_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_2398_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getEnv_2399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2396_ = lean_ctor_get(v_inst_2390_, 1);
        lean_inc_n(v_toBind_2396_, 2);
        v_declName_2397_ = lean_ctor_get(v_e_2393_, 0);
        lean_inc(v_declName_2397_);
        v_us_2398_ = lean_ctor_get(v_e_2393_, 1);
        lean_inc(v_us_2398_);
        lean_dec_ref_known(v_e_2393_, 2);
        v_getEnv_2399_ = lean_ctor_get(v_inst_2391_, 0);
        lean_inc(v_getEnv_2399_);
        v___f_2400_ = lean_alloc_closure(
            l_Lean_matchConstNonRecStructure___redArg___lam__1 as *mut core::ffi::c_void,
            9,
            8,
        );
        lean_closure_set(v___f_2400_, 0, v_declName_2397_);
        lean_closure_set(v___f_2400_, 1, v_failK_2394_);
        lean_closure_set(v___f_2400_, 2, v_k_2395_);
        lean_closure_set(v___f_2400_, 3, v_us_2398_);
        lean_closure_set(v___f_2400_, 4, v_inst_2390_);
        lean_closure_set(v___f_2400_, 5, v_inst_2391_);
        lean_closure_set(v___f_2400_, 6, v_inst_2392_);
        lean_closure_set(v___f_2400_, 7, v_toBind_2396_);
        v___x_2401_ = lean_apply_4(
            v_toBind_2396_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2399_,
            v___f_2400_,
        );
        return v___x_2401_;
    } else {
        let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_2395_);
        lean_dec_ref(v_e_2393_);
        lean_dec_ref(v_inst_2392_);
        lean_dec_ref(v_inst_2391_);
        lean_dec_ref(v_inst_2390_);
        v___x_2402_ = lean_box(0);
        v___x_2403_ = lean_apply_1(v_failK_2394_, v___x_2402_);
        return v___x_2403_;
    }
}
pub unsafe fn l_Lean_hasCompileError___boxed(
    mut v_env_2406_: *mut LeanObject,
    mut v_constName_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut LeanObject = core::ptr::null_mut();
    v_res_2408_ = lean_has_compile_error(v_env_2406_, v_constName_2407_);
    v_r_2409_ = lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__0(
    mut v_____do__lift_2410_: *mut LeanObject,
    mut v_constName_2411_: *mut LeanObject,
    mut v_checkMeta_2412_: u8,
    mut v_inst_2413_: *mut LeanObject,
    mut v_inst_2414_: *mut LeanObject,
    mut v___x_2415_: *mut LeanObject,
    mut v_____do__lift_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_____do__lift_2419_: *mut LeanObject,
    mut v_constName_2420_: *mut LeanObject,
    mut v_checkMeta_2421_: *mut LeanObject,
    mut v_inst_2422_: *mut LeanObject,
    mut v_inst_2423_: *mut LeanObject,
    mut v___x_2424_: *mut LeanObject,
    mut v_____do__lift_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_2426_: u8 = 0;
    let mut v_res_2427_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2426_ = (lean_unbox(v_checkMeta_2421_) as u8);
    v_res_2427_ = l_Lean_evalConst___redArg___lam__0(
        v_____do__lift_2419_,
        v_constName_2420_,
        v_checkMeta_boxed_2426_,
        v_inst_2422_,
        v_inst_2423_,
        v___x_2424_,
        v_____do__lift_2425_,
    );
    lean_dec_ref(v_____do__lift_2425_);
    lean_dec(v_constName_2420_);
    lean_dec_ref(v_____do__lift_2419_);
    return v_res_2427_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1(
    mut v_constName_2428_: *mut LeanObject,
    mut v_checkMeta_2429_: u8,
    mut v_inst_2430_: *mut LeanObject,
    mut v_inst_2431_: *mut LeanObject,
    mut v___x_2432_: *mut LeanObject,
    mut v_toBind_2433_: *mut LeanObject,
    mut v_inst_2434_: *mut LeanObject,
    mut v_____do__lift_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = lean_box((v_checkMeta_2429_) as usize);
    v___f_2437_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2437_, 0, v_____do__lift_2435_);
    lean_closure_set(v___f_2437_, 1, v_constName_2428_);
    lean_closure_set(v___f_2437_, 2, v___x_2436_);
    lean_closure_set(v___f_2437_, 3, v_inst_2430_);
    lean_closure_set(v___f_2437_, 4, v_inst_2431_);
    lean_closure_set(v___f_2437_, 5, v___x_2432_);
    v___x_2438_ = lean_apply_4(
        v_toBind_2433_,
        lean_box(0),
        lean_box(0),
        v_inst_2434_,
        v___f_2437_,
    );
    return v___x_2438_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__1___boxed(
    mut v_constName_2439_: *mut LeanObject,
    mut v_checkMeta_2440_: *mut LeanObject,
    mut v_inst_2441_: *mut LeanObject,
    mut v_inst_2442_: *mut LeanObject,
    mut v___x_2443_: *mut LeanObject,
    mut v_toBind_2444_: *mut LeanObject,
    mut v_inst_2445_: *mut LeanObject,
    mut v_____do__lift_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_2447_: u8 = 0;
    let mut v_res_2448_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2447_ = (lean_unbox(v_checkMeta_2440_) as u8);
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
    mut v_toBind_2449_: *mut LeanObject,
    mut v_getEnv_2450_: *mut LeanObject,
    mut v___f_2451_: *mut LeanObject,
    mut v_____r_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    v___x_2453_ = lean_apply_4(
        v_toBind_2449_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2450_,
        v___f_2451_,
    );
    return v___x_2453_;
}
pub unsafe fn l_Lean_evalConst___redArg___lam__3(
    mut v_constName_2454_: *mut LeanObject,
    mut v_toBind_2455_: *mut LeanObject,
    mut v_getEnv_2456_: *mut LeanObject,
    mut v___f_2457_: *mut LeanObject,
    mut v_inst_2458_: *mut LeanObject,
    mut v___f_2459_: *mut LeanObject,
    mut v_____do__lift_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2461_: u8 = 0;
    v___x_2461_ = lean_has_compile_error(v_____do__lift_2460_, v_constName_2454_);
    if v___x_2461_ == 0 {
        let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2459_);
        lean_dec_ref(v_inst_2458_);
        v___x_2462_ = lean_apply_4(
            v_toBind_2455_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2456_,
            v___f_2457_,
        );
        return v___x_2462_;
    } else {
        let mut v_toMonadExceptOf_2463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2457_);
        lean_dec(v_getEnv_2456_);
        v_toMonadExceptOf_2463_ = lean_ctor_get(v_inst_2458_, 0);
        lean_inc_ref(v_toMonadExceptOf_2463_);
        lean_dec_ref(v_inst_2458_);
        v___x_2464_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_2463_);
        v___x_2465_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_2464_);
        v___x_2466_ = lean_apply_4(
            v_toBind_2455_,
            lean_box(0),
            lean_box(0),
            v___x_2465_,
            v___f_2459_,
        );
        return v___x_2466_;
    }
}
pub unsafe fn l_Lean_evalConst___redArg(
    mut v_inst_2468_: *mut LeanObject,
    mut v_inst_2469_: *mut LeanObject,
    mut v_inst_2470_: *mut LeanObject,
    mut v_inst_2471_: *mut LeanObject,
    mut v_constName_2472_: *mut LeanObject,
    mut v_checkMeta_2473_: u8,
) -> *mut LeanObject {
    let mut v_toBind_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2474_ = lean_ctor_get(v_inst_2468_, 1);
    lean_inc_n(v_toBind_2474_, 4);
    v_getEnv_2475_ = lean_ctor_get(v_inst_2469_, 0);
    lean_inc_n(v_getEnv_2475_, 3);
    lean_dec_ref(v_inst_2469_);
    v___x_2476_ = l_Lean_evalConst___redArg___closed__0;
    v___x_2477_ = lean_box((v_checkMeta_2473_) as usize);
    lean_inc_ref(v_inst_2470_);
    lean_inc(v_constName_2472_);
    v___f_2478_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2478_, 0, v_constName_2472_);
    lean_closure_set(v___f_2478_, 1, v___x_2477_);
    lean_closure_set(v___f_2478_, 2, v_inst_2468_);
    lean_closure_set(v___f_2478_, 3, v_inst_2470_);
    lean_closure_set(v___f_2478_, 4, v___x_2476_);
    lean_closure_set(v___f_2478_, 5, v_toBind_2474_);
    lean_closure_set(v___f_2478_, 6, v_inst_2471_);
    lean_inc_ref(v___f_2478_);
    v___f_2479_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2479_, 0, v_toBind_2474_);
    lean_closure_set(v___f_2479_, 1, v_getEnv_2475_);
    lean_closure_set(v___f_2479_, 2, v___f_2478_);
    v___f_2480_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2480_, 0, v_constName_2472_);
    lean_closure_set(v___f_2480_, 1, v_toBind_2474_);
    lean_closure_set(v___f_2480_, 2, v_getEnv_2475_);
    lean_closure_set(v___f_2480_, 3, v___f_2478_);
    lean_closure_set(v___f_2480_, 4, v_inst_2470_);
    lean_closure_set(v___f_2480_, 5, v___f_2479_);
    v___x_2481_ = lean_apply_4(
        v_toBind_2474_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2475_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_evalConst___redArg___boxed(
    mut v_inst_2482_: *mut LeanObject,
    mut v_inst_2483_: *mut LeanObject,
    mut v_inst_2484_: *mut LeanObject,
    mut v_inst_2485_: *mut LeanObject,
    mut v_constName_2486_: *mut LeanObject,
    mut v_checkMeta_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_2488_: u8 = 0;
    let mut v_res_2489_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2488_ = (lean_unbox(v_checkMeta_2487_) as u8);
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
    mut v_m_2490_: *mut LeanObject,
    mut v_inst_2491_: *mut LeanObject,
    mut v_inst_2492_: *mut LeanObject,
    mut v_inst_2493_: *mut LeanObject,
    mut v_inst_2494_: *mut LeanObject,
    mut v_00_u03b1_2495_: *mut LeanObject,
    mut v_constName_2496_: *mut LeanObject,
    mut v_checkMeta_2497_: u8,
) -> *mut LeanObject {
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_inst_2501_: *mut LeanObject,
    mut v_inst_2502_: *mut LeanObject,
    mut v_inst_2503_: *mut LeanObject,
    mut v_00_u03b1_2504_: *mut LeanObject,
    mut v_constName_2505_: *mut LeanObject,
    mut v_checkMeta_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_2507_: u8 = 0;
    let mut v_res_2508_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2507_ = (lean_unbox(v_checkMeta_2506_) as u8);
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
    mut v_____do__lift_2509_: *mut LeanObject,
    mut v_typeName_2510_: *mut LeanObject,
    mut v_constName_2511_: *mut LeanObject,
    mut v_inst_2512_: *mut LeanObject,
    mut v_inst_2513_: *mut LeanObject,
    mut v___x_2514_: *mut LeanObject,
    mut v_____do__lift_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_____do__lift_2518_: *mut LeanObject,
    mut v_typeName_2519_: *mut LeanObject,
    mut v_constName_2520_: *mut LeanObject,
    mut v_inst_2521_: *mut LeanObject,
    mut v_inst_2522_: *mut LeanObject,
    mut v___x_2523_: *mut LeanObject,
    mut v_____do__lift_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_evalConstCheck___redArg___lam__0(
        v_____do__lift_2518_,
        v_typeName_2519_,
        v_constName_2520_,
        v_inst_2521_,
        v_inst_2522_,
        v___x_2523_,
        v_____do__lift_2524_,
    );
    lean_dec_ref(v_____do__lift_2524_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg___lam__1(
    mut v_typeName_2526_: *mut LeanObject,
    mut v_constName_2527_: *mut LeanObject,
    mut v_inst_2528_: *mut LeanObject,
    mut v_inst_2529_: *mut LeanObject,
    mut v___x_2530_: *mut LeanObject,
    mut v_toBind_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_____do__lift_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___f_2534_ = lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2534_, 0, v_____do__lift_2533_);
    lean_closure_set(v___f_2534_, 1, v_typeName_2526_);
    lean_closure_set(v___f_2534_, 2, v_constName_2527_);
    lean_closure_set(v___f_2534_, 3, v_inst_2528_);
    lean_closure_set(v___f_2534_, 4, v_inst_2529_);
    lean_closure_set(v___f_2534_, 5, v___x_2530_);
    v___x_2535_ = lean_apply_4(
        v_toBind_2531_,
        lean_box(0),
        lean_box(0),
        v_inst_2532_,
        v___f_2534_,
    );
    return v___x_2535_;
}
pub unsafe fn l_Lean_evalConstCheck___redArg(
    mut v_inst_2536_: *mut LeanObject,
    mut v_inst_2537_: *mut LeanObject,
    mut v_inst_2538_: *mut LeanObject,
    mut v_inst_2539_: *mut LeanObject,
    mut v_typeName_2540_: *mut LeanObject,
    mut v_constName_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2542_ = lean_ctor_get(v_inst_2536_, 1);
    lean_inc_n(v_toBind_2542_, 4);
    v_getEnv_2543_ = lean_ctor_get(v_inst_2537_, 0);
    lean_inc_n(v_getEnv_2543_, 3);
    lean_dec_ref(v_inst_2537_);
    v___x_2544_ = l_Lean_evalConst___redArg___closed__0;
    lean_inc_ref(v_inst_2538_);
    lean_inc(v_constName_2541_);
    v___f_2545_ = lean_alloc_closure(
        l_Lean_evalConstCheck___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2545_, 0, v_typeName_2540_);
    lean_closure_set(v___f_2545_, 1, v_constName_2541_);
    lean_closure_set(v___f_2545_, 2, v_inst_2536_);
    lean_closure_set(v___f_2545_, 3, v_inst_2538_);
    lean_closure_set(v___f_2545_, 4, v___x_2544_);
    lean_closure_set(v___f_2545_, 5, v_toBind_2542_);
    lean_closure_set(v___f_2545_, 6, v_inst_2539_);
    lean_inc_ref(v___f_2545_);
    v___f_2546_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2546_, 0, v_toBind_2542_);
    lean_closure_set(v___f_2546_, 1, v_getEnv_2543_);
    lean_closure_set(v___f_2546_, 2, v___f_2545_);
    v___f_2547_ = lean_alloc_closure(
        l_Lean_evalConst___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2547_, 0, v_constName_2541_);
    lean_closure_set(v___f_2547_, 1, v_toBind_2542_);
    lean_closure_set(v___f_2547_, 2, v_getEnv_2543_);
    lean_closure_set(v___f_2547_, 3, v___f_2545_);
    lean_closure_set(v___f_2547_, 4, v_inst_2538_);
    lean_closure_set(v___f_2547_, 5, v___f_2546_);
    v___x_2548_ = lean_apply_4(
        v_toBind_2542_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2543_,
        v___f_2547_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_evalConstCheck(
    mut v_m_2549_: *mut LeanObject,
    mut v_inst_2550_: *mut LeanObject,
    mut v_inst_2551_: *mut LeanObject,
    mut v_inst_2552_: *mut LeanObject,
    mut v_inst_2553_: *mut LeanObject,
    mut v_00_u03b1_2554_: *mut LeanObject,
    mut v_typeName_2555_: *mut LeanObject,
    mut v_constName_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_2558_: *mut LeanObject,
    mut v_val_2559_: *mut LeanObject,
    mut v_toPure_2560_: *mut LeanObject,
    mut v_____do__lift_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_2561_);
    v___x_2563_ = lean_array_get(v___x_2558_, v___x_2562_, v_val_2559_);
    lean_dec_ref(v___x_2562_);
    v___x_2564_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    v___x_2565_ = lean_apply_2(v_toPure_2560_, lean_box(0), v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(
    mut v___x_2566_: *mut LeanObject,
    mut v_val_2567_: *mut LeanObject,
    mut v_toPure_2568_: *mut LeanObject,
    mut v_____do__lift_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2570_: *mut LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Lean_findModuleOf_x3f___redArg___lam__0(
        v___x_2566_,
        v_val_2567_,
        v_toPure_2568_,
        v_____do__lift_2569_,
    );
    lean_dec_ref(v_____do__lift_2569_);
    lean_dec(v_val_2567_);
    lean_dec(v___x_2566_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1(
    mut v_declName_2571_: *mut LeanObject,
    mut v_toPure_2572_: *mut LeanObject,
    mut v___x_2573_: *mut LeanObject,
    mut v_toBind_2574_: *mut LeanObject,
    mut v_getEnv_2575_: *mut LeanObject,
    mut v_____do__lift_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    v___x_2577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2576_, v_declName_2571_);
    if lean_obj_tag(v___x_2577_) == 0 {
        let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_getEnv_2575_);
        lean_dec(v_toBind_2574_);
        lean_dec(v___x_2573_);
        v___x_2578_ = lean_box(0);
        v___x_2579_ = lean_apply_2(v_toPure_2572_, lean_box(0), v___x_2578_);
        return v___x_2579_;
    } else {
        let mut v_val_2580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
        v_val_2580_ = lean_ctor_get(v___x_2577_, 0);
        lean_inc(v_val_2580_);
        lean_dec_ref_known(v___x_2577_, 1);
        v___f_2581_ = lean_alloc_closure(
            l_Lean_findModuleOf_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_2581_, 0, v___x_2573_);
        lean_closure_set(v___f_2581_, 1, v_val_2580_);
        lean_closure_set(v___f_2581_, 2, v_toPure_2572_);
        v___x_2582_ = lean_apply_4(
            v_toBind_2574_,
            lean_box(0),
            lean_box(0),
            v_getEnv_2575_,
            v___f_2581_,
        );
        return v___x_2582_;
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(
    mut v_declName_2583_: *mut LeanObject,
    mut v_toPure_2584_: *mut LeanObject,
    mut v___x_2585_: *mut LeanObject,
    mut v_toBind_2586_: *mut LeanObject,
    mut v_getEnv_2587_: *mut LeanObject,
    mut v_____do__lift_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_Lean_findModuleOf_x3f___redArg___lam__1(
        v_declName_2583_,
        v_toPure_2584_,
        v___x_2585_,
        v_toBind_2586_,
        v_getEnv_2587_,
        v_____do__lift_2588_,
    );
    lean_dec_ref(v_____do__lift_2588_);
    lean_dec(v_declName_2583_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg___lam__2(
    mut v_inst_2590_: *mut LeanObject,
    mut v_declName_2591_: *mut LeanObject,
    mut v_toPure_2592_: *mut LeanObject,
    mut v___x_2593_: *mut LeanObject,
    mut v_toBind_2594_: *mut LeanObject,
    mut v_____r_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getEnv_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    v_getEnv_2596_ = lean_ctor_get(v_inst_2590_, 0);
    lean_inc_n(v_getEnv_2596_, 2);
    lean_dec_ref(v_inst_2590_);
    lean_inc(v_toBind_2594_);
    v___f_2597_ = lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2597_, 0, v_declName_2591_);
    lean_closure_set(v___f_2597_, 1, v_toPure_2592_);
    lean_closure_set(v___f_2597_, 2, v___x_2593_);
    lean_closure_set(v___f_2597_, 3, v_toBind_2594_);
    lean_closure_set(v___f_2597_, 4, v_getEnv_2596_);
    v___x_2598_ = lean_apply_4(
        v_toBind_2594_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2596_,
        v___f_2597_,
    );
    return v___x_2598_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___redArg(
    mut v_inst_2599_: *mut LeanObject,
    mut v_inst_2600_: *mut LeanObject,
    mut v_inst_2601_: *mut LeanObject,
    mut v_declName_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2603_ = lean_ctor_get(v_inst_2599_, 0);
    v_toFunctor_2604_ = lean_ctor_get(v_toApplicative_2603_, 0);
    v_toBind_2605_ = lean_ctor_get(v_inst_2599_, 1);
    lean_inc_n(v_toBind_2605_, 2);
    v_toPure_2606_ = lean_ctor_get(v_toApplicative_2603_, 1);
    v_mapConst_2607_ = lean_ctor_get(v_toFunctor_2604_, 1);
    lean_inc(v_mapConst_2607_);
    v___x_2608_ = lean_box(0);
    lean_inc(v_toPure_2606_);
    lean_inc(v_declName_2602_);
    lean_inc_ref(v_inst_2600_);
    v___f_2609_ = lean_alloc_closure(
        l_Lean_findModuleOf_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2609_, 0, v_inst_2600_);
    lean_closure_set(v___f_2609_, 1, v_declName_2602_);
    lean_closure_set(v___f_2609_, 2, v_toPure_2606_);
    lean_closure_set(v___f_2609_, 3, v___x_2608_);
    lean_closure_set(v___f_2609_, 4, v_toBind_2605_);
    v___x_2610_ =
        l_Lean_getConstInfo___redArg(v_inst_2599_, v_inst_2600_, v_inst_2601_, v_declName_2602_);
    v___x_2611_ = lean_box(0);
    v___x_2612_ = lean_apply_4(
        v_mapConst_2607_,
        lean_box(0),
        lean_box(0),
        v___x_2611_,
        v___x_2610_,
    );
    v___x_2613_ = lean_apply_4(
        v_toBind_2605_,
        lean_box(0),
        lean_box(0),
        v___x_2612_,
        v___f_2609_,
    );
    return v___x_2613_;
}
pub unsafe fn l_Lean_findModuleOf_x3f(
    mut v_m_2614_: *mut LeanObject,
    mut v_inst_2615_: *mut LeanObject,
    mut v_inst_2616_: *mut LeanObject,
    mut v_inst_2617_: *mut LeanObject,
    mut v_declName_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_findModuleOf_x3f___redArg(
        v_inst_2615_,
        v_inst_2616_,
        v_inst_2617_,
        v_declName_2618_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0(
    mut v___x_2620_: *mut LeanObject,
    mut v_toPure_2621_: *mut LeanObject,
    mut v_isUnsafe_2622_: u8,
    mut v_____x_2623_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2623_) == 6 {
        let mut v_val_2624_: *mut LeanObject = core::ptr::null_mut();
        let mut v_numFields_2625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2626_: u8 = 0;
        let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
        v_val_2624_ = lean_ctor_get(v_____x_2623_, 0);
        v_numFields_2625_ = lean_ctor_get(v_val_2624_, 4);
        v___x_2626_ = lean_nat_dec_eq(v_numFields_2625_, v___x_2620_);
        v___x_2627_ = lean_box((v___x_2626_) as usize);
        v___x_2628_ = lean_apply_2(v_toPure_2621_, lean_box(0), v___x_2627_);
        return v___x_2628_;
    } else {
        let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
        v___x_2629_ = lean_box((v_isUnsafe_2622_) as usize);
        v___x_2630_ = lean_apply_2(v_toPure_2621_, lean_box(0), v___x_2629_);
        return v___x_2630_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__0___boxed(
    mut v___x_2631_: *mut LeanObject,
    mut v_toPure_2632_: *mut LeanObject,
    mut v_isUnsafe_2633_: *mut LeanObject,
    mut v_____x_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isUnsafe_boxed_2635_: u8 = 0;
    let mut v_res_2636_: *mut LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2635_ = (lean_unbox(v_isUnsafe_2633_) as u8);
    v_res_2636_ = l_Lean_isEnumType___redArg___lam__0(
        v___x_2631_,
        v_toPure_2632_,
        v_isUnsafe_boxed_2635_,
        v_____x_2634_,
    );
    lean_dec_ref(v_____x_2634_);
    lean_dec(v___x_2631_);
    return v_res_2636_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__1(
    mut v_inst_2637_: *mut LeanObject,
    mut v_inst_2638_: *mut LeanObject,
    mut v_inst_2639_: *mut LeanObject,
    mut v_toBind_2640_: *mut LeanObject,
    mut v___f_2641_: *mut LeanObject,
    mut v_ctorName_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2643_ =
        l_Lean_getConstInfo___redArg(v_inst_2637_, v_inst_2638_, v_inst_2639_, v_ctorName_2642_);
    v___x_2644_ = lean_apply_4(
        v_toBind_2640_,
        lean_box(0),
        lean_box(0),
        v___x_2643_,
        v___f_2641_,
    );
    return v___x_2644_;
}
pub unsafe fn l_Lean_isEnumType___redArg___lam__2(
    mut v_toPure_2645_: *mut LeanObject,
    mut v_inst_2646_: *mut LeanObject,
    mut v_inst_2647_: *mut LeanObject,
    mut v_inst_2648_: *mut LeanObject,
    mut v_toBind_2649_: *mut LeanObject,
    mut v_____do__lift_2650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2650_) == 5 {
        let mut v_val_2651_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toConstantVal_2652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_numParams_2653_: *mut LeanObject = core::ptr::null_mut();
        let mut v_numIndices_2654_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ctors_2655_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isRec_2656_: u8 = 0;
        let mut v_isUnsafe_2657_: u8 = 0;
        let mut v_type_2658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2659_: u8 = 0;
        v_val_2651_ = lean_ctor_get(v_____do__lift_2650_, 0);
        lean_inc_ref(v_val_2651_);
        lean_dec_ref_known(v_____do__lift_2650_, 1);
        v_toConstantVal_2652_ = lean_ctor_get(v_val_2651_, 0);
        v_numParams_2653_ = lean_ctor_get(v_val_2651_, 1);
        lean_inc(v_numParams_2653_);
        v_numIndices_2654_ = lean_ctor_get(v_val_2651_, 2);
        lean_inc(v_numIndices_2654_);
        v_ctors_2655_ = lean_ctor_get(v_val_2651_, 4);
        lean_inc(v_ctors_2655_);
        v_isRec_2656_ = lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        );
        v_isUnsafe_2657_ = lean_ctor_get_uint8(
            v_val_2651_,
            (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
        );
        v_type_2658_ = lean_ctor_get(v_toConstantVal_2652_, 2);
        v___x_2659_ = l_Lean_Expr_isProp(v_type_2658_);
        if v___x_2659_ == 0 {
            let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2662_: u8 = 0;
            v___x_2660_ = l_Lean_InductiveVal_numTypeFormers(v_val_2651_);
            lean_dec_ref(v_val_2651_);
            v___x_2661_ = lean_unsigned_to_nat(1);
            v___x_2662_ = lean_nat_dec_eq(v___x_2660_, v___x_2661_);
            lean_dec(v___x_2660_);
            if v___x_2662_ == 0 {
                let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_ctors_2655_);
                lean_dec(v_numIndices_2654_);
                lean_dec(v_numParams_2653_);
                lean_dec(v_toBind_2649_);
                lean_dec_ref(v_inst_2648_);
                lean_dec_ref(v_inst_2647_);
                lean_dec_ref(v_inst_2646_);
                v___x_2663_ = lean_box((v___x_2662_) as usize);
                v___x_2664_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2663_);
                return v___x_2664_;
            } else {
                let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2666_: u8 = 0;
                v___x_2665_ = lean_unsigned_to_nat(0);
                v___x_2666_ = lean_nat_dec_eq(v_numIndices_2654_, v___x_2665_);
                lean_dec(v_numIndices_2654_);
                if v___x_2666_ == 0 {
                    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_ctors_2655_);
                    lean_dec(v_numParams_2653_);
                    lean_dec(v_toBind_2649_);
                    lean_dec_ref(v_inst_2648_);
                    lean_dec_ref(v_inst_2647_);
                    lean_dec_ref(v_inst_2646_);
                    v___x_2667_ = lean_box((v___x_2666_) as usize);
                    v___x_2668_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2667_);
                    return v___x_2668_;
                } else {
                    let mut v___x_2669_: u8 = 0;
                    v___x_2669_ = lean_nat_dec_eq(v_numParams_2653_, v___x_2665_);
                    lean_dec(v_numParams_2653_);
                    if v___x_2669_ == 0 {
                        let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_ctors_2655_);
                        lean_dec(v_toBind_2649_);
                        lean_dec_ref(v_inst_2648_);
                        lean_dec_ref(v_inst_2647_);
                        lean_dec_ref(v_inst_2646_);
                        v___x_2670_ = lean_box((v___x_2669_) as usize);
                        v___x_2671_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2670_);
                        return v___x_2671_;
                    } else {
                        let mut v___x_2672_: u8 = 0;
                        v___x_2672_ = l_List_isEmpty___redArg(v_ctors_2655_);
                        if v___x_2672_ == 0 {
                            if v_isRec_2656_ == 0 {
                                if v_isUnsafe_2657_ == 0 {
                                    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___f_2674_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___f_2675_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
                                    v___x_2673_ = lean_box((v_isUnsafe_2657_) as usize);
                                    v___f_2674_ = lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    lean_closure_set(v___f_2674_, 0, v___x_2665_);
                                    lean_closure_set(v___f_2674_, 1, v_toPure_2645_);
                                    lean_closure_set(v___f_2674_, 2, v___x_2673_);
                                    lean_inc_ref(v_inst_2646_);
                                    v___f_2675_ = lean_alloc_closure(
                                        l_Lean_isEnumType___redArg___lam__1
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    lean_closure_set(v___f_2675_, 0, v_inst_2646_);
                                    lean_closure_set(v___f_2675_, 1, v_inst_2647_);
                                    lean_closure_set(v___f_2675_, 2, v_inst_2648_);
                                    lean_closure_set(v___f_2675_, 3, v_toBind_2649_);
                                    lean_closure_set(v___f_2675_, 4, v___f_2674_);
                                    v___x_2676_ = l_List_allM___redArg(
                                        v_inst_2646_,
                                        v___f_2675_,
                                        v_ctors_2655_,
                                    );
                                    return v___x_2676_;
                                } else {
                                    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v_ctors_2655_);
                                    lean_dec(v_toBind_2649_);
                                    lean_dec_ref(v_inst_2648_);
                                    lean_dec_ref(v_inst_2647_);
                                    lean_dec_ref(v_inst_2646_);
                                    v___x_2677_ = lean_box((v_isRec_2656_) as usize);
                                    v___x_2678_ =
                                        lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2677_);
                                    return v___x_2678_;
                                }
                            } else {
                                let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec(v_ctors_2655_);
                                lean_dec(v_toBind_2649_);
                                lean_dec_ref(v_inst_2648_);
                                lean_dec_ref(v_inst_2647_);
                                lean_dec_ref(v_inst_2646_);
                                v___x_2679_ = lean_box((v___x_2672_) as usize);
                                v___x_2680_ =
                                    lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2679_);
                                return v___x_2680_;
                            }
                        } else {
                            let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_ctors_2655_);
                            lean_dec(v_toBind_2649_);
                            lean_dec_ref(v_inst_2648_);
                            lean_dec_ref(v_inst_2647_);
                            lean_dec_ref(v_inst_2646_);
                            v___x_2681_ = lean_box((v___x_2659_) as usize);
                            v___x_2682_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2681_);
                            return v___x_2682_;
                        }
                    }
                }
            }
        } else {
            let mut v___x_2683_: u8 = 0;
            let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_ctors_2655_);
            lean_dec(v_numIndices_2654_);
            lean_dec(v_numParams_2653_);
            lean_dec_ref(v_val_2651_);
            lean_dec(v_toBind_2649_);
            lean_dec_ref(v_inst_2648_);
            lean_dec_ref(v_inst_2647_);
            lean_dec_ref(v_inst_2646_);
            v___x_2683_ = 0;
            v___x_2684_ = lean_box((v___x_2683_) as usize);
            v___x_2685_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2684_);
            return v___x_2685_;
        }
    } else {
        let mut v___x_2686_: u8 = 0;
        let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____do__lift_2650_);
        lean_dec(v_toBind_2649_);
        lean_dec_ref(v_inst_2648_);
        lean_dec_ref(v_inst_2647_);
        lean_dec_ref(v_inst_2646_);
        v___x_2686_ = 0;
        v___x_2687_ = lean_box((v___x_2686_) as usize);
        v___x_2688_ = lean_apply_2(v_toPure_2645_, lean_box(0), v___x_2687_);
        return v___x_2688_;
    }
}
pub unsafe fn l_Lean_isEnumType___redArg(
    mut v_inst_2689_: *mut LeanObject,
    mut v_inst_2690_: *mut LeanObject,
    mut v_inst_2691_: *mut LeanObject,
    mut v_declName_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2693_ = lean_ctor_get(v_inst_2689_, 0);
    v_toBind_2694_ = lean_ctor_get(v_inst_2689_, 1);
    lean_inc_n(v_toBind_2694_, 2);
    v_toPure_2695_ = lean_ctor_get(v_toApplicative_2693_, 1);
    lean_inc(v_toPure_2695_);
    lean_inc_ref(v_inst_2691_);
    lean_inc_ref(v_inst_2690_);
    lean_inc_ref(v_inst_2689_);
    v___x_2696_ =
        l_Lean_getConstInfo___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_declName_2692_);
    v___f_2697_ = lean_alloc_closure(
        l_Lean_isEnumType___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2697_, 0, v_toPure_2695_);
    lean_closure_set(v___f_2697_, 1, v_inst_2689_);
    lean_closure_set(v___f_2697_, 2, v_inst_2690_);
    lean_closure_set(v___f_2697_, 3, v_inst_2691_);
    lean_closure_set(v___f_2697_, 4, v_toBind_2694_);
    v___x_2698_ = lean_apply_4(
        v_toBind_2694_,
        lean_box(0),
        lean_box(0),
        v___x_2696_,
        v___f_2697_,
    );
    return v___x_2698_;
}
pub unsafe fn l_Lean_isEnumType(
    mut v_m_2699_: *mut LeanObject,
    mut v_inst_2700_: *mut LeanObject,
    mut v_inst_2701_: *mut LeanObject,
    mut v_inst_2702_: *mut LeanObject,
    mut v_declName_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ =
        l_Lean_isEnumType___redArg(v_inst_2700_, v_inst_2701_, v_inst_2702_, v_declName_2703_);
    return v___x_2704_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_MonadEnv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_AuxRecursor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_MonadEnv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_MonadEnv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_AuxRecursor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_Old(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_MonadEnv(builtin);
}
