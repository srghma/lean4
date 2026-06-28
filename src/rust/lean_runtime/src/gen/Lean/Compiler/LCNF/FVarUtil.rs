// Lean compiler output
// Module: Lean.Compiler.LCNF.FVarUtil
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::Option::{
    l_OptionT_bind, l_OptionT_instMonad___redArg___lam__1, l_OptionT_instMonad___redArg___lam__3,
    l_OptionT_instMonad___redArg___lam__6, l_OptionT_instMonad___redArg___lam__9,
    l_OptionT_instMonad___redArg___lam__11, l_OptionT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::BasicAux::l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go;
use crate::r#gen::Init::Prelude::{l_instInhabitedOfMonad___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp,
    l_Lean_Compiler_LCNF_Alt_forCodeM___redArg, l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_hasFVar, l_Lean_Expr_lam___override, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            69, 120, 112, 114, 46, 109, 97, 112, 70, 86, 97, 114, 77, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            70, 86, 97, 114, 85, 116, 105, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            69, 120, 112, 114, 46, 102, 111, 114, 70, 86, 97, 114, 77, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(
    mut v_toApplicative_3379_: *mut LeanObject,
    mut v_fvarId_3380_: *mut LeanObject,
    mut v_e_3381_: *mut LeanObject,
    mut v_____do__lift_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    v_toPure_3383_ = lean_ctor_get(v_toApplicative_3379_, 1);
    lean_inc(v_toPure_3383_);
    lean_dec_ref(v_toApplicative_3379_);
    v___x_3384_ = l_Lean_instBEqFVarId_beq(v_fvarId_3380_, v_____do__lift_3382_);
    if v___x_3384_ == 0 {
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_3381_);
        v___x_3385_ = l_Lean_Expr_fvar___override(v_____do__lift_3382_);
        v___x_3386_ = lean_apply_2(v_toPure_3383_, lean_box(0), v___x_3385_);
        return v___x_3386_;
    } else {
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_3382_);
        v___x_3387_ = lean_apply_2(v_toPure_3383_, lean_box(0), v_e_3381_);
        return v___x_3387_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(
    mut v_toApplicative_3388_: *mut LeanObject,
    mut v_fvarId_3389_: *mut LeanObject,
    mut v_e_3390_: *mut LeanObject,
    mut v_____do__lift_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3392_: *mut LeanObject = core::ptr::null_mut();
    v_res_3392_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(
        v_toApplicative_3388_,
        v_fvarId_3389_,
        v_e_3390_,
        v_____do__lift_3391_,
    );
    lean_dec(v_fvarId_3389_);
    return v_res_3392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(
    mut v_toApplicative_3393_: *mut LeanObject,
    mut v_____do__lift_3394_: *mut LeanObject,
    mut v_e_3395_: *mut LeanObject,
    mut v_fn_3396_: *mut LeanObject,
    mut v_arg_3397_: *mut LeanObject,
    mut v_____do__lift_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3401_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: usize = 0;
    let mut v___x_3409_: usize = 0;
    let mut v___x_3410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3399_ = lean_ctor_get(v_toApplicative_3393_, 1);
                lean_inc(v_toPure_3399_);
                lean_dec_ref(v_toApplicative_3393_);
                v___x_3405_ = lean_ptr_addr(v_fn_3396_);
                v___x_3406_ = lean_ptr_addr(v_____do__lift_3394_);
                v___x_3407_ = lean_usize_dec_eq(v___x_3405_, v___x_3406_);
                if v___x_3407_ == 0 {
                    v___y_3401_ = v___x_3407_;
                    state = 1;
                    continue;
                } else {
                    v___x_3408_ = lean_ptr_addr(v_arg_3397_);
                    v___x_3409_ = lean_ptr_addr(v_____do__lift_3398_);
                    v___x_3410_ = lean_usize_dec_eq(v___x_3408_, v___x_3409_);
                    v___y_3401_ = v___x_3410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3401_ == 0 {
                    lean_dec_ref(v_e_3395_);
                    v___x_3402_ =
                        l_Lean_Expr_app___override(v_____do__lift_3394_, v_____do__lift_3398_);
                    v___x_3403_ = lean_apply_2(v_toPure_3399_, lean_box(0), v___x_3402_);
                    return v___x_3403_;
                } else {
                    lean_dec_ref(v_____do__lift_3398_);
                    lean_dec_ref(v_____do__lift_3394_);
                    v___x_3404_ = lean_apply_2(v_toPure_3399_, lean_box(0), v_e_3395_);
                    return v___x_3404_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(
    mut v_toApplicative_3411_: *mut LeanObject,
    mut v_____do__lift_3412_: *mut LeanObject,
    mut v_e_3413_: *mut LeanObject,
    mut v_fn_3414_: *mut LeanObject,
    mut v_arg_3415_: *mut LeanObject,
    mut v_____do__lift_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3417_: *mut LeanObject = core::ptr::null_mut();
    v_res_3417_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(
        v_toApplicative_3411_,
        v_____do__lift_3412_,
        v_e_3413_,
        v_fn_3414_,
        v_arg_3415_,
        v_____do__lift_3416_,
    );
    lean_dec_ref(v_arg_3415_);
    lean_dec_ref(v_fn_3414_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(
    mut v_toApplicative_3418_: *mut LeanObject,
    mut v_binderName_3419_: *mut LeanObject,
    mut v_____do__lift_3420_: *mut LeanObject,
    mut v_binderInfo_3421_: u8,
    mut v_e_3422_: *mut LeanObject,
    mut v_binderType_3423_: *mut LeanObject,
    mut v_body_3424_: *mut LeanObject,
    mut v_____do__lift_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: usize = 0;
    let mut v___x_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3426_ = lean_ctor_get(v_toApplicative_3418_, 1);
                lean_inc(v_toPure_3426_);
                lean_dec_ref(v_toApplicative_3418_);
                v___x_3435_ = lean_ptr_addr(v_binderType_3423_);
                v___x_3436_ = lean_ptr_addr(v_____do__lift_3420_);
                v___x_3437_ = lean_usize_dec_eq(v___x_3435_, v___x_3436_);
                if v___x_3437_ == 0 {
                    v___y_3428_ = v___x_3437_;
                    state = 1;
                    continue;
                } else {
                    v___x_3438_ = lean_ptr_addr(v_body_3424_);
                    v___x_3439_ = lean_ptr_addr(v_____do__lift_3425_);
                    v___x_3440_ = lean_usize_dec_eq(v___x_3438_, v___x_3439_);
                    v___y_3428_ = v___x_3440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3428_ == 0 {
                    lean_dec_ref(v_e_3422_);
                    v___x_3429_ = l_Lean_Expr_lam___override(
                        v_binderName_3419_,
                        v_____do__lift_3420_,
                        v_____do__lift_3425_,
                        v_binderInfo_3421_,
                    );
                    v___x_3430_ = lean_apply_2(v_toPure_3426_, lean_box(0), v___x_3429_);
                    return v___x_3430_;
                } else {
                    v___x_3431_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3421_, v_binderInfo_3421_);
                    if v___x_3431_ == 0 {
                        lean_dec_ref(v_e_3422_);
                        v___x_3432_ = l_Lean_Expr_lam___override(
                            v_binderName_3419_,
                            v_____do__lift_3420_,
                            v_____do__lift_3425_,
                            v_binderInfo_3421_,
                        );
                        v___x_3433_ = lean_apply_2(v_toPure_3426_, lean_box(0), v___x_3432_);
                        return v___x_3433_;
                    } else {
                        lean_dec_ref(v_____do__lift_3425_);
                        lean_dec_ref(v_____do__lift_3420_);
                        lean_dec(v_binderName_3419_);
                        v___x_3434_ = lean_apply_2(v_toPure_3426_, lean_box(0), v_e_3422_);
                        return v___x_3434_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(
    mut v_toApplicative_3441_: *mut LeanObject,
    mut v_binderName_3442_: *mut LeanObject,
    mut v_____do__lift_3443_: *mut LeanObject,
    mut v_binderInfo_3444_: *mut LeanObject,
    mut v_e_3445_: *mut LeanObject,
    mut v_binderType_3446_: *mut LeanObject,
    mut v_body_3447_: *mut LeanObject,
    mut v_____do__lift_3448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1027__boxed_3449_: u8 = 0;
    let mut v_res_3450_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1027__boxed_3449_ = (lean_unbox(v_binderInfo_3444_) as u8);
    v_res_3450_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(
        v_toApplicative_3441_,
        v_binderName_3442_,
        v_____do__lift_3443_,
        v_binderInfo_1027__boxed_3449_,
        v_e_3445_,
        v_binderType_3446_,
        v_body_3447_,
        v_____do__lift_3448_,
    );
    lean_dec_ref(v_body_3447_);
    lean_dec_ref(v_binderType_3446_);
    return v_res_3450_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(
    mut v_toApplicative_3451_: *mut LeanObject,
    mut v_binderName_3452_: *mut LeanObject,
    mut v_____do__lift_3453_: *mut LeanObject,
    mut v_binderInfo_3454_: u8,
    mut v_e_3455_: *mut LeanObject,
    mut v_binderType_3456_: *mut LeanObject,
    mut v_body_3457_: *mut LeanObject,
    mut v_____do__lift_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: u8 = 0;
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: usize = 0;
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: usize = 0;
    let mut v___x_3472_: usize = 0;
    let mut v___x_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3459_ = lean_ctor_get(v_toApplicative_3451_, 1);
                lean_inc(v_toPure_3459_);
                lean_dec_ref(v_toApplicative_3451_);
                v___x_3468_ = lean_ptr_addr(v_binderType_3456_);
                v___x_3469_ = lean_ptr_addr(v_____do__lift_3453_);
                v___x_3470_ = lean_usize_dec_eq(v___x_3468_, v___x_3469_);
                if v___x_3470_ == 0 {
                    v___y_3461_ = v___x_3470_;
                    state = 1;
                    continue;
                } else {
                    v___x_3471_ = lean_ptr_addr(v_body_3457_);
                    v___x_3472_ = lean_ptr_addr(v_____do__lift_3458_);
                    v___x_3473_ = lean_usize_dec_eq(v___x_3471_, v___x_3472_);
                    v___y_3461_ = v___x_3473_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3461_ == 0 {
                    lean_dec_ref(v_e_3455_);
                    v___x_3462_ = l_Lean_Expr_forallE___override(
                        v_binderName_3452_,
                        v_____do__lift_3453_,
                        v_____do__lift_3458_,
                        v_binderInfo_3454_,
                    );
                    v___x_3463_ = lean_apply_2(v_toPure_3459_, lean_box(0), v___x_3462_);
                    return v___x_3463_;
                } else {
                    v___x_3464_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3454_, v_binderInfo_3454_);
                    if v___x_3464_ == 0 {
                        lean_dec_ref(v_e_3455_);
                        v___x_3465_ = l_Lean_Expr_forallE___override(
                            v_binderName_3452_,
                            v_____do__lift_3453_,
                            v_____do__lift_3458_,
                            v_binderInfo_3454_,
                        );
                        v___x_3466_ = lean_apply_2(v_toPure_3459_, lean_box(0), v___x_3465_);
                        return v___x_3466_;
                    } else {
                        lean_dec_ref(v_____do__lift_3458_);
                        lean_dec_ref(v_____do__lift_3453_);
                        lean_dec(v_binderName_3452_);
                        v___x_3467_ = lean_apply_2(v_toPure_3459_, lean_box(0), v_e_3455_);
                        return v___x_3467_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(
    mut v_toApplicative_3474_: *mut LeanObject,
    mut v_binderName_3475_: *mut LeanObject,
    mut v_____do__lift_3476_: *mut LeanObject,
    mut v_binderInfo_3477_: *mut LeanObject,
    mut v_e_3478_: *mut LeanObject,
    mut v_binderType_3479_: *mut LeanObject,
    mut v_body_3480_: *mut LeanObject,
    mut v_____do__lift_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1073__boxed_3482_: u8 = 0;
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1073__boxed_3482_ = (lean_unbox(v_binderInfo_3477_) as u8);
    v_res_3483_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(
        v_toApplicative_3474_,
        v_binderName_3475_,
        v_____do__lift_3476_,
        v_binderInfo_1073__boxed_3482_,
        v_e_3478_,
        v_binderType_3479_,
        v_body_3480_,
        v_____do__lift_3481_,
    );
    lean_dec_ref(v_body_3480_);
    lean_dec_ref(v_binderType_3479_);
    return v_res_3483_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2;
    v___x_3488_ = lean_unsigned_to_nat(41);
    v___x_3489_ = lean_unsigned_to_nat(30);
    v___x_3490_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1;
    v___x_3491_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0;
    v___x_3492_ = l_mkPanicMessageWithDecl(
        v___x_3491_,
        v___x_3490_,
        v___x_3489_,
        v___x_3488_,
        v___x_3487_,
    );
    return v___x_3492_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(
    mut v_toApplicative_3493_: *mut LeanObject,
    mut v_binderName_3494_: *mut LeanObject,
    mut v_binderInfo_3495_: u8,
    mut v_e_3496_: *mut LeanObject,
    mut v_binderType_3497_: *mut LeanObject,
    mut v_body_3498_: *mut LeanObject,
    mut v_inst_3499_: *mut LeanObject,
    mut v_f_3500_: *mut LeanObject,
    mut v_toBind_3501_: *mut LeanObject,
    mut v_____do__lift_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3503_ = lean_box((v_binderInfo_3495_) as usize);
    lean_inc_ref(v_body_3498_);
    v___f_3504_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_3504_, 0, v_toApplicative_3493_);
    lean_closure_set(v___f_3504_, 1, v_binderName_3494_);
    lean_closure_set(v___f_3504_, 2, v_____do__lift_3502_);
    lean_closure_set(v___f_3504_, 3, v___x_3503_);
    lean_closure_set(v___f_3504_, 4, v_e_3496_);
    lean_closure_set(v___f_3504_, 5, v_binderType_3497_);
    lean_closure_set(v___f_3504_, 6, v_body_3498_);
    v___x_3505_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3499_, v_f_3500_, v_body_3498_);
    v___x_3506_ = lean_apply_4(
        v_toBind_3501_,
        lean_box(0),
        lean_box(0),
        v___x_3505_,
        v___f_3504_,
    );
    return v___x_3506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(
    mut v_toApplicative_3507_: *mut LeanObject,
    mut v_binderName_3508_: *mut LeanObject,
    mut v_binderInfo_3509_: *mut LeanObject,
    mut v_e_3510_: *mut LeanObject,
    mut v_binderType_3511_: *mut LeanObject,
    mut v_body_3512_: *mut LeanObject,
    mut v_inst_3513_: *mut LeanObject,
    mut v_f_3514_: *mut LeanObject,
    mut v_toBind_3515_: *mut LeanObject,
    mut v_____do__lift_3516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1152__boxed_3517_: u8 = 0;
    let mut v_res_3518_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1152__boxed_3517_ = (lean_unbox(v_binderInfo_3509_) as u8);
    v_res_3518_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(
        v_toApplicative_3507_,
        v_binderName_3508_,
        v_binderInfo_1152__boxed_3517_,
        v_e_3510_,
        v_binderType_3511_,
        v_body_3512_,
        v_inst_3513_,
        v_f_3514_,
        v_toBind_3515_,
        v_____do__lift_3516_,
    );
    return v_res_3518_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(
    mut v_toApplicative_3519_: *mut LeanObject,
    mut v_binderName_3520_: *mut LeanObject,
    mut v_binderInfo_3521_: u8,
    mut v_e_3522_: *mut LeanObject,
    mut v_binderType_3523_: *mut LeanObject,
    mut v_body_3524_: *mut LeanObject,
    mut v_inst_3525_: *mut LeanObject,
    mut v_f_3526_: *mut LeanObject,
    mut v_toBind_3527_: *mut LeanObject,
    mut v_____do__lift_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    v___x_3529_ = lean_box((v_binderInfo_3521_) as usize);
    lean_inc_ref(v_body_3524_);
    v___f_3530_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_3530_, 0, v_toApplicative_3519_);
    lean_closure_set(v___f_3530_, 1, v_binderName_3520_);
    lean_closure_set(v___f_3530_, 2, v_____do__lift_3528_);
    lean_closure_set(v___f_3530_, 3, v___x_3529_);
    lean_closure_set(v___f_3530_, 4, v_e_3522_);
    lean_closure_set(v___f_3530_, 5, v_binderType_3523_);
    lean_closure_set(v___f_3530_, 6, v_body_3524_);
    v___x_3531_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3525_, v_f_3526_, v_body_3524_);
    v___x_3532_ = lean_apply_4(
        v_toBind_3527_,
        lean_box(0),
        lean_box(0),
        v___x_3531_,
        v___f_3530_,
    );
    return v___x_3532_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(
    mut v_toApplicative_3533_: *mut LeanObject,
    mut v_binderName_3534_: *mut LeanObject,
    mut v_binderInfo_3535_: *mut LeanObject,
    mut v_e_3536_: *mut LeanObject,
    mut v_binderType_3537_: *mut LeanObject,
    mut v_body_3538_: *mut LeanObject,
    mut v_inst_3539_: *mut LeanObject,
    mut v_f_3540_: *mut LeanObject,
    mut v_toBind_3541_: *mut LeanObject,
    mut v_____do__lift_3542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1161__boxed_3543_: u8 = 0;
    let mut v_res_3544_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1161__boxed_3543_ = (lean_unbox(v_binderInfo_3535_) as u8);
    v_res_3544_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(
        v_toApplicative_3533_,
        v_binderName_3534_,
        v_binderInfo_1161__boxed_3543_,
        v_e_3536_,
        v_binderType_3537_,
        v_body_3538_,
        v_inst_3539_,
        v_f_3540_,
        v_toBind_3541_,
        v_____do__lift_3542_,
    );
    return v_res_3544_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
    mut v_inst_3545_: *mut LeanObject,
    mut v_f_3546_: *mut LeanObject,
    mut v_e_3547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3548_: u8 = 0;
    v___x_3548_ = l_Lean_Expr_hasFVar(v_e_3547_);
    if v___x_3548_ == 0 {
        let mut v_toApplicative_3549_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_3550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_3546_);
        v_toApplicative_3549_ = lean_ctor_get(v_inst_3545_, 0);
        lean_inc_ref(v_toApplicative_3549_);
        lean_dec_ref(v_inst_3545_);
        v_toPure_3550_ = lean_ctor_get(v_toApplicative_3549_, 1);
        lean_inc(v_toPure_3550_);
        lean_dec_ref(v_toApplicative_3549_);
        v___x_3551_ = lean_apply_2(v_toPure_3550_, lean_box(0), v_e_3547_);
        return v___x_3551_;
    } else {
        match lean_obj_tag(v_e_3547_) {
            1 => {
                let mut v_fvarId_3552_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toApplicative_3553_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toBind_3554_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_3555_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
                v_fvarId_3552_ = lean_ctor_get(v_e_3547_, 0);
                lean_inc_n(v_fvarId_3552_, 2);
                v_toApplicative_3553_ = lean_ctor_get(v_inst_3545_, 0);
                lean_inc_ref(v_toApplicative_3553_);
                v_toBind_3554_ = lean_ctor_get(v_inst_3545_, 1);
                lean_inc(v_toBind_3554_);
                lean_dec_ref(v_inst_3545_);
                v___f_3555_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3555_, 0, v_toApplicative_3553_);
                lean_closure_set(v___f_3555_, 1, v_fvarId_3552_);
                lean_closure_set(v___f_3555_, 2, v_e_3547_);
                v___x_3556_ = lean_apply_1(v_f_3546_, v_fvarId_3552_);
                v___x_3557_ = lean_apply_4(
                    v_toBind_3554_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3556_,
                    v___f_3555_,
                );
                return v___x_3557_;
            }
            2 => {
                let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_e_3547_, 1);
                lean_dec(v_f_3546_);
                v___x_3558_ = l_Lean_instInhabitedExpr;
                v___x_3559_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3558_);
                v___x_3560_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3561_ = l_panic___redArg(v___x_3559_, v___x_3560_);
                lean_dec(v___x_3559_);
                return v___x_3561_;
            }
            5 => {
                let mut v_fn_3562_: *mut LeanObject = core::ptr::null_mut();
                let mut v_arg_3563_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toApplicative_3564_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toBind_3565_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_3566_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
                v_fn_3562_ = lean_ctor_get(v_e_3547_, 0);
                lean_inc_ref_n(v_fn_3562_, 2);
                v_arg_3563_ = lean_ctor_get(v_e_3547_, 1);
                lean_inc_ref(v_arg_3563_);
                v_toApplicative_3564_ = lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3565_ = lean_ctor_get(v_inst_3545_, 1);
                lean_inc_n(v_toBind_3565_, 2);
                lean_inc(v_f_3546_);
                lean_inc_ref(v_inst_3545_);
                lean_inc_ref(v_toApplicative_3564_);
                v___f_3566_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_3566_, 0, v_toApplicative_3564_);
                lean_closure_set(v___f_3566_, 1, v_e_3547_);
                lean_closure_set(v___f_3566_, 2, v_fn_3562_);
                lean_closure_set(v___f_3566_, 3, v_arg_3563_);
                lean_closure_set(v___f_3566_, 4, v_inst_3545_);
                lean_closure_set(v___f_3566_, 5, v_f_3546_);
                lean_closure_set(v___f_3566_, 6, v_toBind_3565_);
                v___x_3567_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_fn_3562_,
                );
                v___x_3568_ = lean_apply_4(
                    v_toBind_3565_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3567_,
                    v___f_3566_,
                );
                return v___x_3568_;
            }
            6 => {
                let mut v_binderName_3569_: *mut LeanObject = core::ptr::null_mut();
                let mut v_binderType_3570_: *mut LeanObject = core::ptr::null_mut();
                let mut v_body_3571_: *mut LeanObject = core::ptr::null_mut();
                let mut v_binderInfo_3572_: u8 = 0;
                let mut v_toApplicative_3573_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toBind_3574_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_3576_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
                v_binderName_3569_ = lean_ctor_get(v_e_3547_, 0);
                lean_inc(v_binderName_3569_);
                v_binderType_3570_ = lean_ctor_get(v_e_3547_, 1);
                lean_inc_ref_n(v_binderType_3570_, 2);
                v_body_3571_ = lean_ctor_get(v_e_3547_, 2);
                lean_inc_ref(v_body_3571_);
                v_binderInfo_3572_ = lean_ctor_get_uint8(
                    v_e_3547_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                );
                v_toApplicative_3573_ = lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3574_ = lean_ctor_get(v_inst_3545_, 1);
                lean_inc_n(v_toBind_3574_, 2);
                v___x_3575_ = lean_box((v_binderInfo_3572_) as usize);
                lean_inc(v_f_3546_);
                lean_inc_ref(v_inst_3545_);
                lean_inc_ref(v_toApplicative_3573_);
                v___f_3576_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                lean_closure_set(v___f_3576_, 0, v_toApplicative_3573_);
                lean_closure_set(v___f_3576_, 1, v_binderName_3569_);
                lean_closure_set(v___f_3576_, 2, v___x_3575_);
                lean_closure_set(v___f_3576_, 3, v_e_3547_);
                lean_closure_set(v___f_3576_, 4, v_binderType_3570_);
                lean_closure_set(v___f_3576_, 5, v_body_3571_);
                lean_closure_set(v___f_3576_, 6, v_inst_3545_);
                lean_closure_set(v___f_3576_, 7, v_f_3546_);
                lean_closure_set(v___f_3576_, 8, v_toBind_3574_);
                v___x_3577_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_binderType_3570_,
                );
                v___x_3578_ = lean_apply_4(
                    v_toBind_3574_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3577_,
                    v___f_3576_,
                );
                return v___x_3578_;
            }
            7 => {
                let mut v_binderName_3579_: *mut LeanObject = core::ptr::null_mut();
                let mut v_binderType_3580_: *mut LeanObject = core::ptr::null_mut();
                let mut v_body_3581_: *mut LeanObject = core::ptr::null_mut();
                let mut v_binderInfo_3582_: u8 = 0;
                let mut v_toApplicative_3583_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toBind_3584_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_3586_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
                v_binderName_3579_ = lean_ctor_get(v_e_3547_, 0);
                lean_inc(v_binderName_3579_);
                v_binderType_3580_ = lean_ctor_get(v_e_3547_, 1);
                lean_inc_ref_n(v_binderType_3580_, 2);
                v_body_3581_ = lean_ctor_get(v_e_3547_, 2);
                lean_inc_ref(v_body_3581_);
                v_binderInfo_3582_ = lean_ctor_get_uint8(
                    v_e_3547_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                );
                v_toApplicative_3583_ = lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3584_ = lean_ctor_get(v_inst_3545_, 1);
                lean_inc_n(v_toBind_3584_, 2);
                v___x_3585_ = lean_box((v_binderInfo_3582_) as usize);
                lean_inc(v_f_3546_);
                lean_inc_ref(v_inst_3545_);
                lean_inc_ref(v_toApplicative_3583_);
                v___f_3586_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                lean_closure_set(v___f_3586_, 0, v_toApplicative_3583_);
                lean_closure_set(v___f_3586_, 1, v_binderName_3579_);
                lean_closure_set(v___f_3586_, 2, v___x_3585_);
                lean_closure_set(v___f_3586_, 3, v_e_3547_);
                lean_closure_set(v___f_3586_, 4, v_binderType_3580_);
                lean_closure_set(v___f_3586_, 5, v_body_3581_);
                lean_closure_set(v___f_3586_, 6, v_inst_3545_);
                lean_closure_set(v___f_3586_, 7, v_f_3546_);
                lean_closure_set(v___f_3586_, 8, v_toBind_3584_);
                v___x_3587_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_binderType_3580_,
                );
                v___x_3588_ = lean_apply_4(
                    v_toBind_3584_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3587_,
                    v___f_3586_,
                );
                return v___x_3588_;
            }
            8 => {
                let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_e_3547_, 4);
                lean_dec(v_f_3546_);
                v___x_3589_ = l_Lean_instInhabitedExpr;
                v___x_3590_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3589_);
                v___x_3591_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3592_ = l_panic___redArg(v___x_3590_, v___x_3591_);
                lean_dec(v___x_3590_);
                return v___x_3592_;
            }
            11 => {
                let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_e_3547_, 3);
                lean_dec(v_f_3546_);
                v___x_3593_ = l_Lean_instInhabitedExpr;
                v___x_3594_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3593_);
                v___x_3595_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3596_ = l_panic___redArg(v___x_3594_, v___x_3595_);
                lean_dec(v___x_3594_);
                return v___x_3596_;
            }
            _ => {
                let mut v_toApplicative_3597_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_3598_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_f_3546_);
                v_toApplicative_3597_ = lean_ctor_get(v_inst_3545_, 0);
                lean_inc_ref(v_toApplicative_3597_);
                lean_dec_ref(v_inst_3545_);
                v_toPure_3598_ = lean_ctor_get(v_toApplicative_3597_, 1);
                lean_inc(v_toPure_3598_);
                lean_dec_ref(v_toApplicative_3597_);
                v___x_3599_ = lean_apply_2(v_toPure_3598_, lean_box(0), v_e_3547_);
                return v___x_3599_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(
    mut v_toApplicative_3600_: *mut LeanObject,
    mut v_e_3601_: *mut LeanObject,
    mut v_fn_3602_: *mut LeanObject,
    mut v_arg_3603_: *mut LeanObject,
    mut v_inst_3604_: *mut LeanObject,
    mut v_f_3605_: *mut LeanObject,
    mut v_toBind_3606_: *mut LeanObject,
    mut v_____do__lift_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_arg_3603_);
    v___f_3608_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3608_, 0, v_toApplicative_3600_);
    lean_closure_set(v___f_3608_, 1, v_____do__lift_3607_);
    lean_closure_set(v___f_3608_, 2, v_e_3601_);
    lean_closure_set(v___f_3608_, 3, v_fn_3602_);
    lean_closure_set(v___f_3608_, 4, v_arg_3603_);
    v___x_3609_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3604_, v_f_3605_, v_arg_3603_);
    v___x_3610_ = lean_apply_4(
        v_toBind_3606_,
        lean_box(0),
        lean_box(0),
        v___x_3609_,
        v___f_3608_,
    );
    return v___x_3610_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM(
    mut v_m_3611_: *mut LeanObject,
    mut v_inst_3612_: *mut LeanObject,
    mut v_inst_3613_: *mut LeanObject,
    mut v_f_3614_: *mut LeanObject,
    mut v_e_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    v___x_3616_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3613_, v_f_3614_, v_e_3615_);
    return v___x_3616_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(
    mut v_m_3617_: *mut LeanObject,
    mut v_inst_3618_: *mut LeanObject,
    mut v_inst_3619_: *mut LeanObject,
    mut v_f_3620_: *mut LeanObject,
    mut v_e_3621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3622_: *mut LeanObject = core::ptr::null_mut();
    v_res_3622_ = l_Lean_Compiler_LCNF_Expr_mapFVarM(
        v_m_3617_,
        v_inst_3618_,
        v_inst_3619_,
        v_f_3620_,
        v_e_3621_,
    );
    lean_dec(v_inst_3618_);
    return v_res_3622_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    v___x_3624_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2;
    v___x_3625_ = lean_unsigned_to_nat(40);
    v___x_3626_ = lean_unsigned_to_nat(49);
    v___x_3627_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0;
    v___x_3628_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0;
    v___x_3629_ = l_mkPanicMessageWithDecl(
        v___x_3628_,
        v___x_3627_,
        v___x_3626_,
        v___x_3625_,
        v___x_3624_,
    );
    return v___x_3629_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(
    mut v_inst_3630_: *mut LeanObject,
    mut v_f_3631_: *mut LeanObject,
    mut v_arg_3632_: *mut LeanObject,
    mut v_____r_3633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    v___x_3634_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3630_, v_f_3631_, v_arg_3632_);
    return v___x_3634_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
    mut v_inst_3635_: *mut LeanObject,
    mut v_f_3636_: *mut LeanObject,
    mut v_e_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: u8 = 0;
    let mut v_toApplicative_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3645_ = l_Lean_Expr_hasFVar(v_e_3637_);
                if v___x_3645_ == 0 {
                    lean_dec_ref(v_e_3637_);
                    lean_dec(v_f_3636_);
                    v_toApplicative_3646_ = lean_ctor_get(v_inst_3635_, 0);
                    lean_inc_ref(v_toApplicative_3646_);
                    lean_dec_ref(v_inst_3635_);
                    v_toPure_3647_ = lean_ctor_get(v_toApplicative_3646_, 1);
                    lean_inc(v_toPure_3647_);
                    lean_dec_ref(v_toApplicative_3646_);
                    v___x_3648_ = lean_box(0);
                    v___x_3649_ = lean_apply_2(v_toPure_3647_, lean_box(0), v___x_3648_);
                    return v___x_3649_;
                } else {
                    match lean_obj_tag(v_e_3637_) {
                        1 => {
                            lean_dec_ref(v_inst_3635_);
                            v_fvarId_3650_ = lean_ctor_get(v_e_3637_, 0);
                            lean_inc(v_fvarId_3650_);
                            lean_dec_ref_known(v_e_3637_, 1);
                            v___x_3651_ = lean_apply_1(v_f_3636_, v_fvarId_3650_);
                            return v___x_3651_;
                        }
                        2 => {
                            lean_dec_ref_known(v_e_3637_, 1);
                            lean_dec(v_f_3636_);
                            v___x_3652_ = lean_box(0);
                            v___x_3653_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3652_);
                            v___x_3654_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3655_ = l_panic___redArg(v___x_3653_, v___x_3654_);
                            lean_dec(v___x_3653_);
                            return v___x_3655_;
                        }
                        5 => {
                            v_fn_3656_ = lean_ctor_get(v_e_3637_, 0);
                            lean_inc_ref(v_fn_3656_);
                            v_arg_3657_ = lean_ctor_get(v_e_3637_, 1);
                            lean_inc_ref(v_arg_3657_);
                            lean_dec_ref_known(v_e_3637_, 2);
                            v_toBind_3658_ = lean_ctor_get(v_inst_3635_, 1);
                            lean_inc(v_toBind_3658_);
                            lean_inc(v_f_3636_);
                            lean_inc_ref(v_inst_3635_);
                            v___f_3659_ = lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            lean_closure_set(v___f_3659_, 0, v_inst_3635_);
                            lean_closure_set(v___f_3659_, 1, v_f_3636_);
                            lean_closure_set(v___f_3659_, 2, v_arg_3657_);
                            v___x_3660_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                                v_inst_3635_,
                                v_f_3636_,
                                v_fn_3656_,
                            );
                            v___x_3661_ = lean_apply_4(
                                v_toBind_3658_,
                                lean_box(0),
                                lean_box(0),
                                v___x_3660_,
                                v___f_3659_,
                            );
                            return v___x_3661_;
                        }
                        6 => {
                            v_binderType_3662_ = lean_ctor_get(v_e_3637_, 1);
                            lean_inc_ref(v_binderType_3662_);
                            v_body_3663_ = lean_ctor_get(v_e_3637_, 2);
                            lean_inc_ref(v_body_3663_);
                            lean_dec_ref_known(v_e_3637_, 3);
                            v_ty_3639_ = v_binderType_3662_;
                            v_body_3640_ = v_body_3663_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_3664_ = lean_ctor_get(v_e_3637_, 1);
                            lean_inc_ref(v_binderType_3664_);
                            v_body_3665_ = lean_ctor_get(v_e_3637_, 2);
                            lean_inc_ref(v_body_3665_);
                            lean_dec_ref_known(v_e_3637_, 3);
                            v_ty_3639_ = v_binderType_3664_;
                            v_body_3640_ = v_body_3665_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            lean_dec_ref_known(v_e_3637_, 4);
                            lean_dec(v_f_3636_);
                            v___x_3666_ = lean_box(0);
                            v___x_3667_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3666_);
                            v___x_3668_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3669_ = l_panic___redArg(v___x_3667_, v___x_3668_);
                            lean_dec(v___x_3667_);
                            return v___x_3669_;
                        }
                        11 => {
                            lean_dec_ref_known(v_e_3637_, 3);
                            lean_dec(v_f_3636_);
                            v___x_3670_ = lean_box(0);
                            v___x_3671_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3670_);
                            v___x_3672_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3673_ = l_panic___redArg(v___x_3671_, v___x_3672_);
                            lean_dec(v___x_3671_);
                            return v___x_3673_;
                        }
                        _ => {
                            lean_dec_ref(v_e_3637_);
                            lean_dec(v_f_3636_);
                            v_toApplicative_3674_ = lean_ctor_get(v_inst_3635_, 0);
                            lean_inc_ref(v_toApplicative_3674_);
                            lean_dec_ref(v_inst_3635_);
                            v_toPure_3675_ = lean_ctor_get(v_toApplicative_3674_, 1);
                            lean_inc(v_toPure_3675_);
                            lean_dec_ref(v_toApplicative_3674_);
                            v___x_3676_ = lean_box(0);
                            v___x_3677_ = lean_apply_2(v_toPure_3675_, lean_box(0), v___x_3676_);
                            return v___x_3677_;
                        }
                    }
                }
            }
            1 => {
                v_toBind_3641_ = lean_ctor_get(v_inst_3635_, 1);
                lean_inc(v_toBind_3641_);
                lean_inc(v_f_3636_);
                lean_inc_ref(v_inst_3635_);
                v___f_3642_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3642_, 0, v_inst_3635_);
                lean_closure_set(v___f_3642_, 1, v_f_3636_);
                lean_closure_set(v___f_3642_, 2, v_body_3640_);
                v___x_3643_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                    v_inst_3635_,
                    v_f_3636_,
                    v_ty_3639_,
                );
                v___x_3644_ = lean_apply_4(
                    v_toBind_3641_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3643_,
                    v___f_3642_,
                );
                return v___x_3644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(
    mut v_inst_3678_: *mut LeanObject,
    mut v_f_3679_: *mut LeanObject,
    mut v_body_3680_: *mut LeanObject,
    mut v_____r_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    v___x_3682_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3678_, v_f_3679_, v_body_3680_);
    return v___x_3682_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM(
    mut v_m_3683_: *mut LeanObject,
    mut v_inst_3684_: *mut LeanObject,
    mut v_f_3685_: *mut LeanObject,
    mut v_e_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3684_, v_f_3685_, v_e_3686_);
    return v___x_3687_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(
    mut v_m_3688_: *mut LeanObject,
    mut v_inst_3689_: *mut LeanObject,
    mut v_inst_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    v___x_3693_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3690_, v___y_3691_, v___y_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(
    mut v_m_3694_: *mut LeanObject,
    mut v_inst_3695_: *mut LeanObject,
    mut v_inst_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3699_: *mut LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(
        v_m_3694_,
        v_inst_3695_,
        v_inst_3696_,
        v___y_3697_,
        v___y_3698_,
    );
    lean_dec(v_inst_3695_);
    return v_res_3699_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(
    mut v_m_3700_: *mut LeanObject,
    mut v_inst_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    v___x_3704_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3701_, v___y_3702_, v___y_3703_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(
    mut v_arg_3711_: *mut LeanObject,
    mut v_toPure_3712_: *mut LeanObject,
    mut v_____do__lift_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    v___x_3714_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(
            v_arg_3711_,
            v_____do__lift_3713_,
        );
    v___x_3715_ = lean_apply_2(v_toPure_3712_, lean_box(0), v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(
    mut v_pu_3716_: u8,
    mut v_arg_3717_: *mut LeanObject,
    mut v_toPure_3718_: *mut LeanObject,
    mut v_____do__lift_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(
        v_pu_3716_,
        v_arg_3717_,
        v_____do__lift_3719_,
    );
    v___x_3721_ = lean_apply_2(v_toPure_3718_, lean_box(0), v___x_3720_);
    return v___x_3721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_3722_: *mut LeanObject,
    mut v_arg_3723_: *mut LeanObject,
    mut v_toPure_3724_: *mut LeanObject,
    mut v_____do__lift_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3726_: u8 = 0;
    let mut v_res_3727_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3726_ = (lean_unbox(v_pu_3722_) as u8);
    v_res_3727_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(
        v_pu_boxed_3726_,
        v_arg_3723_,
        v_toPure_3724_,
        v_____do__lift_3725_,
    );
    return v_res_3727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
    mut v_pu_3728_: u8,
    mut v_inst_3729_: *mut LeanObject,
    mut v_f_3730_: *mut LeanObject,
    mut v_arg_3731_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_arg_3731_) {
        0 => {
            let mut v_toApplicative_3732_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3733_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3732_ = lean_ctor_get(v_inst_3729_, 0);
            lean_inc_ref(v_toApplicative_3732_);
            lean_dec(v_f_3730_);
            lean_dec_ref(v_inst_3729_);
            v_toPure_3733_ = lean_ctor_get(v_toApplicative_3732_, 1);
            lean_inc(v_toPure_3733_);
            lean_dec_ref(v_toApplicative_3732_);
            v___x_3734_ = lean_box(0);
            v___x_3735_ = lean_apply_2(v_toPure_3733_, lean_box(0), v___x_3734_);
            return v___x_3735_;
        }
        1 => {
            let mut v_toApplicative_3736_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3737_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3738_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_3739_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3740_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3736_ = lean_ctor_get(v_inst_3729_, 0);
            lean_inc_ref(v_toApplicative_3736_);
            v_toBind_3737_ = lean_ctor_get(v_inst_3729_, 1);
            lean_inc(v_toBind_3737_);
            lean_dec_ref(v_inst_3729_);
            v_toPure_3738_ = lean_ctor_get(v_toApplicative_3736_, 1);
            lean_inc(v_toPure_3738_);
            lean_dec_ref(v_toApplicative_3736_);
            v_fvarId_3739_ = lean_ctor_get(v_arg_3731_, 0);
            lean_inc(v_fvarId_3739_);
            v___f_3740_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_3740_, 0, v_arg_3731_);
            lean_closure_set(v___f_3740_, 1, v_toPure_3738_);
            v___x_3741_ = lean_apply_1(v_f_3730_, v_fvarId_3739_);
            v___x_3742_ = lean_apply_4(
                v_toBind_3737_,
                lean_box(0),
                lean_box(0),
                v___x_3741_,
                v___f_3740_,
            );
            return v___x_3742_;
        }
        _ => {
            let mut v_toApplicative_3743_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3744_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3745_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_3746_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3743_ = lean_ctor_get(v_inst_3729_, 0);
            v_toBind_3744_ = lean_ctor_get(v_inst_3729_, 1);
            lean_inc(v_toBind_3744_);
            v_toPure_3745_ = lean_ctor_get(v_toApplicative_3743_, 1);
            v_expr_3746_ = lean_ctor_get(v_arg_3731_, 0);
            lean_inc_ref(v_expr_3746_);
            v___x_3747_ = lean_box((v_pu_3728_) as usize);
            lean_inc(v_toPure_3745_);
            v___f_3748_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_3748_, 0, v___x_3747_);
            lean_closure_set(v___f_3748_, 1, v_arg_3731_);
            lean_closure_set(v___f_3748_, 2, v_toPure_3745_);
            v___x_3749_ =
                l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3729_, v_f_3730_, v_expr_3746_);
            v___x_3750_ = lean_apply_4(
                v_toBind_3744_,
                lean_box(0),
                lean_box(0),
                v___x_3749_,
                v___f_3748_,
            );
            return v___x_3750_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(
    mut v_pu_3751_: *mut LeanObject,
    mut v_inst_3752_: *mut LeanObject,
    mut v_f_3753_: *mut LeanObject,
    mut v_arg_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3755_: u8 = 0;
    let mut v_res_3756_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3755_ = (lean_unbox(v_pu_3751_) as u8);
    v_res_3756_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_boxed_3755_,
        v_inst_3752_,
        v_f_3753_,
        v_arg_3754_,
    );
    return v_res_3756_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM(
    mut v_m_3757_: *mut LeanObject,
    mut v_pu_3758_: u8,
    mut v_inst_3759_: *mut LeanObject,
    mut v_inst_3760_: *mut LeanObject,
    mut v_f_3761_: *mut LeanObject,
    mut v_arg_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    v___x_3763_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3758_,
        v_inst_3760_,
        v_f_3761_,
        v_arg_3762_,
    );
    return v___x_3763_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(
    mut v_m_3764_: *mut LeanObject,
    mut v_pu_3765_: *mut LeanObject,
    mut v_inst_3766_: *mut LeanObject,
    mut v_inst_3767_: *mut LeanObject,
    mut v_f_3768_: *mut LeanObject,
    mut v_arg_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3770_: u8 = 0;
    let mut v_res_3771_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3770_ = (lean_unbox(v_pu_3765_) as u8);
    v_res_3771_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(
        v_m_3764_,
        v_pu_boxed_3770_,
        v_inst_3766_,
        v_inst_3767_,
        v_f_3768_,
        v_arg_3769_,
    );
    lean_dec(v_inst_3766_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(
    mut v_inst_3772_: *mut LeanObject,
    mut v_f_3773_: *mut LeanObject,
    mut v_arg_3774_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_arg_3774_) {
        0 => {
            let mut v_toApplicative_3775_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3776_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3775_ = lean_ctor_get(v_inst_3772_, 0);
            lean_inc_ref(v_toApplicative_3775_);
            lean_dec(v_f_3773_);
            lean_dec_ref(v_inst_3772_);
            v_toPure_3776_ = lean_ctor_get(v_toApplicative_3775_, 1);
            lean_inc(v_toPure_3776_);
            lean_dec_ref(v_toApplicative_3775_);
            v___x_3777_ = lean_box(0);
            v___x_3778_ = lean_apply_2(v_toPure_3776_, lean_box(0), v___x_3777_);
            return v___x_3778_;
        }
        1 => {
            let mut v_fvarId_3779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_3772_);
            v_fvarId_3779_ = lean_ctor_get(v_arg_3774_, 0);
            lean_inc(v_fvarId_3779_);
            lean_dec_ref_known(v_arg_3774_, 1);
            v___x_3780_ = lean_apply_1(v_f_3773_, v_fvarId_3779_);
            return v___x_3780_;
        }
        _ => {
            let mut v_expr_3781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
            v_expr_3781_ = lean_ctor_get(v_arg_3774_, 0);
            lean_inc_ref(v_expr_3781_);
            lean_dec_ref_known(v_arg_3774_, 1);
            v___x_3782_ =
                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3772_, v_f_3773_, v_expr_3781_);
            return v___x_3782_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM(
    mut v_m_3783_: *mut LeanObject,
    mut v_pu_3784_: u8,
    mut v_inst_3785_: *mut LeanObject,
    mut v_f_3786_: *mut LeanObject,
    mut v_arg_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    v___x_3788_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_3785_, v_f_3786_, v_arg_3787_);
    return v___x_3788_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(
    mut v_m_3789_: *mut LeanObject,
    mut v_pu_3790_: *mut LeanObject,
    mut v_inst_3791_: *mut LeanObject,
    mut v_f_3792_: *mut LeanObject,
    mut v_arg_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3794_: u8 = 0;
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3794_ = (lean_unbox(v_pu_3790_) as u8);
    v_res_3795_ = l_Lean_Compiler_LCNF_Arg_forFVarM(
        v_m_3789_,
        v_pu_boxed_3794_,
        v_inst_3791_,
        v_f_3792_,
        v_arg_3793_,
    );
    return v_res_3795_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(
    mut v_pu_3796_: u8,
    mut v_m_3797_: *mut LeanObject,
    mut v_inst_3798_: *mut LeanObject,
    mut v_inst_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3796_,
        v_inst_3799_,
        v___y_3800_,
        v___y_3801_,
    );
    return v___x_3802_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(
    mut v_pu_3803_: *mut LeanObject,
    mut v_m_3804_: *mut LeanObject,
    mut v_inst_3805_: *mut LeanObject,
    mut v_inst_3806_: *mut LeanObject,
    mut v___y_3807_: *mut LeanObject,
    mut v___y_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3809_: u8 = 0;
    let mut v_res_3810_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3809_ = (lean_unbox(v_pu_3803_) as u8);
    v_res_3810_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(
        v_pu_boxed_3809_,
        v_m_3804_,
        v_inst_3805_,
        v_inst_3806_,
        v___y_3807_,
        v___y_3808_,
    );
    lean_dec(v_inst_3805_);
    return v_res_3810_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(
    mut v_m_3811_: *mut LeanObject,
    mut v_inst_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v___x_3815_ =
        l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_3812_, v___y_3813_, v___y_3814_);
    return v___x_3815_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg(mut v_pu_3817_: u8) -> *mut LeanObject {
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    v___x_3818_ = lean_box((v_pu_3817_) as usize);
    v___f_3819_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3819_, 0, v___x_3818_);
    v___f_3820_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0;
    v___x_3821_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3821_, 0, v___f_3819_);
    lean_ctor_set(v___x_3821_, 1, v___f_3820_);
    return v___x_3821_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(
    mut v_pu_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3823_: u8 = 0;
    let mut v_res_3824_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3823_ = (lean_unbox(v_pu_3822_) as u8);
    v_res_3824_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_boxed_3823_);
    return v_res_3824_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(
    mut v_pu_3825_: u8,
    mut v_inst_3826_: *mut LeanObject,
    mut v_f_3827_: *mut LeanObject,
    mut v___y_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3829_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3825_,
        v_inst_3826_,
        v_f_3827_,
        v___y_3828_,
    );
    return v___x_3829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_3830_: *mut LeanObject,
    mut v_inst_3831_: *mut LeanObject,
    mut v_f_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3834_: u8 = 0;
    let mut v_res_3835_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3834_ = (lean_unbox(v_pu_3830_) as u8);
    v_res_3835_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(
        v_pu_boxed_3834_,
        v_inst_3831_,
        v_f_3832_,
        v___y_3833_,
    );
    return v_res_3835_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(
    mut v_pu_3836_: u8,
    mut v_e_3837_: *mut LeanObject,
    mut v_toPure_3838_: *mut LeanObject,
    mut v_____do__lift_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    v___x_3840_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(
        v_pu_3836_,
        v_e_3837_,
        v_____do__lift_3839_,
    );
    v___x_3841_ = lean_apply_2(v_toPure_3838_, lean_box(0), v___x_3840_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_3842_: *mut LeanObject,
    mut v_e_3843_: *mut LeanObject,
    mut v_toPure_3844_: *mut LeanObject,
    mut v_____do__lift_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3846_: u8 = 0;
    let mut v_res_3847_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3846_ = (lean_unbox(v_pu_3842_) as u8);
    v_res_3847_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(
        v_pu_boxed_3846_,
        v_e_3843_,
        v_toPure_3844_,
        v_____do__lift_3845_,
    );
    return v_res_3847_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(
    mut v_pu_3848_: u8,
    mut v_e_3849_: *mut LeanObject,
    mut v_toPure_3850_: *mut LeanObject,
    mut v_____do__lift_3851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(
        v_pu_3848_,
        v_e_3849_,
        v_____do__lift_3851_,
    );
    v___x_3853_ = lean_apply_2(v_toPure_3850_, lean_box(0), v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(
    mut v_pu_3854_: *mut LeanObject,
    mut v_e_3855_: *mut LeanObject,
    mut v_toPure_3856_: *mut LeanObject,
    mut v_____do__lift_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3858_: u8 = 0;
    let mut v_res_3859_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3858_ = (lean_unbox(v_pu_3854_) as u8);
    v_res_3859_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(
        v_pu_boxed_3858_,
        v_e_3855_,
        v_toPure_3856_,
        v_____do__lift_3857_,
    );
    return v_res_3859_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(
    mut v_pu_3860_: u8,
    mut v_e_3861_: *mut LeanObject,
    mut v_____do__lift_3862_: *mut LeanObject,
    mut v_toPure_3863_: *mut LeanObject,
    mut v_____do__lift_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    v___x_3865_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(
        v_pu_3860_,
        v_e_3861_,
        v_____do__lift_3862_,
        v_____do__lift_3864_,
    );
    v___x_3866_ = lean_apply_2(v_toPure_3863_, lean_box(0), v___x_3865_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(
    mut v_pu_3867_: *mut LeanObject,
    mut v_e_3868_: *mut LeanObject,
    mut v_____do__lift_3869_: *mut LeanObject,
    mut v_toPure_3870_: *mut LeanObject,
    mut v_____do__lift_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3872_: u8 = 0;
    let mut v_res_3873_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3872_ = (lean_unbox(v_pu_3867_) as u8);
    v_res_3873_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(
        v_pu_boxed_3872_,
        v_e_3868_,
        v_____do__lift_3869_,
        v_toPure_3870_,
        v_____do__lift_3871_,
    );
    lean_dec(v_e_3868_);
    return v_res_3873_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(
    mut v_pu_3874_: u8,
    mut v_e_3875_: *mut LeanObject,
    mut v_toPure_3876_: *mut LeanObject,
    mut v_args_3877_: *mut LeanObject,
    mut v_inst_3878_: *mut LeanObject,
    mut v___f_3879_: *mut LeanObject,
    mut v_toBind_3880_: *mut LeanObject,
    mut v_____do__lift_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3884_: usize = 0;
    let mut v___x_3885_: usize = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    v___x_3882_ = lean_box((v_pu_3874_) as usize);
    v___f_3883_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_3883_, 0, v___x_3882_);
    lean_closure_set(v___f_3883_, 1, v_e_3875_);
    lean_closure_set(v___f_3883_, 2, v_____do__lift_3881_);
    lean_closure_set(v___f_3883_, 3, v_toPure_3876_);
    v_sz_3884_ = lean_array_size(v_args_3877_);
    v___x_3885_ = 0usize;
    v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_3878_,
        v___f_3879_,
        v_sz_3884_,
        v___x_3885_,
        v_args_3877_,
    );
    v___x_3887_ = lean_apply_4(
        v_toBind_3880_,
        lean_box(0),
        lean_box(0),
        v___x_3886_,
        v___f_3883_,
    );
    return v___x_3887_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(
    mut v_pu_3888_: *mut LeanObject,
    mut v_e_3889_: *mut LeanObject,
    mut v_toPure_3890_: *mut LeanObject,
    mut v_args_3891_: *mut LeanObject,
    mut v_inst_3892_: *mut LeanObject,
    mut v___f_3893_: *mut LeanObject,
    mut v_toBind_3894_: *mut LeanObject,
    mut v_____do__lift_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3896_: u8 = 0;
    let mut v_res_3897_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3896_ = (lean_unbox(v_pu_3888_) as u8);
    v_res_3897_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(
        v_pu_boxed_3896_,
        v_e_3889_,
        v_toPure_3890_,
        v_args_3891_,
        v_inst_3892_,
        v___f_3893_,
        v_toBind_3894_,
        v_____do__lift_3895_,
    );
    return v_res_3897_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(
    mut v_pu_3898_: u8,
    mut v_e_3899_: *mut LeanObject,
    mut v_n_3900_: *mut LeanObject,
    mut v_toPure_3901_: *mut LeanObject,
    mut v_____do__lift_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    v___x_3903_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(
            v_pu_3898_,
            v_e_3899_,
            v_n_3900_,
            v_____do__lift_3902_,
        );
    v___x_3904_ = lean_apply_2(v_toPure_3901_, lean_box(0), v___x_3903_);
    return v___x_3904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(
    mut v_pu_3905_: *mut LeanObject,
    mut v_e_3906_: *mut LeanObject,
    mut v_n_3907_: *mut LeanObject,
    mut v_toPure_3908_: *mut LeanObject,
    mut v_____do__lift_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3910_: u8 = 0;
    let mut v_res_3911_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3910_ = (lean_unbox(v_pu_3905_) as u8);
    v_res_3911_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(
        v_pu_boxed_3910_,
        v_e_3906_,
        v_n_3907_,
        v_toPure_3908_,
        v_____do__lift_3909_,
    );
    lean_dec(v_e_3906_);
    return v_res_3911_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(
    mut v_pu_3912_: u8,
    mut v_e_3913_: *mut LeanObject,
    mut v_____do__lift_3914_: *mut LeanObject,
    mut v_i_3915_: *mut LeanObject,
    mut v_updateHeader_3916_: u8,
    mut v_toPure_3917_: *mut LeanObject,
    mut v_____do__lift_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    v___x_3919_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(
            v_pu_3912_,
            v_e_3913_,
            v_____do__lift_3914_,
            v_i_3915_,
            v_updateHeader_3916_,
            v_____do__lift_3918_,
        );
    v___x_3920_ = lean_apply_2(v_toPure_3917_, lean_box(0), v___x_3919_);
    return v___x_3920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(
    mut v_pu_3921_: *mut LeanObject,
    mut v_e_3922_: *mut LeanObject,
    mut v_____do__lift_3923_: *mut LeanObject,
    mut v_i_3924_: *mut LeanObject,
    mut v_updateHeader_3925_: *mut LeanObject,
    mut v_toPure_3926_: *mut LeanObject,
    mut v_____do__lift_3927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3928_: u8 = 0;
    let mut v_updateHeader_627__boxed_3929_: u8 = 0;
    let mut v_res_3930_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3928_ = (lean_unbox(v_pu_3921_) as u8);
    v_updateHeader_627__boxed_3929_ = (lean_unbox(v_updateHeader_3925_) as u8);
    v_res_3930_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(
        v_pu_boxed_3928_,
        v_e_3922_,
        v_____do__lift_3923_,
        v_i_3924_,
        v_updateHeader_627__boxed_3929_,
        v_toPure_3926_,
        v_____do__lift_3927_,
    );
    return v_res_3930_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(
    mut v_pu_3931_: u8,
    mut v_e_3932_: *mut LeanObject,
    mut v_i_3933_: *mut LeanObject,
    mut v_updateHeader_3934_: u8,
    mut v_toPure_3935_: *mut LeanObject,
    mut v_args_3936_: *mut LeanObject,
    mut v_inst_3937_: *mut LeanObject,
    mut v___f_3938_: *mut LeanObject,
    mut v_toBind_3939_: *mut LeanObject,
    mut v_____do__lift_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3944_: usize = 0;
    let mut v___x_3945_: usize = 0;
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    v___x_3941_ = lean_box((v_pu_3931_) as usize);
    v___x_3942_ = lean_box((v_updateHeader_3934_) as usize);
    v___f_3943_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3943_, 0, v___x_3941_);
    lean_closure_set(v___f_3943_, 1, v_e_3932_);
    lean_closure_set(v___f_3943_, 2, v_____do__lift_3940_);
    lean_closure_set(v___f_3943_, 3, v_i_3933_);
    lean_closure_set(v___f_3943_, 4, v___x_3942_);
    lean_closure_set(v___f_3943_, 5, v_toPure_3935_);
    v_sz_3944_ = lean_array_size(v_args_3936_);
    v___x_3945_ = 0usize;
    v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_3937_,
        v___f_3938_,
        v_sz_3944_,
        v___x_3945_,
        v_args_3936_,
    );
    v___x_3947_ = lean_apply_4(
        v_toBind_3939_,
        lean_box(0),
        lean_box(0),
        v___x_3946_,
        v___f_3943_,
    );
    return v___x_3947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(
    mut v_pu_3948_: *mut LeanObject,
    mut v_e_3949_: *mut LeanObject,
    mut v_i_3950_: *mut LeanObject,
    mut v_updateHeader_3951_: *mut LeanObject,
    mut v_toPure_3952_: *mut LeanObject,
    mut v_args_3953_: *mut LeanObject,
    mut v_inst_3954_: *mut LeanObject,
    mut v___f_3955_: *mut LeanObject,
    mut v_toBind_3956_: *mut LeanObject,
    mut v_____do__lift_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3958_: u8 = 0;
    let mut v_updateHeader_642__boxed_3959_: u8 = 0;
    let mut v_res_3960_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3958_ = (lean_unbox(v_pu_3948_) as u8);
    v_updateHeader_642__boxed_3959_ = (lean_unbox(v_updateHeader_3951_) as u8);
    v_res_3960_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(
        v_pu_boxed_3958_,
        v_e_3949_,
        v_i_3950_,
        v_updateHeader_642__boxed_3959_,
        v_toPure_3952_,
        v_args_3953_,
        v_inst_3954_,
        v___f_3955_,
        v_toBind_3956_,
        v_____do__lift_3957_,
    );
    return v_res_3960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(
    mut v_pu_3961_: u8,
    mut v_e_3962_: *mut LeanObject,
    mut v_ty_3963_: *mut LeanObject,
    mut v_toPure_3964_: *mut LeanObject,
    mut v_____do__lift_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(
        v_pu_3961_,
        v_e_3962_,
        v_ty_3963_,
        v_____do__lift_3965_,
    );
    v___x_3967_ = lean_apply_2(v_toPure_3964_, lean_box(0), v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(
    mut v_pu_3968_: *mut LeanObject,
    mut v_e_3969_: *mut LeanObject,
    mut v_ty_3970_: *mut LeanObject,
    mut v_toPure_3971_: *mut LeanObject,
    mut v_____do__lift_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3973_ = (lean_unbox(v_pu_3968_) as u8);
    v_res_3974_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(
        v_pu_boxed_3973_,
        v_e_3969_,
        v_ty_3970_,
        v_toPure_3971_,
        v_____do__lift_3972_,
    );
    lean_dec(v_e_3969_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(
    mut v_pu_3975_: u8,
    mut v_e_3976_: *mut LeanObject,
    mut v_toPure_3977_: *mut LeanObject,
    mut v_____do__lift_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    v___x_3979_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(
            v_pu_3975_,
            v_e_3976_,
            v_____do__lift_3978_,
        );
    v___x_3980_ = lean_apply_2(v_toPure_3977_, lean_box(0), v___x_3979_);
    return v___x_3980_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(
    mut v_pu_3981_: *mut LeanObject,
    mut v_e_3982_: *mut LeanObject,
    mut v_toPure_3983_: *mut LeanObject,
    mut v_____do__lift_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3985_: u8 = 0;
    let mut v_res_3986_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3985_ = (lean_unbox(v_pu_3981_) as u8);
    v_res_3986_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(
        v_pu_boxed_3985_,
        v_e_3982_,
        v_toPure_3983_,
        v_____do__lift_3984_,
    );
    return v_res_3986_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(
    mut v_pu_3987_: u8,
    mut v_e_3988_: *mut LeanObject,
    mut v_toPure_3989_: *mut LeanObject,
    mut v_____do__lift_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3991_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(
            v_pu_3987_,
            v_e_3988_,
            v_____do__lift_3990_,
        );
    v___x_3992_ = lean_apply_2(v_toPure_3989_, lean_box(0), v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed(
    mut v_pu_3993_: *mut LeanObject,
    mut v_e_3994_: *mut LeanObject,
    mut v_toPure_3995_: *mut LeanObject,
    mut v_____do__lift_3996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3997_: u8 = 0;
    let mut v_res_3998_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3997_ = (lean_unbox(v_pu_3993_) as u8);
    v_res_3998_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(
        v_pu_boxed_3997_,
        v_e_3994_,
        v_toPure_3995_,
        v_____do__lift_3996_,
    );
    return v_res_3998_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
    mut v_pu_3999_: u8,
    mut v_inst_4000_: *mut LeanObject,
    mut v_f_4001_: *mut LeanObject,
    mut v_e_4002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4012_: usize = 0;
    let mut v___x_4013_: usize = 0;
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4026_: usize = 0;
    let mut v___x_4027_: usize = 0;
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4037_: usize = 0;
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_4056_: u8 = 0;
    let mut v_args_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4003_ = lean_ctor_get(v_inst_4000_, 0);
                v_toBind_4004_ = lean_ctor_get(v_inst_4000_, 1);
                lean_inc(v_toBind_4004_);
                v_toPure_4005_ = lean_ctor_get(v_toApplicative_4003_, 1);
                v___x_4006_ = lean_box((v_pu_3999_) as usize);
                lean_inc(v_f_4001_);
                lean_inc_ref(v_inst_4000_);
                v___f_4007_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4007_, 0, v___x_4006_);
                lean_closure_set(v___f_4007_, 1, v_inst_4000_);
                lean_closure_set(v___f_4007_, 2, v_f_4001_);
                v___x_4008_ = lean_box((v_pu_3999_) as usize);
                lean_inc_n(v_toPure_4005_, 2);
                lean_inc_n(v_e_4002_, 2);
                v___f_4009_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4009_, 0, v___x_4008_);
                lean_closure_set(v___f_4009_, 1, v_e_4002_);
                lean_closure_set(v___f_4009_, 2, v_toPure_4005_);
                v___x_4016_ = lean_box((v_pu_3999_) as usize);
                v___f_4017_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4017_, 0, v___x_4016_);
                lean_closure_set(v___f_4017_, 1, v_e_4002_);
                lean_closure_set(v___f_4017_, 2, v_toPure_4005_);
                match lean_obj_tag(v_e_4002_) {
                    2 => {
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_struct_4022_ = lean_ctor_get(v_e_4002_, 2);
                        lean_inc(v_struct_4022_);
                        lean_dec_ref_known(v_e_4002_, 3);
                        v___x_4023_ = lean_apply_1(v_f_4001_, v_struct_4022_);
                        v___x_4024_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4023_,
                            v___f_4017_,
                        );
                        return v___x_4024_;
                    }
                    3 => {
                        lean_dec_ref(v___f_4017_);
                        lean_dec(v_f_4001_);
                        v_args_4025_ = lean_ctor_get(v_e_4002_, 2);
                        lean_inc_ref(v_args_4025_);
                        lean_dec_ref_known(v_e_4002_, 3);
                        v_sz_4026_ = lean_array_size(v_args_4025_);
                        v___x_4027_ = 0usize;
                        v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_4000_,
                            v___f_4007_,
                            v_sz_4026_,
                            v___x_4027_,
                            v_args_4025_,
                        );
                        v___x_4029_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4028_,
                            v___f_4009_,
                        );
                        return v___x_4029_;
                    }
                    4 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        v_fvarId_4030_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc(v_fvarId_4030_);
                        v_args_4031_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc_ref(v_args_4031_);
                        v___x_4032_ = lean_box((v_pu_3999_) as usize);
                        lean_inc(v_toBind_4004_);
                        v___f_4033_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            8,
                            7,
                        );
                        lean_closure_set(v___f_4033_, 0, v___x_4032_);
                        lean_closure_set(v___f_4033_, 1, v_e_4002_);
                        lean_closure_set(v___f_4033_, 2, v_toPure_4005_);
                        lean_closure_set(v___f_4033_, 3, v_args_4031_);
                        lean_closure_set(v___f_4033_, 4, v_inst_4000_);
                        lean_closure_set(v___f_4033_, 5, v___f_4007_);
                        lean_closure_set(v___f_4033_, 6, v_toBind_4004_);
                        v___x_4034_ = lean_apply_1(v_f_4001_, v_fvarId_4030_);
                        v___x_4035_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4034_,
                            v___f_4033_,
                        );
                        return v___x_4035_;
                    }
                    5 => {
                        lean_dec_ref(v___f_4017_);
                        lean_dec(v_f_4001_);
                        v_args_4036_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc_ref(v_args_4036_);
                        lean_dec_ref_known(v_e_4002_, 2);
                        v_sz_4037_ = lean_array_size(v_args_4036_);
                        v___x_4038_ = 0usize;
                        v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_4000_,
                            v___f_4007_,
                            v_sz_4037_,
                            v___x_4038_,
                            v_args_4036_,
                        );
                        v___x_4040_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4039_,
                            v___f_4009_,
                        );
                        return v___x_4040_;
                    }
                    6 => {
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_var_4041_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc(v_var_4041_);
                        lean_dec_ref_known(v_e_4002_, 2);
                        v_fvarId_4019_ = v_var_4041_;
                        state = 2;
                        continue;
                    }
                    7 => {
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_var_4042_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc(v_var_4042_);
                        lean_dec_ref_known(v_e_4002_, 2);
                        v_fvarId_4019_ = v_var_4042_;
                        state = 2;
                        continue;
                    }
                    8 => {
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_var_4043_ = lean_ctor_get(v_e_4002_, 2);
                        lean_inc(v_var_4043_);
                        lean_dec_ref_known(v_e_4002_, 3);
                        v___x_4044_ = lean_apply_1(v_f_4001_, v_var_4043_);
                        v___x_4045_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4044_,
                            v___f_4017_,
                        );
                        return v___x_4045_;
                    }
                    9 => {
                        lean_dec_ref(v___f_4017_);
                        lean_dec(v_f_4001_);
                        v_args_4046_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc_ref(v_args_4046_);
                        lean_dec_ref_known(v_e_4002_, 2);
                        v_args_4011_ = v_args_4046_;
                        state = 1;
                        continue;
                    }
                    10 => {
                        lean_dec_ref(v___f_4017_);
                        lean_dec(v_f_4001_);
                        v_args_4047_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc_ref(v_args_4047_);
                        lean_dec_ref_known(v_e_4002_, 2);
                        v_args_4011_ = v_args_4047_;
                        state = 1;
                        continue;
                    }
                    11 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_n_4048_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc(v_n_4048_);
                        v_var_4049_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc(v_var_4049_);
                        v___x_4050_ = lean_box((v_pu_3999_) as usize);
                        v___f_4051_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        lean_closure_set(v___f_4051_, 0, v___x_4050_);
                        lean_closure_set(v___f_4051_, 1, v_e_4002_);
                        lean_closure_set(v___f_4051_, 2, v_n_4048_);
                        lean_closure_set(v___f_4051_, 3, v_toPure_4005_);
                        v___x_4052_ = lean_apply_1(v_f_4001_, v_var_4049_);
                        v___x_4053_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4052_,
                            v___f_4051_,
                        );
                        return v___x_4053_;
                    }
                    12 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        v_var_4054_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc(v_var_4054_);
                        v_i_4055_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc_ref(v_i_4055_);
                        v_updateHeader_4056_ = lean_ctor_get_uint8(
                            v_e_4002_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_args_4057_ = lean_ctor_get(v_e_4002_, 2);
                        lean_inc_ref(v_args_4057_);
                        v___x_4058_ = lean_box((v_pu_3999_) as usize);
                        v___x_4059_ = lean_box((v_updateHeader_4056_) as usize);
                        lean_inc(v_toBind_4004_);
                        v___f_4060_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed
                                as *mut core::ffi::c_void,
                            10,
                            9,
                        );
                        lean_closure_set(v___f_4060_, 0, v___x_4058_);
                        lean_closure_set(v___f_4060_, 1, v_e_4002_);
                        lean_closure_set(v___f_4060_, 2, v_i_4055_);
                        lean_closure_set(v___f_4060_, 3, v___x_4059_);
                        lean_closure_set(v___f_4060_, 4, v_toPure_4005_);
                        lean_closure_set(v___f_4060_, 5, v_args_4057_);
                        lean_closure_set(v___f_4060_, 6, v_inst_4000_);
                        lean_closure_set(v___f_4060_, 7, v___f_4007_);
                        lean_closure_set(v___f_4060_, 8, v_toBind_4004_);
                        v___x_4061_ = lean_apply_1(v_f_4001_, v_var_4054_);
                        v___x_4062_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4061_,
                            v___f_4060_,
                        );
                        return v___x_4062_;
                    }
                    13 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_ty_4063_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc_ref(v_ty_4063_);
                        v_fvarId_4064_ = lean_ctor_get(v_e_4002_, 1);
                        lean_inc(v_fvarId_4064_);
                        v___x_4065_ = lean_box((v_pu_3999_) as usize);
                        v___f_4066_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        lean_closure_set(v___f_4066_, 0, v___x_4065_);
                        lean_closure_set(v___f_4066_, 1, v_e_4002_);
                        lean_closure_set(v___f_4066_, 2, v_ty_4063_);
                        lean_closure_set(v___f_4066_, 3, v_toPure_4005_);
                        v___x_4067_ = lean_apply_1(v_f_4001_, v_fvarId_4064_);
                        v___x_4068_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4067_,
                            v___f_4066_,
                        );
                        return v___x_4068_;
                    }
                    14 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_fvarId_4069_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc(v_fvarId_4069_);
                        v___x_4070_ = lean_box((v_pu_3999_) as usize);
                        v___f_4071_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___f_4071_, 0, v___x_4070_);
                        lean_closure_set(v___f_4071_, 1, v_e_4002_);
                        lean_closure_set(v___f_4071_, 2, v_toPure_4005_);
                        v___x_4072_ = lean_apply_1(v_f_4001_, v_fvarId_4069_);
                        v___x_4073_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4072_,
                            v___f_4071_,
                        );
                        return v___x_4073_;
                    }
                    15 => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec_ref(v_inst_4000_);
                        v_fvarId_4074_ = lean_ctor_get(v_e_4002_, 0);
                        lean_inc(v_fvarId_4074_);
                        v___x_4075_ = lean_box((v_pu_3999_) as usize);
                        v___f_4076_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___f_4076_, 0, v___x_4075_);
                        lean_closure_set(v___f_4076_, 1, v_e_4002_);
                        lean_closure_set(v___f_4076_, 2, v_toPure_4005_);
                        v___x_4077_ = lean_apply_1(v_f_4001_, v_fvarId_4074_);
                        v___x_4078_ = lean_apply_4(
                            v_toBind_4004_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4077_,
                            v___f_4076_,
                        );
                        return v___x_4078_;
                    }
                    _ => {
                        lean_inc(v_toPure_4005_);
                        lean_dec_ref(v___f_4017_);
                        lean_dec_ref(v___f_4009_);
                        lean_dec_ref(v___f_4007_);
                        lean_dec(v_toBind_4004_);
                        lean_dec(v_f_4001_);
                        lean_dec_ref(v_inst_4000_);
                        v___x_4079_ = lean_apply_2(v_toPure_4005_, lean_box(0), v_e_4002_);
                        return v___x_4079_;
                    }
                }
            }
            1 => {
                v_sz_4012_ = lean_array_size(v_args_4011_);
                v___x_4013_ = 0usize;
                v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_4000_,
                    v___f_4007_,
                    v_sz_4012_,
                    v___x_4013_,
                    v_args_4011_,
                );
                v___x_4015_ = lean_apply_4(
                    v_toBind_4004_,
                    lean_box(0),
                    lean_box(0),
                    v___x_4014_,
                    v___f_4009_,
                );
                return v___x_4015_;
            }
            2 => {
                v___x_4020_ = lean_apply_1(v_f_4001_, v_fvarId_4019_);
                v___x_4021_ = lean_apply_4(
                    v_toBind_4004_,
                    lean_box(0),
                    lean_box(0),
                    v___x_4020_,
                    v___f_4017_,
                );
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(
    mut v_pu_4080_: *mut LeanObject,
    mut v_inst_4081_: *mut LeanObject,
    mut v_f_4082_: *mut LeanObject,
    mut v_e_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4084_: u8 = 0;
    let mut v_res_4085_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4084_ = (lean_unbox(v_pu_4080_) as u8);
    v_res_4085_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_boxed_4084_,
        v_inst_4081_,
        v_f_4082_,
        v_e_4083_,
    );
    return v_res_4085_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM(
    mut v_m_4086_: *mut LeanObject,
    mut v_pu_4087_: u8,
    mut v_inst_4088_: *mut LeanObject,
    mut v_inst_4089_: *mut LeanObject,
    mut v_f_4090_: *mut LeanObject,
    mut v_e_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4087_,
        v_inst_4089_,
        v_f_4090_,
        v_e_4091_,
    );
    return v___x_4092_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(
    mut v_m_4093_: *mut LeanObject,
    mut v_pu_4094_: *mut LeanObject,
    mut v_inst_4095_: *mut LeanObject,
    mut v_inst_4096_: *mut LeanObject,
    mut v_f_4097_: *mut LeanObject,
    mut v_e_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4099_: u8 = 0;
    let mut v_res_4100_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4099_ = (lean_unbox(v_pu_4094_) as u8);
    v_res_4100_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(
        v_m_4093_,
        v_pu_boxed_4099_,
        v_inst_4095_,
        v_inst_4096_,
        v_f_4097_,
        v_e_4098_,
    );
    lean_dec(v_inst_4095_);
    return v_res_4100_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(
    mut v_inst_4101_: *mut LeanObject,
    mut v_f_4102_: *mut LeanObject,
    mut v_x_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    v___x_4105_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_4101_, v_f_4102_, v___y_4104_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(
    mut v_args_4106_: *mut LeanObject,
    mut v_toPure_4107_: *mut LeanObject,
    mut v_inst_4108_: *mut LeanObject,
    mut v___f_4109_: *mut LeanObject,
    mut v_____r_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    v___x_4111_ = lean_unsigned_to_nat(0);
    v___x_4112_ = lean_array_get_size(v_args_4106_);
    v___x_4113_ = lean_box(0);
    v___x_4114_ = lean_nat_dec_lt(v___x_4111_, v___x_4112_);
    if v___x_4114_ == 0 {
        let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4109_);
        lean_dec_ref(v_inst_4108_);
        lean_dec_ref(v_args_4106_);
        v___x_4115_ = lean_apply_2(v_toPure_4107_, lean_box(0), v___x_4113_);
        return v___x_4115_;
    } else {
        let mut v___x_4116_: u8 = 0;
        v___x_4116_ = lean_nat_dec_le(v___x_4112_, v___x_4112_);
        if v___x_4116_ == 0 {
            if v___x_4114_ == 0 {
                let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_4109_);
                lean_dec_ref(v_inst_4108_);
                lean_dec_ref(v_args_4106_);
                v___x_4117_ = lean_apply_2(v_toPure_4107_, lean_box(0), v___x_4113_);
                return v___x_4117_;
            } else {
                let mut v___x_4118_: usize = 0;
                let mut v___x_4119_: usize = 0;
                let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_4107_);
                v___x_4118_ = 0usize;
                v___x_4119_ = lean_usize_of_nat(v___x_4112_);
                v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_4108_,
                    v___f_4109_,
                    v_args_4106_,
                    v___x_4118_,
                    v___x_4119_,
                    v___x_4113_,
                );
                return v___x_4120_;
            }
        } else {
            let mut v___x_4121_: usize = 0;
            let mut v___x_4122_: usize = 0;
            let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_4107_);
            v___x_4121_ = 0usize;
            v___x_4122_ = lean_usize_of_nat(v___x_4112_);
            v___x_4123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_4108_,
                v___f_4109_,
                v_args_4106_,
                v___x_4121_,
                v___x_4122_,
                v___x_4113_,
            );
            return v___x_4123_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(
    mut v_inst_4124_: *mut LeanObject,
    mut v_f_4125_: *mut LeanObject,
    mut v_e_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: usize = 0;
    let mut v___x_4141_: usize = 0;
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: usize = 0;
    let mut v___x_4157_: usize = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: usize = 0;
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: u8 = 0;
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: usize = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: usize = 0;
    let mut v___x_4179_: usize = 0;
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4127_ = lean_ctor_get(v_inst_4124_, 0);
                v_toBind_4128_ = lean_ctor_get(v_inst_4124_, 1);
                v_toPure_4129_ = lean_ctor_get(v_toApplicative_4127_, 1);
                lean_inc(v_f_4125_);
                lean_inc_ref(v_inst_4124_);
                v___f_4130_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4130_, 0, v_inst_4124_);
                lean_closure_set(v___f_4130_, 1, v_f_4125_);
                match lean_obj_tag(v_e_4126_) {
                    2 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_struct_4146_ = lean_ctor_get(v_e_4126_, 2);
                        lean_inc(v_struct_4146_);
                        lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4147_ = lean_apply_1(v_f_4125_, v_struct_4146_);
                        return v___x_4147_;
                    }
                    3 => {
                        lean_dec(v_f_4125_);
                        v_args_4148_ = lean_ctor_get(v_e_4126_, 2);
                        lean_inc_ref(v_args_4148_);
                        lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4149_ = lean_unsigned_to_nat(0);
                        v___x_4150_ = lean_array_get_size(v_args_4148_);
                        v___x_4151_ = lean_box(0);
                        v___x_4152_ = lean_nat_dec_lt(v___x_4149_, v___x_4150_);
                        if v___x_4152_ == 0 {
                            lean_inc(v_toPure_4129_);
                            lean_dec_ref(v_args_4148_);
                            lean_dec_ref(v___f_4130_);
                            lean_dec_ref(v_inst_4124_);
                            v___x_4153_ = lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4151_);
                            return v___x_4153_;
                        } else {
                            v___x_4154_ = lean_nat_dec_le(v___x_4150_, v___x_4150_);
                            if v___x_4154_ == 0 {
                                if v___x_4152_ == 0 {
                                    lean_inc(v_toPure_4129_);
                                    lean_dec_ref(v_args_4148_);
                                    lean_dec_ref(v___f_4130_);
                                    lean_dec_ref(v_inst_4124_);
                                    v___x_4155_ =
                                        lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4151_);
                                    return v___x_4155_;
                                } else {
                                    v___x_4156_ = 0usize;
                                    v___x_4157_ = lean_usize_of_nat(v___x_4150_);
                                    v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4124_, v___f_4130_, v_args_4148_, v___x_4156_, v___x_4157_, v___x_4151_);
                                    return v___x_4158_;
                                }
                            } else {
                                v___x_4159_ = 0usize;
                                v___x_4160_ = lean_usize_of_nat(v___x_4150_);
                                v___x_4161_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v_inst_4124_,
                                        v___f_4130_,
                                        v_args_4148_,
                                        v___x_4159_,
                                        v___x_4160_,
                                        v___x_4151_,
                                    );
                                return v___x_4161_;
                            }
                        }
                    }
                    4 => {
                        lean_inc(v_toPure_4129_);
                        lean_inc(v_toBind_4128_);
                        v_fvarId_4162_ = lean_ctor_get(v_e_4126_, 0);
                        lean_inc(v_fvarId_4162_);
                        v_args_4163_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc_ref(v_args_4163_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___f_4164_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        lean_closure_set(v___f_4164_, 0, v_args_4163_);
                        lean_closure_set(v___f_4164_, 1, v_toPure_4129_);
                        lean_closure_set(v___f_4164_, 2, v_inst_4124_);
                        lean_closure_set(v___f_4164_, 3, v___f_4130_);
                        v___x_4165_ = lean_apply_1(v_f_4125_, v_fvarId_4162_);
                        v___x_4166_ = lean_apply_4(
                            v_toBind_4128_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4165_,
                            v___f_4164_,
                        );
                        return v___x_4166_;
                    }
                    5 => {
                        lean_dec(v_f_4125_);
                        v_args_4167_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc_ref(v_args_4167_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4168_ = lean_unsigned_to_nat(0);
                        v___x_4169_ = lean_array_get_size(v_args_4167_);
                        v___x_4170_ = lean_box(0);
                        v___x_4171_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
                        if v___x_4171_ == 0 {
                            lean_inc(v_toPure_4129_);
                            lean_dec_ref(v_args_4167_);
                            lean_dec_ref(v___f_4130_);
                            lean_dec_ref(v_inst_4124_);
                            v___x_4172_ = lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4170_);
                            return v___x_4172_;
                        } else {
                            v___x_4173_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
                            if v___x_4173_ == 0 {
                                if v___x_4171_ == 0 {
                                    lean_inc(v_toPure_4129_);
                                    lean_dec_ref(v_args_4167_);
                                    lean_dec_ref(v___f_4130_);
                                    lean_dec_ref(v_inst_4124_);
                                    v___x_4174_ =
                                        lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4170_);
                                    return v___x_4174_;
                                } else {
                                    v___x_4175_ = 0usize;
                                    v___x_4176_ = lean_usize_of_nat(v___x_4169_);
                                    v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4124_, v___f_4130_, v_args_4167_, v___x_4175_, v___x_4176_, v___x_4170_);
                                    return v___x_4177_;
                                }
                            } else {
                                v___x_4178_ = 0usize;
                                v___x_4179_ = lean_usize_of_nat(v___x_4169_);
                                v___x_4180_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v_inst_4124_,
                                        v___f_4130_,
                                        v_args_4167_,
                                        v___x_4178_,
                                        v___x_4179_,
                                        v___x_4170_,
                                    );
                                return v___x_4180_;
                            }
                        }
                    }
                    6 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_var_4181_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc(v_var_4181_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4182_ = lean_apply_1(v_f_4125_, v_var_4181_);
                        return v___x_4182_;
                    }
                    7 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_var_4183_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc(v_var_4183_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4184_ = lean_apply_1(v_f_4125_, v_var_4183_);
                        return v___x_4184_;
                    }
                    8 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_var_4185_ = lean_ctor_get(v_e_4126_, 2);
                        lean_inc(v_var_4185_);
                        lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4186_ = lean_apply_1(v_f_4125_, v_var_4185_);
                        return v___x_4186_;
                    }
                    9 => {
                        lean_dec(v_f_4125_);
                        v_args_4187_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc_ref(v_args_4187_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v_args_4132_ = v_args_4187_;
                        state = 1;
                        continue;
                    }
                    10 => {
                        lean_dec(v_f_4125_);
                        v_args_4188_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc_ref(v_args_4188_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v_args_4132_ = v_args_4188_;
                        state = 1;
                        continue;
                    }
                    11 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_var_4189_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc(v_var_4189_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4190_ = lean_apply_1(v_f_4125_, v_var_4189_);
                        return v___x_4190_;
                    }
                    12 => {
                        lean_inc(v_toPure_4129_);
                        lean_inc(v_toBind_4128_);
                        v_var_4191_ = lean_ctor_get(v_e_4126_, 0);
                        lean_inc(v_var_4191_);
                        v_args_4192_ = lean_ctor_get(v_e_4126_, 2);
                        lean_inc_ref(v_args_4192_);
                        lean_dec_ref_known(v_e_4126_, 3);
                        v___f_4193_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        lean_closure_set(v___f_4193_, 0, v_args_4192_);
                        lean_closure_set(v___f_4193_, 1, v_toPure_4129_);
                        lean_closure_set(v___f_4193_, 2, v_inst_4124_);
                        lean_closure_set(v___f_4193_, 3, v___f_4130_);
                        v___x_4194_ = lean_apply_1(v_f_4125_, v_var_4191_);
                        v___x_4195_ = lean_apply_4(
                            v_toBind_4128_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4194_,
                            v___f_4193_,
                        );
                        return v___x_4195_;
                    }
                    13 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_fvarId_4196_ = lean_ctor_get(v_e_4126_, 1);
                        lean_inc(v_fvarId_4196_);
                        lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4197_ = lean_apply_1(v_f_4125_, v_fvarId_4196_);
                        return v___x_4197_;
                    }
                    14 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_fvarId_4198_ = lean_ctor_get(v_e_4126_, 0);
                        lean_inc(v_fvarId_4198_);
                        lean_dec_ref_known(v_e_4126_, 1);
                        v___x_4199_ = lean_apply_1(v_f_4125_, v_fvarId_4198_);
                        return v___x_4199_;
                    }
                    15 => {
                        lean_dec_ref(v___f_4130_);
                        lean_dec_ref(v_inst_4124_);
                        v_fvarId_4200_ = lean_ctor_get(v_e_4126_, 0);
                        lean_inc(v_fvarId_4200_);
                        lean_dec_ref_known(v_e_4126_, 1);
                        v___x_4201_ = lean_apply_1(v_f_4125_, v_fvarId_4200_);
                        return v___x_4201_;
                    }
                    _ => {
                        lean_inc(v_toPure_4129_);
                        lean_dec_ref(v___f_4130_);
                        lean_dec(v_e_4126_);
                        lean_dec(v_f_4125_);
                        lean_dec_ref(v_inst_4124_);
                        v___x_4202_ = lean_box(0);
                        v___x_4203_ = lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4202_);
                        return v___x_4203_;
                    }
                }
            }
            1 => {
                v___x_4133_ = lean_unsigned_to_nat(0);
                v___x_4134_ = lean_array_get_size(v_args_4132_);
                v___x_4135_ = lean_box(0);
                v___x_4136_ = lean_nat_dec_lt(v___x_4133_, v___x_4134_);
                if v___x_4136_ == 0 {
                    lean_inc(v_toPure_4129_);
                    lean_dec_ref(v_args_4132_);
                    lean_dec_ref(v___f_4130_);
                    lean_dec_ref(v_inst_4124_);
                    v___x_4137_ = lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4135_);
                    return v___x_4137_;
                } else {
                    v___x_4138_ = lean_nat_dec_le(v___x_4134_, v___x_4134_);
                    if v___x_4138_ == 0 {
                        if v___x_4136_ == 0 {
                            lean_inc(v_toPure_4129_);
                            lean_dec_ref(v_args_4132_);
                            lean_dec_ref(v___f_4130_);
                            lean_dec_ref(v_inst_4124_);
                            v___x_4139_ = lean_apply_2(v_toPure_4129_, lean_box(0), v___x_4135_);
                            return v___x_4139_;
                        } else {
                            v___x_4140_ = 0usize;
                            v___x_4141_ = lean_usize_of_nat(v___x_4134_);
                            v___x_4142_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v_inst_4124_,
                                    v___f_4130_,
                                    v_args_4132_,
                                    v___x_4140_,
                                    v___x_4141_,
                                    v___x_4135_,
                                );
                            return v___x_4142_;
                        }
                    } else {
                        v___x_4143_ = 0usize;
                        v___x_4144_ = lean_usize_of_nat(v___x_4134_);
                        v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_4124_,
                            v___f_4130_,
                            v_args_4132_,
                            v___x_4143_,
                            v___x_4144_,
                            v___x_4135_,
                        );
                        return v___x_4145_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM(
    mut v_m_4204_: *mut LeanObject,
    mut v_pu_4205_: u8,
    mut v_inst_4206_: *mut LeanObject,
    mut v_f_4207_: *mut LeanObject,
    mut v_e_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    v___x_4209_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4206_, v_f_4207_, v_e_4208_);
    return v___x_4209_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(
    mut v_m_4210_: *mut LeanObject,
    mut v_pu_4211_: *mut LeanObject,
    mut v_inst_4212_: *mut LeanObject,
    mut v_f_4213_: *mut LeanObject,
    mut v_e_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4215_ = (lean_unbox(v_pu_4211_) as u8);
    v_res_4216_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(
        v_m_4210_,
        v_pu_boxed_4215_,
        v_inst_4212_,
        v_f_4213_,
        v_e_4214_,
    );
    return v_res_4216_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(
    mut v_pu_4217_: u8,
    mut v_m_4218_: *mut LeanObject,
    mut v_inst_4219_: *mut LeanObject,
    mut v_inst_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    v___x_4223_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4217_,
        v_inst_4220_,
        v___y_4221_,
        v___y_4222_,
    );
    return v___x_4223_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(
    mut v_pu_4224_: *mut LeanObject,
    mut v_m_4225_: *mut LeanObject,
    mut v_inst_4226_: *mut LeanObject,
    mut v_inst_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4230_: u8 = 0;
    let mut v_res_4231_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4230_ = (lean_unbox(v_pu_4224_) as u8);
    v_res_4231_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(
        v_pu_boxed_4230_,
        v_m_4225_,
        v_inst_4226_,
        v_inst_4227_,
        v___y_4228_,
        v___y_4229_,
    );
    lean_dec(v_inst_4226_);
    return v_res_4231_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(
    mut v_m_4232_: *mut LeanObject,
    mut v_inst_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    v___x_4236_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4233_, v___y_4234_, v___y_4235_);
    return v___x_4236_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue(mut v_pu_4238_: u8) -> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    v___x_4239_ = lean_box((v_pu_4238_) as usize);
    v___f_4240_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4240_, 0, v___x_4239_);
    v___f_4241_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0;
    v___x_4242_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4242_, 0, v___f_4240_);
    lean_ctor_set(v___x_4242_, 1, v___f_4241_);
    return v___x_4242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(
    mut v_pu_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4244_: u8 = 0;
    let mut v_res_4245_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4244_ = (lean_unbox(v_pu_4243_) as u8);
    v_res_4245_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_4244_);
    return v_res_4245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(
    mut v_pu_4246_: u8,
    mut v_decl_4247_: *mut LeanObject,
    mut v_____do__lift_4248_: *mut LeanObject,
    mut v_inst_4249_: *mut LeanObject,
    mut v_____do__lift_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = lean_box((v_pu_4246_) as usize);
    v___x_4252_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_4252_, 0, v___x_4251_);
    lean_closure_set(v___x_4252_, 1, v_decl_4247_);
    lean_closure_set(v___x_4252_, 2, v_____do__lift_4248_);
    lean_closure_set(v___x_4252_, 3, v_____do__lift_4250_);
    v___x_4253_ = lean_apply_2(v_inst_4249_, lean_box(0), v___x_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_4254_: *mut LeanObject,
    mut v_decl_4255_: *mut LeanObject,
    mut v_____do__lift_4256_: *mut LeanObject,
    mut v_inst_4257_: *mut LeanObject,
    mut v_____do__lift_4258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4259_: u8 = 0;
    let mut v_res_4260_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4259_ = (lean_unbox(v_pu_4254_) as u8);
    v_res_4260_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(
        v_pu_boxed_4259_,
        v_decl_4255_,
        v_____do__lift_4256_,
        v_inst_4257_,
        v_____do__lift_4258_,
    );
    return v_res_4260_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(
    mut v_pu_4261_: u8,
    mut v_decl_4262_: *mut LeanObject,
    mut v_inst_4263_: *mut LeanObject,
    mut v_inst_4264_: *mut LeanObject,
    mut v_f_4265_: *mut LeanObject,
    mut v_value_4266_: *mut LeanObject,
    mut v_toBind_4267_: *mut LeanObject,
    mut v_____do__lift_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    v___x_4269_ = lean_box((v_pu_4261_) as usize);
    v___f_4270_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4270_, 0, v___x_4269_);
    lean_closure_set(v___f_4270_, 1, v_decl_4262_);
    lean_closure_set(v___f_4270_, 2, v_____do__lift_4268_);
    lean_closure_set(v___f_4270_, 3, v_inst_4263_);
    v___x_4271_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4261_,
        v_inst_4264_,
        v_f_4265_,
        v_value_4266_,
    );
    v___x_4272_ = lean_apply_4(
        v_toBind_4267_,
        lean_box(0),
        lean_box(0),
        v___x_4271_,
        v___f_4270_,
    );
    return v___x_4272_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_4273_: *mut LeanObject,
    mut v_decl_4274_: *mut LeanObject,
    mut v_inst_4275_: *mut LeanObject,
    mut v_inst_4276_: *mut LeanObject,
    mut v_f_4277_: *mut LeanObject,
    mut v_value_4278_: *mut LeanObject,
    mut v_toBind_4279_: *mut LeanObject,
    mut v_____do__lift_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4281_: u8 = 0;
    let mut v_res_4282_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4281_ = (lean_unbox(v_pu_4273_) as u8);
    v_res_4282_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(
        v_pu_boxed_4281_,
        v_decl_4274_,
        v_inst_4275_,
        v_inst_4276_,
        v_f_4277_,
        v_value_4278_,
        v_toBind_4279_,
        v_____do__lift_4280_,
    );
    return v_res_4282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
    mut v_pu_4283_: u8,
    mut v_inst_4284_: *mut LeanObject,
    mut v_inst_4285_: *mut LeanObject,
    mut v_f_4286_: *mut LeanObject,
    mut v_decl_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4288_ = lean_ctor_get(v_inst_4285_, 1);
    lean_inc_n(v_toBind_4288_, 2);
    v_type_4289_ = lean_ctor_get(v_decl_4287_, 2);
    lean_inc_ref(v_type_4289_);
    v_value_4290_ = lean_ctor_get(v_decl_4287_, 3);
    lean_inc(v_value_4290_);
    v___x_4291_ = lean_box((v_pu_4283_) as usize);
    lean_inc(v_f_4286_);
    lean_inc_ref(v_inst_4285_);
    v___f_4292_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_4292_, 0, v___x_4291_);
    lean_closure_set(v___f_4292_, 1, v_decl_4287_);
    lean_closure_set(v___f_4292_, 2, v_inst_4284_);
    lean_closure_set(v___f_4292_, 3, v_inst_4285_);
    lean_closure_set(v___f_4292_, 4, v_f_4286_);
    lean_closure_set(v___f_4292_, 5, v_value_4290_);
    lean_closure_set(v___f_4292_, 6, v_toBind_4288_);
    v___x_4293_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_4285_, v_f_4286_, v_type_4289_);
    v___x_4294_ = lean_apply_4(
        v_toBind_4288_,
        lean_box(0),
        lean_box(0),
        v___x_4293_,
        v___f_4292_,
    );
    return v___x_4294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(
    mut v_pu_4295_: *mut LeanObject,
    mut v_inst_4296_: *mut LeanObject,
    mut v_inst_4297_: *mut LeanObject,
    mut v_f_4298_: *mut LeanObject,
    mut v_decl_4299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4300_: u8 = 0;
    let mut v_res_4301_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4300_ = (lean_unbox(v_pu_4295_) as u8);
    v_res_4301_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_boxed_4300_,
        v_inst_4296_,
        v_inst_4297_,
        v_f_4298_,
        v_decl_4299_,
    );
    return v_res_4301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM(
    mut v_m_4302_: *mut LeanObject,
    mut v_pu_4303_: u8,
    mut v_inst_4304_: *mut LeanObject,
    mut v_inst_4305_: *mut LeanObject,
    mut v_f_4306_: *mut LeanObject,
    mut v_decl_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_4303_,
        v_inst_4304_,
        v_inst_4305_,
        v_f_4306_,
        v_decl_4307_,
    );
    return v___x_4308_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(
    mut v_m_4309_: *mut LeanObject,
    mut v_pu_4310_: *mut LeanObject,
    mut v_inst_4311_: *mut LeanObject,
    mut v_inst_4312_: *mut LeanObject,
    mut v_f_4313_: *mut LeanObject,
    mut v_decl_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4315_: u8 = 0;
    let mut v_res_4316_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4315_ = (lean_unbox(v_pu_4310_) as u8);
    v_res_4316_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(
        v_m_4309_,
        v_pu_boxed_4315_,
        v_inst_4311_,
        v_inst_4312_,
        v_f_4313_,
        v_decl_4314_,
    );
    return v_res_4316_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(
    mut v_inst_4317_: *mut LeanObject,
    mut v_f_4318_: *mut LeanObject,
    mut v_value_4319_: *mut LeanObject,
    mut v_____r_4320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    v___x_4321_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4317_, v_f_4318_, v_value_4319_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
    mut v_inst_4322_: *mut LeanObject,
    mut v_f_4323_: *mut LeanObject,
    mut v_decl_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4325_ = lean_ctor_get(v_inst_4322_, 1);
    lean_inc(v_toBind_4325_);
    v_type_4326_ = lean_ctor_get(v_decl_4324_, 2);
    lean_inc_ref(v_type_4326_);
    v_value_4327_ = lean_ctor_get(v_decl_4324_, 3);
    lean_inc(v_value_4327_);
    lean_dec_ref(v_decl_4324_);
    lean_inc(v_f_4323_);
    lean_inc_ref(v_inst_4322_);
    v___f_4328_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4328_, 0, v_inst_4322_);
    lean_closure_set(v___f_4328_, 1, v_f_4323_);
    lean_closure_set(v___f_4328_, 2, v_value_4327_);
    v___x_4329_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_4322_, v_f_4323_, v_type_4326_);
    v___x_4330_ = lean_apply_4(
        v_toBind_4325_,
        lean_box(0),
        lean_box(0),
        v___x_4329_,
        v___f_4328_,
    );
    return v___x_4330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM(
    mut v_m_4331_: *mut LeanObject,
    mut v_pu_4332_: u8,
    mut v_inst_4333_: *mut LeanObject,
    mut v_f_4334_: *mut LeanObject,
    mut v_decl_4335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ =
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_4333_, v_f_4334_, v_decl_4335_);
    return v___x_4336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(
    mut v_m_4337_: *mut LeanObject,
    mut v_pu_4338_: *mut LeanObject,
    mut v_inst_4339_: *mut LeanObject,
    mut v_f_4340_: *mut LeanObject,
    mut v_decl_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4342_: u8 = 0;
    let mut v_res_4343_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4342_ = (lean_unbox(v_pu_4338_) as u8);
    v_res_4343_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(
        v_m_4337_,
        v_pu_boxed_4342_,
        v_inst_4339_,
        v_f_4340_,
        v_decl_4341_,
    );
    return v_res_4343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(
    mut v_pu_4344_: u8,
    mut v_m_4345_: *mut LeanObject,
    mut v_inst_4346_: *mut LeanObject,
    mut v_inst_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_4344_,
        v_inst_4346_,
        v_inst_4347_,
        v___y_4348_,
        v___y_4349_,
    );
    return v___x_4350_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(
    mut v_pu_4351_: *mut LeanObject,
    mut v_m_4352_: *mut LeanObject,
    mut v_inst_4353_: *mut LeanObject,
    mut v_inst_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4357_: u8 = 0;
    let mut v_res_4358_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4357_ = (lean_unbox(v_pu_4351_) as u8);
    v_res_4358_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(
        v_pu_boxed_4357_,
        v_m_4352_,
        v_inst_4353_,
        v_inst_4354_,
        v___y_4355_,
        v___y_4356_,
    );
    return v_res_4358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(
    mut v_m_4359_: *mut LeanObject,
    mut v_inst_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ =
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_4360_, v___y_4361_, v___y_4362_);
    return v___x_4363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(mut v_pu_4365_: u8) -> *mut LeanObject {
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    v___x_4366_ = lean_box((v_pu_4365_) as usize);
    v___f_4367_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4367_, 0, v___x_4366_);
    v___f_4368_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0;
    v___x_4369_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4369_, 0, v___f_4367_);
    lean_ctor_set(v___x_4369_, 1, v___f_4368_);
    return v___x_4369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(
    mut v_pu_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4371_: u8 = 0;
    let mut v_res_4372_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4371_ = (lean_unbox(v_pu_4370_) as u8);
    v_res_4372_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_4371_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(
    mut v_pu_4373_: u8,
    mut v_param_4374_: *mut LeanObject,
    mut v_inst_4375_: *mut LeanObject,
    mut v_____do__lift_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = lean_box((v_pu_4373_) as usize);
    v___x_4378_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_4378_, 0, v___x_4377_);
    lean_closure_set(v___x_4378_, 1, v_param_4374_);
    lean_closure_set(v___x_4378_, 2, v_____do__lift_4376_);
    v___x_4379_ = lean_apply_2(v_inst_4375_, lean_box(0), v___x_4378_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_4380_: *mut LeanObject,
    mut v_param_4381_: *mut LeanObject,
    mut v_inst_4382_: *mut LeanObject,
    mut v_____do__lift_4383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4384_: u8 = 0;
    let mut v_res_4385_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4384_ = (lean_unbox(v_pu_4380_) as u8);
    v_res_4385_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(
        v_pu_boxed_4384_,
        v_param_4381_,
        v_inst_4382_,
        v_____do__lift_4383_,
    );
    return v_res_4385_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
    mut v_pu_4386_: u8,
    mut v_inst_4387_: *mut LeanObject,
    mut v_inst_4388_: *mut LeanObject,
    mut v_f_4389_: *mut LeanObject,
    mut v_param_4390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4391_ = lean_ctor_get(v_inst_4388_, 1);
    lean_inc(v_toBind_4391_);
    v_type_4392_ = lean_ctor_get(v_param_4390_, 2);
    lean_inc_ref(v_type_4392_);
    v___x_4393_ = lean_box((v_pu_4386_) as usize);
    v___f_4394_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4394_, 0, v___x_4393_);
    lean_closure_set(v___f_4394_, 1, v_param_4390_);
    lean_closure_set(v___f_4394_, 2, v_inst_4387_);
    v___x_4395_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_4388_, v_f_4389_, v_type_4392_);
    v___x_4396_ = lean_apply_4(
        v_toBind_4391_,
        lean_box(0),
        lean_box(0),
        v___x_4395_,
        v___f_4394_,
    );
    return v___x_4396_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(
    mut v_pu_4397_: *mut LeanObject,
    mut v_inst_4398_: *mut LeanObject,
    mut v_inst_4399_: *mut LeanObject,
    mut v_f_4400_: *mut LeanObject,
    mut v_param_4401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4402_: u8 = 0;
    let mut v_res_4403_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4402_ = (lean_unbox(v_pu_4397_) as u8);
    v_res_4403_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_boxed_4402_,
        v_inst_4398_,
        v_inst_4399_,
        v_f_4400_,
        v_param_4401_,
    );
    return v_res_4403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM(
    mut v_m_4404_: *mut LeanObject,
    mut v_pu_4405_: u8,
    mut v_inst_4406_: *mut LeanObject,
    mut v_inst_4407_: *mut LeanObject,
    mut v_f_4408_: *mut LeanObject,
    mut v_param_4409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_4405_,
        v_inst_4406_,
        v_inst_4407_,
        v_f_4408_,
        v_param_4409_,
    );
    return v___x_4410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(
    mut v_m_4411_: *mut LeanObject,
    mut v_pu_4412_: *mut LeanObject,
    mut v_inst_4413_: *mut LeanObject,
    mut v_inst_4414_: *mut LeanObject,
    mut v_f_4415_: *mut LeanObject,
    mut v_param_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4417_: u8 = 0;
    let mut v_res_4418_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4417_ = (lean_unbox(v_pu_4412_) as u8);
    v_res_4418_ = l_Lean_Compiler_LCNF_Param_mapFVarM(
        v_m_4411_,
        v_pu_boxed_4417_,
        v_inst_4413_,
        v_inst_4414_,
        v_f_4415_,
        v_param_4416_,
    );
    return v_res_4418_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___redArg(
    mut v_inst_4419_: *mut LeanObject,
    mut v_f_4420_: *mut LeanObject,
    mut v_param_4421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    v_type_4422_ = lean_ctor_get(v_param_4421_, 2);
    lean_inc_ref(v_type_4422_);
    lean_dec_ref(v_param_4421_);
    v___x_4423_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_4419_, v_f_4420_, v_type_4422_);
    return v___x_4423_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM(
    mut v_m_4424_: *mut LeanObject,
    mut v_pu_4425_: u8,
    mut v_inst_4426_: *mut LeanObject,
    mut v_f_4427_: *mut LeanObject,
    mut v_param_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_4426_, v_f_4427_, v_param_4428_);
    return v___x_4429_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___boxed(
    mut v_m_4430_: *mut LeanObject,
    mut v_pu_4431_: *mut LeanObject,
    mut v_inst_4432_: *mut LeanObject,
    mut v_f_4433_: *mut LeanObject,
    mut v_param_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4435_: u8 = 0;
    let mut v_res_4436_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4435_ = (lean_unbox(v_pu_4431_) as u8);
    v_res_4436_ = l_Lean_Compiler_LCNF_Param_forFVarM(
        v_m_4430_,
        v_pu_boxed_4435_,
        v_inst_4432_,
        v_f_4433_,
        v_param_4434_,
    );
    return v_res_4436_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(
    mut v_pu_4437_: u8,
    mut v_m_4438_: *mut LeanObject,
    mut v_inst_4439_: *mut LeanObject,
    mut v_inst_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_4437_,
        v_inst_4439_,
        v_inst_4440_,
        v___y_4441_,
        v___y_4442_,
    );
    return v___x_4443_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(
    mut v_pu_4444_: *mut LeanObject,
    mut v_m_4445_: *mut LeanObject,
    mut v_inst_4446_: *mut LeanObject,
    mut v_inst_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4450_: u8 = 0;
    let mut v_res_4451_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4450_ = (lean_unbox(v_pu_4444_) as u8);
    v_res_4451_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(
        v_pu_boxed_4450_,
        v_m_4445_,
        v_inst_4446_,
        v_inst_4447_,
        v___y_4448_,
        v___y_4449_,
    );
    return v_res_4451_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(
    mut v_m_4452_: *mut LeanObject,
    mut v_inst_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    v___x_4456_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_4453_, v___y_4454_, v___y_4455_);
    return v___x_4456_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam(mut v_pu_4458_: u8) -> *mut LeanObject {
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    v___x_4459_ = lean_box((v_pu_4458_) as usize);
    v___f_4460_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4460_, 0, v___x_4459_);
    v___f_4461_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0;
    v___x_4462_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4462_, 0, v___f_4460_);
    lean_ctor_set(v___x_4462_, 1, v___f_4461_);
    return v___x_4462_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(
    mut v_pu_4463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4464_: u8 = 0;
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4464_ = (lean_unbox(v_pu_4463_) as u8);
    v_res_4465_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_4464_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(
    mut v_decl_4466_: *mut LeanObject,
    mut v_toPure_4467_: *mut LeanObject,
    mut v_c_4468_: *mut LeanObject,
    mut v_k_4469_: *mut LeanObject,
    mut v_decl_4470_: *mut LeanObject,
    mut v_____do__lift_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4473_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: usize = 0;
    let mut v___x_4478_: usize = 0;
    let mut v___x_4479_: u8 = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: usize = 0;
    let mut v___x_4482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4477_ = lean_ptr_addr(v_k_4469_);
                v___x_4478_ = lean_ptr_addr(v_____do__lift_4471_);
                v___x_4479_ = lean_usize_dec_eq(v___x_4477_, v___x_4478_);
                if v___x_4479_ == 0 {
                    v___y_4473_ = v___x_4479_;
                    state = 1;
                    continue;
                } else {
                    v___x_4480_ = lean_ptr_addr(v_decl_4470_);
                    v___x_4481_ = lean_ptr_addr(v_decl_4466_);
                    v___x_4482_ = lean_usize_dec_eq(v___x_4480_, v___x_4481_);
                    v___y_4473_ = v___x_4482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4473_ == 0 {
                    lean_dec_ref(v_c_4468_);
                    v___x_4474_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4474_, 0, v_decl_4466_);
                    lean_ctor_set(v___x_4474_, 1, v_____do__lift_4471_);
                    v___x_4475_ = lean_apply_2(v_toPure_4467_, lean_box(0), v___x_4474_);
                    return v___x_4475_;
                } else {
                    lean_dec_ref(v_____do__lift_4471_);
                    lean_dec_ref(v_decl_4466_);
                    v___x_4476_ = lean_apply_2(v_toPure_4467_, lean_box(0), v_c_4468_);
                    return v___x_4476_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(
    mut v_decl_4483_: *mut LeanObject,
    mut v_toPure_4484_: *mut LeanObject,
    mut v_c_4485_: *mut LeanObject,
    mut v_k_4486_: *mut LeanObject,
    mut v_decl_4487_: *mut LeanObject,
    mut v_____do__lift_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4489_: *mut LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(
        v_decl_4483_,
        v_toPure_4484_,
        v_c_4485_,
        v_k_4486_,
        v_decl_4487_,
        v_____do__lift_4488_,
    );
    lean_dec_ref(v_decl_4487_);
    lean_dec_ref(v_k_4486_);
    return v_res_4489_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(
    mut v_____do__lift_4490_: *mut LeanObject,
    mut v_i_4491_: *mut LeanObject,
    mut v_____do__lift_4492_: *mut LeanObject,
    mut v_toPure_4493_: *mut LeanObject,
    mut v_y_4494_: *mut LeanObject,
    mut v_k_4495_: *mut LeanObject,
    mut v_c_4496_: *mut LeanObject,
    mut v_fvarId_4497_: *mut LeanObject,
    mut v_____do__lift_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4500_: u8 = 0;
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: usize = 0;
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: usize = 0;
    let mut v___x_4515_: usize = 0;
    let mut v___x_4516_: u8 = 0;
    let mut v___x_4517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4514_ = lean_ptr_addr(v_fvarId_4497_);
                v___x_4515_ = lean_ptr_addr(v_____do__lift_4490_);
                v___x_4516_ = lean_usize_dec_eq(v___x_4514_, v___x_4515_);
                if v___x_4516_ == 0 {
                    v___y_4500_ = v___x_4516_;
                    state = 1;
                    continue;
                } else {
                    v___x_4517_ = lean_nat_dec_eq(v_i_4491_, v_i_4491_);
                    v___y_4500_ = v___x_4517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4500_ == 0 {
                    lean_dec_ref(v_c_4496_);
                    v___x_4501_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v___x_4501_, 0, v_____do__lift_4490_);
                    lean_ctor_set(v___x_4501_, 1, v_i_4491_);
                    lean_ctor_set(v___x_4501_, 2, v_____do__lift_4492_);
                    lean_ctor_set(v___x_4501_, 3, v_____do__lift_4498_);
                    v___x_4502_ = lean_apply_2(v_toPure_4493_, lean_box(0), v___x_4501_);
                    return v___x_4502_;
                } else {
                    v___x_4503_ = lean_ptr_addr(v_y_4494_);
                    v___x_4504_ = lean_ptr_addr(v_____do__lift_4492_);
                    v___x_4505_ = lean_usize_dec_eq(v___x_4503_, v___x_4504_);
                    if v___x_4505_ == 0 {
                        lean_dec_ref(v_c_4496_);
                        v___x_4506_ = lean_alloc_ctor(7, 4, (0) as u32);
                        lean_ctor_set(v___x_4506_, 0, v_____do__lift_4490_);
                        lean_ctor_set(v___x_4506_, 1, v_i_4491_);
                        lean_ctor_set(v___x_4506_, 2, v_____do__lift_4492_);
                        lean_ctor_set(v___x_4506_, 3, v_____do__lift_4498_);
                        v___x_4507_ = lean_apply_2(v_toPure_4493_, lean_box(0), v___x_4506_);
                        return v___x_4507_;
                    } else {
                        v___x_4508_ = lean_ptr_addr(v_k_4495_);
                        v___x_4509_ = lean_ptr_addr(v_____do__lift_4498_);
                        v___x_4510_ = lean_usize_dec_eq(v___x_4508_, v___x_4509_);
                        if v___x_4510_ == 0 {
                            lean_dec_ref(v_c_4496_);
                            v___x_4511_ = lean_alloc_ctor(7, 4, (0) as u32);
                            lean_ctor_set(v___x_4511_, 0, v_____do__lift_4490_);
                            lean_ctor_set(v___x_4511_, 1, v_i_4491_);
                            lean_ctor_set(v___x_4511_, 2, v_____do__lift_4492_);
                            lean_ctor_set(v___x_4511_, 3, v_____do__lift_4498_);
                            v___x_4512_ = lean_apply_2(v_toPure_4493_, lean_box(0), v___x_4511_);
                            return v___x_4512_;
                        } else {
                            lean_dec_ref(v_____do__lift_4498_);
                            lean_dec(v_____do__lift_4492_);
                            lean_dec(v_i_4491_);
                            lean_dec(v_____do__lift_4490_);
                            v___x_4513_ = lean_apply_2(v_toPure_4493_, lean_box(0), v_c_4496_);
                            return v___x_4513_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(
    mut v_____do__lift_4518_: *mut LeanObject,
    mut v_i_4519_: *mut LeanObject,
    mut v_____do__lift_4520_: *mut LeanObject,
    mut v_toPure_4521_: *mut LeanObject,
    mut v_y_4522_: *mut LeanObject,
    mut v_k_4523_: *mut LeanObject,
    mut v_c_4524_: *mut LeanObject,
    mut v_fvarId_4525_: *mut LeanObject,
    mut v_____do__lift_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4527_: *mut LeanObject = core::ptr::null_mut();
    v_res_4527_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(
        v_____do__lift_4518_,
        v_i_4519_,
        v_____do__lift_4520_,
        v_toPure_4521_,
        v_y_4522_,
        v_k_4523_,
        v_c_4524_,
        v_fvarId_4525_,
        v_____do__lift_4526_,
    );
    lean_dec(v_fvarId_4525_);
    lean_dec_ref(v_k_4523_);
    lean_dec(v_y_4522_);
    return v_res_4527_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(
    mut v_fvarId_4528_: *mut LeanObject,
    mut v_toPure_4529_: *mut LeanObject,
    mut v_c_4530_: *mut LeanObject,
    mut v_____do__lift_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4532_: u8 = 0;
    v___x_4532_ = l_Lean_instBEqFVarId_beq(v_fvarId_4528_, v_____do__lift_4531_);
    if v___x_4532_ == 0 {
        let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_c_4530_);
        v___x_4533_ = lean_alloc_ctor(5, 1, (0) as u32);
        lean_ctor_set(v___x_4533_, 0, v_____do__lift_4531_);
        v___x_4534_ = lean_apply_2(v_toPure_4529_, lean_box(0), v___x_4533_);
        return v___x_4534_;
    } else {
        let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_4531_);
        v___x_4535_ = lean_apply_2(v_toPure_4529_, lean_box(0), v_c_4530_);
        return v___x_4535_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(
    mut v_fvarId_4536_: *mut LeanObject,
    mut v_toPure_4537_: *mut LeanObject,
    mut v_c_4538_: *mut LeanObject,
    mut v_____do__lift_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4540_: *mut LeanObject = core::ptr::null_mut();
    v_res_4540_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(
        v_fvarId_4536_,
        v_toPure_4537_,
        v_c_4538_,
        v_____do__lift_4539_,
    );
    lean_dec(v_fvarId_4536_);
    return v_res_4540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(
    mut v_____do__lift_4541_: *mut LeanObject,
    mut v_cidx_4542_: *mut LeanObject,
    mut v_toPure_4543_: *mut LeanObject,
    mut v_k_4544_: *mut LeanObject,
    mut v_c_4545_: *mut LeanObject,
    mut v_fvarId_4546_: *mut LeanObject,
    mut v_____do__lift_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4549_: u8 = 0;
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: usize = 0;
    let mut v___x_4553_: usize = 0;
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4558_ = lean_ptr_addr(v_fvarId_4546_);
                v___x_4559_ = lean_ptr_addr(v_____do__lift_4541_);
                v___x_4560_ = lean_usize_dec_eq(v___x_4558_, v___x_4559_);
                if v___x_4560_ == 0 {
                    v___y_4549_ = v___x_4560_;
                    state = 1;
                    continue;
                } else {
                    v___x_4561_ = lean_nat_dec_eq(v_cidx_4542_, v_cidx_4542_);
                    v___y_4549_ = v___x_4561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4549_ == 0 {
                    lean_dec_ref(v_c_4545_);
                    v___x_4550_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v___x_4550_, 0, v_____do__lift_4541_);
                    lean_ctor_set(v___x_4550_, 1, v_cidx_4542_);
                    lean_ctor_set(v___x_4550_, 2, v_____do__lift_4547_);
                    v___x_4551_ = lean_apply_2(v_toPure_4543_, lean_box(0), v___x_4550_);
                    return v___x_4551_;
                } else {
                    v___x_4552_ = lean_ptr_addr(v_k_4544_);
                    v___x_4553_ = lean_ptr_addr(v_____do__lift_4547_);
                    v___x_4554_ = lean_usize_dec_eq(v___x_4552_, v___x_4553_);
                    if v___x_4554_ == 0 {
                        lean_dec_ref(v_c_4545_);
                        v___x_4555_ = lean_alloc_ctor(10, 3, (0) as u32);
                        lean_ctor_set(v___x_4555_, 0, v_____do__lift_4541_);
                        lean_ctor_set(v___x_4555_, 1, v_cidx_4542_);
                        lean_ctor_set(v___x_4555_, 2, v_____do__lift_4547_);
                        v___x_4556_ = lean_apply_2(v_toPure_4543_, lean_box(0), v___x_4555_);
                        return v___x_4556_;
                    } else {
                        lean_dec_ref(v_____do__lift_4547_);
                        lean_dec(v_cidx_4542_);
                        lean_dec(v_____do__lift_4541_);
                        v___x_4557_ = lean_apply_2(v_toPure_4543_, lean_box(0), v_c_4545_);
                        return v___x_4557_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(
    mut v_____do__lift_4562_: *mut LeanObject,
    mut v_cidx_4563_: *mut LeanObject,
    mut v_toPure_4564_: *mut LeanObject,
    mut v_k_4565_: *mut LeanObject,
    mut v_c_4566_: *mut LeanObject,
    mut v_fvarId_4567_: *mut LeanObject,
    mut v_____do__lift_4568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4569_: *mut LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(
        v_____do__lift_4562_,
        v_cidx_4563_,
        v_toPure_4564_,
        v_k_4565_,
        v_c_4566_,
        v_fvarId_4567_,
        v_____do__lift_4568_,
    );
    lean_dec(v_fvarId_4567_);
    lean_dec_ref(v_k_4565_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(
    mut v_____do__lift_4570_: *mut LeanObject,
    mut v_n_4571_: *mut LeanObject,
    mut v_check_4572_: u8,
    mut v_persistent_4573_: u8,
    mut v_toPure_4574_: *mut LeanObject,
    mut v_k_4575_: *mut LeanObject,
    mut v_c_4576_: *mut LeanObject,
    mut v_fvarId_4577_: *mut LeanObject,
    mut v_____do__lift_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4580_: u8 = 0;
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: usize = 0;
    let mut v___x_4584_: usize = 0;
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: usize = 0;
    let mut v___x_4590_: usize = 0;
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4589_ = lean_ptr_addr(v_fvarId_4577_);
                v___x_4590_ = lean_ptr_addr(v_____do__lift_4570_);
                v___x_4591_ = lean_usize_dec_eq(v___x_4589_, v___x_4590_);
                if v___x_4591_ == 0 {
                    v___y_4580_ = v___x_4591_;
                    state = 1;
                    continue;
                } else {
                    v___x_4592_ = lean_nat_dec_eq(v_n_4571_, v_n_4571_);
                    v___y_4580_ = v___x_4592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4580_ == 0 {
                    lean_dec_ref(v_c_4576_);
                    v___x_4581_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v___x_4581_, 0, v_____do__lift_4570_);
                    lean_ctor_set(v___x_4581_, 1, v_n_4571_);
                    lean_ctor_set(v___x_4581_, 2, v_____do__lift_4578_);
                    lean_ctor_set_uint8(
                        v___x_4581_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_4572_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4581_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_4573_,
                    );
                    v___x_4582_ = lean_apply_2(v_toPure_4574_, lean_box(0), v___x_4581_);
                    return v___x_4582_;
                } else {
                    v___x_4583_ = lean_ptr_addr(v_k_4575_);
                    v___x_4584_ = lean_ptr_addr(v_____do__lift_4578_);
                    v___x_4585_ = lean_usize_dec_eq(v___x_4583_, v___x_4584_);
                    if v___x_4585_ == 0 {
                        lean_dec_ref(v_c_4576_);
                        v___x_4586_ = lean_alloc_ctor(11, 3, (2) as u32);
                        lean_ctor_set(v___x_4586_, 0, v_____do__lift_4570_);
                        lean_ctor_set(v___x_4586_, 1, v_n_4571_);
                        lean_ctor_set(v___x_4586_, 2, v_____do__lift_4578_);
                        lean_ctor_set_uint8(
                            v___x_4586_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_check_4572_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4586_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_persistent_4573_,
                        );
                        v___x_4587_ = lean_apply_2(v_toPure_4574_, lean_box(0), v___x_4586_);
                        return v___x_4587_;
                    } else {
                        lean_dec_ref(v_____do__lift_4578_);
                        lean_dec(v_n_4571_);
                        lean_dec(v_____do__lift_4570_);
                        v___x_4588_ = lean_apply_2(v_toPure_4574_, lean_box(0), v_c_4576_);
                        return v___x_4588_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(
    mut v_____do__lift_4593_: *mut LeanObject,
    mut v_n_4594_: *mut LeanObject,
    mut v_check_4595_: *mut LeanObject,
    mut v_persistent_4596_: *mut LeanObject,
    mut v_toPure_4597_: *mut LeanObject,
    mut v_k_4598_: *mut LeanObject,
    mut v_c_4599_: *mut LeanObject,
    mut v_fvarId_4600_: *mut LeanObject,
    mut v_____do__lift_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_1824__boxed_4602_: u8 = 0;
    let mut v_persistent_1825__boxed_4603_: u8 = 0;
    let mut v_res_4604_: *mut LeanObject = core::ptr::null_mut();
    v_check_1824__boxed_4602_ = (lean_unbox(v_check_4595_) as u8);
    v_persistent_1825__boxed_4603_ = (lean_unbox(v_persistent_4596_) as u8);
    v_res_4604_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(
        v_____do__lift_4593_,
        v_n_4594_,
        v_check_1824__boxed_4602_,
        v_persistent_1825__boxed_4603_,
        v_toPure_4597_,
        v_k_4598_,
        v_c_4599_,
        v_fvarId_4600_,
        v_____do__lift_4601_,
    );
    lean_dec(v_fvarId_4600_);
    lean_dec_ref(v_k_4598_);
    return v_res_4604_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(
    mut v_____do__lift_4605_: *mut LeanObject,
    mut v_i_4606_: *mut LeanObject,
    mut v_offset_4607_: *mut LeanObject,
    mut v_____do__lift_4608_: *mut LeanObject,
    mut v_____do__lift_4609_: *mut LeanObject,
    mut v_toPure_4610_: *mut LeanObject,
    mut v_y_4611_: *mut LeanObject,
    mut v_ty_4612_: *mut LeanObject,
    mut v_k_4613_: *mut LeanObject,
    mut v_c_4614_: *mut LeanObject,
    mut v_fvarId_4615_: *mut LeanObject,
    mut v_____do__lift_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4618_: u8 = 0;
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: usize = 0;
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: usize = 0;
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4640_ = lean_ptr_addr(v_fvarId_4615_);
                v___x_4641_ = lean_ptr_addr(v_____do__lift_4605_);
                v___x_4642_ = lean_usize_dec_eq(v___x_4640_, v___x_4641_);
                if v___x_4642_ == 0 {
                    v___y_4618_ = v___x_4642_;
                    state = 1;
                    continue;
                } else {
                    v___x_4643_ = lean_nat_dec_eq(v_i_4606_, v_i_4606_);
                    v___y_4618_ = v___x_4643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4618_ == 0 {
                    lean_dec_ref(v_c_4614_);
                    v___x_4619_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v___x_4619_, 0, v_____do__lift_4605_);
                    lean_ctor_set(v___x_4619_, 1, v_i_4606_);
                    lean_ctor_set(v___x_4619_, 2, v_offset_4607_);
                    lean_ctor_set(v___x_4619_, 3, v_____do__lift_4608_);
                    lean_ctor_set(v___x_4619_, 4, v_____do__lift_4609_);
                    lean_ctor_set(v___x_4619_, 5, v_____do__lift_4616_);
                    v___x_4620_ = lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4619_);
                    return v___x_4620_;
                } else {
                    v___x_4621_ = lean_nat_dec_eq(v_offset_4607_, v_offset_4607_);
                    if v___x_4621_ == 0 {
                        lean_dec_ref(v_c_4614_);
                        v___x_4622_ = lean_alloc_ctor(9, 6, (0) as u32);
                        lean_ctor_set(v___x_4622_, 0, v_____do__lift_4605_);
                        lean_ctor_set(v___x_4622_, 1, v_i_4606_);
                        lean_ctor_set(v___x_4622_, 2, v_offset_4607_);
                        lean_ctor_set(v___x_4622_, 3, v_____do__lift_4608_);
                        lean_ctor_set(v___x_4622_, 4, v_____do__lift_4609_);
                        lean_ctor_set(v___x_4622_, 5, v_____do__lift_4616_);
                        v___x_4623_ = lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4622_);
                        return v___x_4623_;
                    } else {
                        v___x_4624_ = lean_ptr_addr(v_y_4611_);
                        v___x_4625_ = lean_ptr_addr(v_____do__lift_4608_);
                        v___x_4626_ = lean_usize_dec_eq(v___x_4624_, v___x_4625_);
                        if v___x_4626_ == 0 {
                            lean_dec_ref(v_c_4614_);
                            v___x_4627_ = lean_alloc_ctor(9, 6, (0) as u32);
                            lean_ctor_set(v___x_4627_, 0, v_____do__lift_4605_);
                            lean_ctor_set(v___x_4627_, 1, v_i_4606_);
                            lean_ctor_set(v___x_4627_, 2, v_offset_4607_);
                            lean_ctor_set(v___x_4627_, 3, v_____do__lift_4608_);
                            lean_ctor_set(v___x_4627_, 4, v_____do__lift_4609_);
                            lean_ctor_set(v___x_4627_, 5, v_____do__lift_4616_);
                            v___x_4628_ = lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4627_);
                            return v___x_4628_;
                        } else {
                            v___x_4629_ = lean_ptr_addr(v_ty_4612_);
                            v___x_4630_ = lean_ptr_addr(v_____do__lift_4609_);
                            v___x_4631_ = lean_usize_dec_eq(v___x_4629_, v___x_4630_);
                            if v___x_4631_ == 0 {
                                lean_dec_ref(v_c_4614_);
                                v___x_4632_ = lean_alloc_ctor(9, 6, (0) as u32);
                                lean_ctor_set(v___x_4632_, 0, v_____do__lift_4605_);
                                lean_ctor_set(v___x_4632_, 1, v_i_4606_);
                                lean_ctor_set(v___x_4632_, 2, v_offset_4607_);
                                lean_ctor_set(v___x_4632_, 3, v_____do__lift_4608_);
                                lean_ctor_set(v___x_4632_, 4, v_____do__lift_4609_);
                                lean_ctor_set(v___x_4632_, 5, v_____do__lift_4616_);
                                v___x_4633_ =
                                    lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4632_);
                                return v___x_4633_;
                            } else {
                                v___x_4634_ = lean_ptr_addr(v_k_4613_);
                                v___x_4635_ = lean_ptr_addr(v_____do__lift_4616_);
                                v___x_4636_ = lean_usize_dec_eq(v___x_4634_, v___x_4635_);
                                if v___x_4636_ == 0 {
                                    lean_dec_ref(v_c_4614_);
                                    v___x_4637_ = lean_alloc_ctor(9, 6, (0) as u32);
                                    lean_ctor_set(v___x_4637_, 0, v_____do__lift_4605_);
                                    lean_ctor_set(v___x_4637_, 1, v_i_4606_);
                                    lean_ctor_set(v___x_4637_, 2, v_offset_4607_);
                                    lean_ctor_set(v___x_4637_, 3, v_____do__lift_4608_);
                                    lean_ctor_set(v___x_4637_, 4, v_____do__lift_4609_);
                                    lean_ctor_set(v___x_4637_, 5, v_____do__lift_4616_);
                                    v___x_4638_ =
                                        lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4637_);
                                    return v___x_4638_;
                                } else {
                                    lean_dec_ref(v_____do__lift_4616_);
                                    lean_dec_ref(v_____do__lift_4609_);
                                    lean_dec(v_____do__lift_4608_);
                                    lean_dec(v_offset_4607_);
                                    lean_dec(v_i_4606_);
                                    lean_dec(v_____do__lift_4605_);
                                    v___x_4639_ =
                                        lean_apply_2(v_toPure_4610_, lean_box(0), v_c_4614_);
                                    return v___x_4639_;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(
    mut v_____do__lift_4644_: *mut LeanObject,
    mut v_i_4645_: *mut LeanObject,
    mut v_offset_4646_: *mut LeanObject,
    mut v_____do__lift_4647_: *mut LeanObject,
    mut v_____do__lift_4648_: *mut LeanObject,
    mut v_toPure_4649_: *mut LeanObject,
    mut v_y_4650_: *mut LeanObject,
    mut v_ty_4651_: *mut LeanObject,
    mut v_k_4652_: *mut LeanObject,
    mut v_c_4653_: *mut LeanObject,
    mut v_fvarId_4654_: *mut LeanObject,
    mut v_____do__lift_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4656_: *mut LeanObject = core::ptr::null_mut();
    v_res_4656_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(
        v_____do__lift_4644_,
        v_i_4645_,
        v_offset_4646_,
        v_____do__lift_4647_,
        v_____do__lift_4648_,
        v_toPure_4649_,
        v_y_4650_,
        v_ty_4651_,
        v_k_4652_,
        v_c_4653_,
        v_fvarId_4654_,
        v_____do__lift_4655_,
    );
    lean_dec(v_fvarId_4654_);
    lean_dec_ref(v_k_4652_);
    lean_dec_ref(v_ty_4651_);
    lean_dec(v_y_4650_);
    return v_res_4656_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(
    mut v_pu_4657_: u8,
    mut v_decl_4658_: *mut LeanObject,
    mut v_____do__lift_4659_: *mut LeanObject,
    mut v_params_4660_: *mut LeanObject,
    mut v_inst_4661_: *mut LeanObject,
    mut v_toBind_4662_: *mut LeanObject,
    mut v___f_4663_: *mut LeanObject,
    mut v_____do__lift_4664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665_ = lean_box((v_pu_4657_) as usize);
    v___x_4666_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___x_4666_, 0, v___x_4665_);
    lean_closure_set(v___x_4666_, 1, v_decl_4658_);
    lean_closure_set(v___x_4666_, 2, v_____do__lift_4659_);
    lean_closure_set(v___x_4666_, 3, v_params_4660_);
    lean_closure_set(v___x_4666_, 4, v_____do__lift_4664_);
    v___x_4667_ = lean_apply_2(v_inst_4661_, lean_box(0), v___x_4666_);
    v___x_4668_ = lean_apply_4(
        v_toBind_4662_,
        lean_box(0),
        lean_box(0),
        v___x_4667_,
        v___f_4663_,
    );
    return v___x_4668_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(
    mut v_pu_4669_: *mut LeanObject,
    mut v_decl_4670_: *mut LeanObject,
    mut v_____do__lift_4671_: *mut LeanObject,
    mut v_params_4672_: *mut LeanObject,
    mut v_inst_4673_: *mut LeanObject,
    mut v_toBind_4674_: *mut LeanObject,
    mut v___f_4675_: *mut LeanObject,
    mut v_____do__lift_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4677_: u8 = 0;
    let mut v_res_4678_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4677_ = (lean_unbox(v_pu_4669_) as u8);
    v_res_4678_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(
        v_pu_boxed_4677_,
        v_decl_4670_,
        v_____do__lift_4671_,
        v_params_4672_,
        v_inst_4673_,
        v_toBind_4674_,
        v___f_4675_,
        v_____do__lift_4676_,
    );
    return v_res_4678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(
    mut v_____do__lift_4679_: *mut LeanObject,
    mut v_toPure_4680_: *mut LeanObject,
    mut v_c_4681_: *mut LeanObject,
    mut v_fvarId_4682_: *mut LeanObject,
    mut v_args_4683_: *mut LeanObject,
    mut v_____do__lift_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4686_: u8 = 0;
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: usize = 0;
    let mut v___x_4692_: usize = 0;
    let mut v___x_4693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4690_ = l_Lean_instBEqFVarId_beq(v_fvarId_4682_, v_____do__lift_4679_);
                if v___x_4690_ == 0 {
                    v___y_4686_ = v___x_4690_;
                    state = 1;
                    continue;
                } else {
                    v___x_4691_ = lean_ptr_addr(v_args_4683_);
                    v___x_4692_ = lean_ptr_addr(v_____do__lift_4684_);
                    v___x_4693_ = lean_usize_dec_eq(v___x_4691_, v___x_4692_);
                    v___y_4686_ = v___x_4693_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4686_ == 0 {
                    lean_dec_ref(v_c_4681_);
                    v___x_4687_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_4687_, 0, v_____do__lift_4679_);
                    lean_ctor_set(v___x_4687_, 1, v_____do__lift_4684_);
                    v___x_4688_ = lean_apply_2(v_toPure_4680_, lean_box(0), v___x_4687_);
                    return v___x_4688_;
                } else {
                    lean_dec_ref(v_____do__lift_4684_);
                    lean_dec(v_____do__lift_4679_);
                    v___x_4689_ = lean_apply_2(v_toPure_4680_, lean_box(0), v_c_4681_);
                    return v___x_4689_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(
    mut v_____do__lift_4694_: *mut LeanObject,
    mut v_toPure_4695_: *mut LeanObject,
    mut v_c_4696_: *mut LeanObject,
    mut v_fvarId_4697_: *mut LeanObject,
    mut v_args_4698_: *mut LeanObject,
    mut v_____do__lift_4699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4700_: *mut LeanObject = core::ptr::null_mut();
    v_res_4700_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(
        v_____do__lift_4694_,
        v_toPure_4695_,
        v_c_4696_,
        v_fvarId_4697_,
        v_args_4698_,
        v_____do__lift_4699_,
    );
    lean_dec_ref(v_args_4698_);
    lean_dec(v_fvarId_4697_);
    return v_res_4700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(
    mut v_toPure_4701_: *mut LeanObject,
    mut v_c_4702_: *mut LeanObject,
    mut v_fvarId_4703_: *mut LeanObject,
    mut v_args_4704_: *mut LeanObject,
    mut v_pu_4705_: u8,
    mut v_inst_4706_: *mut LeanObject,
    mut v_inst_4707_: *mut LeanObject,
    mut v_f_4708_: *mut LeanObject,
    mut v_toBind_4709_: *mut LeanObject,
    mut v_____do__lift_4710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4714_: usize = 0;
    let mut v___x_4715_: usize = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_args_4704_);
    v___f_4711_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4711_, 0, v_____do__lift_4710_);
    lean_closure_set(v___f_4711_, 1, v_toPure_4701_);
    lean_closure_set(v___f_4711_, 2, v_c_4702_);
    lean_closure_set(v___f_4711_, 3, v_fvarId_4703_);
    lean_closure_set(v___f_4711_, 4, v_args_4704_);
    v___x_4712_ = lean_box((v_pu_4705_) as usize);
    lean_inc_ref(v_inst_4707_);
    v___x_4713_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_4713_, 0, lean_box(0));
    lean_closure_set(v___x_4713_, 1, v___x_4712_);
    lean_closure_set(v___x_4713_, 2, v_inst_4706_);
    lean_closure_set(v___x_4713_, 3, v_inst_4707_);
    lean_closure_set(v___x_4713_, 4, v_f_4708_);
    v_sz_4714_ = lean_array_size(v_args_4704_);
    v___x_4715_ = 0usize;
    v___x_4716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_4707_,
        v___x_4713_,
        v_sz_4714_,
        v___x_4715_,
        v_args_4704_,
    );
    v___x_4717_ = lean_apply_4(
        v_toBind_4709_,
        lean_box(0),
        lean_box(0),
        v___x_4716_,
        v___f_4711_,
    );
    return v___x_4717_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(
    mut v_toPure_4718_: *mut LeanObject,
    mut v_c_4719_: *mut LeanObject,
    mut v_fvarId_4720_: *mut LeanObject,
    mut v_args_4721_: *mut LeanObject,
    mut v_pu_4722_: *mut LeanObject,
    mut v_inst_4723_: *mut LeanObject,
    mut v_inst_4724_: *mut LeanObject,
    mut v_f_4725_: *mut LeanObject,
    mut v_toBind_4726_: *mut LeanObject,
    mut v_____do__lift_4727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4728_: u8 = 0;
    let mut v_res_4729_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4728_ = (lean_unbox(v_pu_4722_) as u8);
    v_res_4729_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(
        v_toPure_4718_,
        v_c_4719_,
        v_fvarId_4720_,
        v_args_4721_,
        v_pu_boxed_4728_,
        v_inst_4723_,
        v_inst_4724_,
        v_f_4725_,
        v_toBind_4726_,
        v_____do__lift_4727_,
    );
    return v_res_4729_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(
    mut v_typeName_4730_: *mut LeanObject,
    mut v_____do__lift_4731_: *mut LeanObject,
    mut v_____do__lift_4732_: *mut LeanObject,
    mut v_toPure_4733_: *mut LeanObject,
    mut v_discr_4734_: *mut LeanObject,
    mut v_c_4735_: *mut LeanObject,
    mut v_alts_4736_: *mut LeanObject,
    mut v_resultType_4737_: *mut LeanObject,
    mut v_____do__lift_4738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: u8 = 0;
    let mut v___x_4745_: u8 = 0;
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: usize = 0;
    let mut v___x_4748_: usize = 0;
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4747_ = lean_ptr_addr(v_alts_4736_);
                v___x_4748_ = lean_ptr_addr(v_____do__lift_4738_);
                v___x_4749_ = lean_usize_dec_eq(v___x_4747_, v___x_4748_);
                if v___x_4749_ == 0 {
                    v___y_4744_ = v___x_4749_;
                    state = 2;
                    continue;
                } else {
                    v___x_4750_ = lean_ptr_addr(v_resultType_4737_);
                    v___x_4751_ = lean_ptr_addr(v_____do__lift_4731_);
                    v___x_4752_ = lean_usize_dec_eq(v___x_4750_, v___x_4751_);
                    v___y_4744_ = v___x_4752_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4740_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4740_, 0, v_typeName_4730_);
                lean_ctor_set(v___x_4740_, 1, v_____do__lift_4731_);
                lean_ctor_set(v___x_4740_, 2, v_____do__lift_4732_);
                lean_ctor_set(v___x_4740_, 3, v_____do__lift_4738_);
                v___x_4741_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_4741_, 0, v___x_4740_);
                v___x_4742_ = lean_apply_2(v_toPure_4733_, lean_box(0), v___x_4741_);
                return v___x_4742_;
            }
            2 => {
                if v___y_4744_ == 0 {
                    lean_dec_ref(v_c_4735_);
                    state = 1;
                    continue;
                } else {
                    v___x_4745_ = l_Lean_instBEqFVarId_beq(v_discr_4734_, v_____do__lift_4732_);
                    if v___x_4745_ == 0 {
                        lean_dec_ref(v_c_4735_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_____do__lift_4738_);
                        lean_dec(v_____do__lift_4732_);
                        lean_dec_ref(v_____do__lift_4731_);
                        lean_dec(v_typeName_4730_);
                        v___x_4746_ = lean_apply_2(v_toPure_4733_, lean_box(0), v_c_4735_);
                        return v___x_4746_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(
    mut v_typeName_4753_: *mut LeanObject,
    mut v_____do__lift_4754_: *mut LeanObject,
    mut v_____do__lift_4755_: *mut LeanObject,
    mut v_toPure_4756_: *mut LeanObject,
    mut v_discr_4757_: *mut LeanObject,
    mut v_c_4758_: *mut LeanObject,
    mut v_alts_4759_: *mut LeanObject,
    mut v_resultType_4760_: *mut LeanObject,
    mut v_____do__lift_4761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4762_: *mut LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(
        v_typeName_4753_,
        v_____do__lift_4754_,
        v_____do__lift_4755_,
        v_toPure_4756_,
        v_discr_4757_,
        v_c_4758_,
        v_alts_4759_,
        v_resultType_4760_,
        v_____do__lift_4761_,
    );
    lean_dec_ref(v_resultType_4760_);
    lean_dec_ref(v_alts_4759_);
    lean_dec(v_discr_4757_);
    return v_res_4762_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(
    mut v_typeName_4763_: *mut LeanObject,
    mut v_____do__lift_4764_: *mut LeanObject,
    mut v_toPure_4765_: *mut LeanObject,
    mut v_discr_4766_: *mut LeanObject,
    mut v_c_4767_: *mut LeanObject,
    mut v_alts_4768_: *mut LeanObject,
    mut v_resultType_4769_: *mut LeanObject,
    mut v_inst_4770_: *mut LeanObject,
    mut v___f_4771_: *mut LeanObject,
    mut v_toBind_4772_: *mut LeanObject,
    mut v_____do__lift_4773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_alts_4768_);
    v___f_4774_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_4774_, 0, v_typeName_4763_);
    lean_closure_set(v___f_4774_, 1, v_____do__lift_4764_);
    lean_closure_set(v___f_4774_, 2, v_____do__lift_4773_);
    lean_closure_set(v___f_4774_, 3, v_toPure_4765_);
    lean_closure_set(v___f_4774_, 4, v_discr_4766_);
    lean_closure_set(v___f_4774_, 5, v_c_4767_);
    lean_closure_set(v___f_4774_, 6, v_alts_4768_);
    lean_closure_set(v___f_4774_, 7, v_resultType_4769_);
    v___x_4775_ = lean_unsigned_to_nat(0);
    v___x_4776_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(
        lean_box(0),
        lean_box(0),
        v_inst_4770_,
        v___f_4771_,
        v___x_4775_,
        v_alts_4768_,
    );
    v___x_4777_ = lean_apply_4(
        v_toBind_4772_,
        lean_box(0),
        lean_box(0),
        v___x_4776_,
        v___f_4774_,
    );
    return v___x_4777_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(
    mut v_typeName_4778_: *mut LeanObject,
    mut v_toPure_4779_: *mut LeanObject,
    mut v_discr_4780_: *mut LeanObject,
    mut v_c_4781_: *mut LeanObject,
    mut v_alts_4782_: *mut LeanObject,
    mut v_resultType_4783_: *mut LeanObject,
    mut v_inst_4784_: *mut LeanObject,
    mut v___f_4785_: *mut LeanObject,
    mut v_toBind_4786_: *mut LeanObject,
    mut v_f_4787_: *mut LeanObject,
    mut v_____do__lift_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_4786_);
    lean_inc(v_discr_4780_);
    v___f_4789_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_4789_, 0, v_typeName_4778_);
    lean_closure_set(v___f_4789_, 1, v_____do__lift_4788_);
    lean_closure_set(v___f_4789_, 2, v_toPure_4779_);
    lean_closure_set(v___f_4789_, 3, v_discr_4780_);
    lean_closure_set(v___f_4789_, 4, v_c_4781_);
    lean_closure_set(v___f_4789_, 5, v_alts_4782_);
    lean_closure_set(v___f_4789_, 6, v_resultType_4783_);
    lean_closure_set(v___f_4789_, 7, v_inst_4784_);
    lean_closure_set(v___f_4789_, 8, v___f_4785_);
    lean_closure_set(v___f_4789_, 9, v_toBind_4786_);
    v___x_4790_ = lean_apply_1(v_f_4787_, v_discr_4780_);
    v___x_4791_ = lean_apply_4(
        v_toBind_4786_,
        lean_box(0),
        lean_box(0),
        v___x_4790_,
        v___f_4789_,
    );
    return v___x_4791_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(
    mut v_____do__lift_4792_: *mut LeanObject,
    mut v_n_4793_: *mut LeanObject,
    mut v_check_4794_: u8,
    mut v_persistent_4795_: u8,
    mut v_objs_x3f_4796_: *mut LeanObject,
    mut v_toPure_4797_: *mut LeanObject,
    mut v_k_4798_: *mut LeanObject,
    mut v_c_4799_: *mut LeanObject,
    mut v_fvarId_4800_: *mut LeanObject,
    mut v_____do__lift_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4803_: u8 = 0;
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: usize = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: usize = 0;
    let mut v___x_4817_: usize = 0;
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4816_ = lean_ptr_addr(v_fvarId_4800_);
                v___x_4817_ = lean_ptr_addr(v_____do__lift_4792_);
                v___x_4818_ = lean_usize_dec_eq(v___x_4816_, v___x_4817_);
                if v___x_4818_ == 0 {
                    v___y_4803_ = v___x_4818_;
                    state = 1;
                    continue;
                } else {
                    v___x_4819_ = lean_nat_dec_eq(v_n_4793_, v_n_4793_);
                    v___y_4803_ = v___x_4819_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4803_ == 0 {
                    lean_dec_ref(v_c_4799_);
                    v___x_4804_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v___x_4804_, 0, v_____do__lift_4792_);
                    lean_ctor_set(v___x_4804_, 1, v_n_4793_);
                    lean_ctor_set(v___x_4804_, 2, v_objs_x3f_4796_);
                    lean_ctor_set(v___x_4804_, 3, v_____do__lift_4801_);
                    lean_ctor_set_uint8(
                        v___x_4804_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_4794_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4804_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_4795_,
                    );
                    v___x_4805_ = lean_apply_2(v_toPure_4797_, lean_box(0), v___x_4804_);
                    return v___x_4805_;
                } else {
                    v___x_4806_ = lean_ptr_addr(v_objs_x3f_4796_);
                    v___x_4807_ = lean_usize_dec_eq(v___x_4806_, v___x_4806_);
                    if v___x_4807_ == 0 {
                        lean_dec_ref(v_c_4799_);
                        v___x_4808_ = lean_alloc_ctor(12, 4, (2) as u32);
                        lean_ctor_set(v___x_4808_, 0, v_____do__lift_4792_);
                        lean_ctor_set(v___x_4808_, 1, v_n_4793_);
                        lean_ctor_set(v___x_4808_, 2, v_objs_x3f_4796_);
                        lean_ctor_set(v___x_4808_, 3, v_____do__lift_4801_);
                        lean_ctor_set_uint8(
                            v___x_4808_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                            v_check_4794_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4808_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                            v_persistent_4795_,
                        );
                        v___x_4809_ = lean_apply_2(v_toPure_4797_, lean_box(0), v___x_4808_);
                        return v___x_4809_;
                    } else {
                        v___x_4810_ = lean_ptr_addr(v_k_4798_);
                        v___x_4811_ = lean_ptr_addr(v_____do__lift_4801_);
                        v___x_4812_ = lean_usize_dec_eq(v___x_4810_, v___x_4811_);
                        if v___x_4812_ == 0 {
                            lean_dec_ref(v_c_4799_);
                            v___x_4813_ = lean_alloc_ctor(12, 4, (2) as u32);
                            lean_ctor_set(v___x_4813_, 0, v_____do__lift_4792_);
                            lean_ctor_set(v___x_4813_, 1, v_n_4793_);
                            lean_ctor_set(v___x_4813_, 2, v_objs_x3f_4796_);
                            lean_ctor_set(v___x_4813_, 3, v_____do__lift_4801_);
                            lean_ctor_set_uint8(
                                v___x_4813_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                v_check_4794_,
                            );
                            lean_ctor_set_uint8(
                                v___x_4813_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                                v_persistent_4795_,
                            );
                            v___x_4814_ = lean_apply_2(v_toPure_4797_, lean_box(0), v___x_4813_);
                            return v___x_4814_;
                        } else {
                            lean_dec_ref(v_____do__lift_4801_);
                            lean_dec(v_objs_x3f_4796_);
                            lean_dec(v_n_4793_);
                            lean_dec(v_____do__lift_4792_);
                            v___x_4815_ = lean_apply_2(v_toPure_4797_, lean_box(0), v_c_4799_);
                            return v___x_4815_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(
    mut v_____do__lift_4820_: *mut LeanObject,
    mut v_n_4821_: *mut LeanObject,
    mut v_check_4822_: *mut LeanObject,
    mut v_persistent_4823_: *mut LeanObject,
    mut v_objs_x3f_4824_: *mut LeanObject,
    mut v_toPure_4825_: *mut LeanObject,
    mut v_k_4826_: *mut LeanObject,
    mut v_c_4827_: *mut LeanObject,
    mut v_fvarId_4828_: *mut LeanObject,
    mut v_____do__lift_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_2130__boxed_4830_: u8 = 0;
    let mut v_persistent_2131__boxed_4831_: u8 = 0;
    let mut v_res_4832_: *mut LeanObject = core::ptr::null_mut();
    v_check_2130__boxed_4830_ = (lean_unbox(v_check_4822_) as u8);
    v_persistent_2131__boxed_4831_ = (lean_unbox(v_persistent_4823_) as u8);
    v_res_4832_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(
        v_____do__lift_4820_,
        v_n_4821_,
        v_check_2130__boxed_4830_,
        v_persistent_2131__boxed_4831_,
        v_objs_x3f_4824_,
        v_toPure_4825_,
        v_k_4826_,
        v_c_4827_,
        v_fvarId_4828_,
        v_____do__lift_4829_,
    );
    lean_dec(v_fvarId_4828_);
    lean_dec_ref(v_k_4826_);
    return v_res_4832_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(
    mut v_decl_4833_: *mut LeanObject,
    mut v_toPure_4834_: *mut LeanObject,
    mut v_c_4835_: *mut LeanObject,
    mut v_k_4836_: *mut LeanObject,
    mut v_decl_4837_: *mut LeanObject,
    mut v_____do__lift_4838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4840_: u8 = 0;
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v___x_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4844_ = lean_ptr_addr(v_k_4836_);
                v___x_4845_ = lean_ptr_addr(v_____do__lift_4838_);
                v___x_4846_ = lean_usize_dec_eq(v___x_4844_, v___x_4845_);
                if v___x_4846_ == 0 {
                    v___y_4840_ = v___x_4846_;
                    state = 1;
                    continue;
                } else {
                    v___x_4847_ = lean_ptr_addr(v_decl_4837_);
                    v___x_4848_ = lean_ptr_addr(v_decl_4833_);
                    v___x_4849_ = lean_usize_dec_eq(v___x_4847_, v___x_4848_);
                    v___y_4840_ = v___x_4849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4840_ == 0 {
                    lean_dec_ref(v_c_4835_);
                    v___x_4841_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4841_, 0, v_decl_4833_);
                    lean_ctor_set(v___x_4841_, 1, v_____do__lift_4838_);
                    v___x_4842_ = lean_apply_2(v_toPure_4834_, lean_box(0), v___x_4841_);
                    return v___x_4842_;
                } else {
                    lean_dec_ref(v_____do__lift_4838_);
                    lean_dec_ref(v_decl_4833_);
                    v___x_4843_ = lean_apply_2(v_toPure_4834_, lean_box(0), v_c_4835_);
                    return v___x_4843_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(
    mut v_decl_4850_: *mut LeanObject,
    mut v_toPure_4851_: *mut LeanObject,
    mut v_c_4852_: *mut LeanObject,
    mut v_k_4853_: *mut LeanObject,
    mut v_decl_4854_: *mut LeanObject,
    mut v_____do__lift_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4856_: *mut LeanObject = core::ptr::null_mut();
    v_res_4856_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(
        v_decl_4850_,
        v_toPure_4851_,
        v_c_4852_,
        v_k_4853_,
        v_decl_4854_,
        v_____do__lift_4855_,
    );
    lean_dec_ref(v_decl_4854_);
    lean_dec_ref(v_k_4853_);
    return v_res_4856_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(
    mut v_decl_4857_: *mut LeanObject,
    mut v_toPure_4858_: *mut LeanObject,
    mut v_c_4859_: *mut LeanObject,
    mut v_k_4860_: *mut LeanObject,
    mut v_decl_4861_: *mut LeanObject,
    mut v_____do__lift_4862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4864_: u8 = 0;
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: usize = 0;
    let mut v___x_4869_: usize = 0;
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: usize = 0;
    let mut v___x_4873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4868_ = lean_ptr_addr(v_k_4860_);
                v___x_4869_ = lean_ptr_addr(v_____do__lift_4862_);
                v___x_4870_ = lean_usize_dec_eq(v___x_4868_, v___x_4869_);
                if v___x_4870_ == 0 {
                    v___y_4864_ = v___x_4870_;
                    state = 1;
                    continue;
                } else {
                    v___x_4871_ = lean_ptr_addr(v_decl_4861_);
                    v___x_4872_ = lean_ptr_addr(v_decl_4857_);
                    v___x_4873_ = lean_usize_dec_eq(v___x_4871_, v___x_4872_);
                    v___y_4864_ = v___x_4873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4864_ == 0 {
                    lean_dec_ref(v_c_4859_);
                    v___x_4865_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4865_, 0, v_decl_4857_);
                    lean_ctor_set(v___x_4865_, 1, v_____do__lift_4862_);
                    v___x_4866_ = lean_apply_2(v_toPure_4858_, lean_box(0), v___x_4865_);
                    return v___x_4866_;
                } else {
                    lean_dec_ref(v_____do__lift_4862_);
                    lean_dec_ref(v_decl_4857_);
                    v___x_4867_ = lean_apply_2(v_toPure_4858_, lean_box(0), v_c_4859_);
                    return v___x_4867_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(
    mut v_decl_4874_: *mut LeanObject,
    mut v_toPure_4875_: *mut LeanObject,
    mut v_c_4876_: *mut LeanObject,
    mut v_k_4877_: *mut LeanObject,
    mut v_decl_4878_: *mut LeanObject,
    mut v_____do__lift_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4880_: *mut LeanObject = core::ptr::null_mut();
    v_res_4880_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(
        v_decl_4874_,
        v_toPure_4875_,
        v_c_4876_,
        v_k_4877_,
        v_decl_4878_,
        v_____do__lift_4879_,
    );
    lean_dec_ref(v_decl_4878_);
    lean_dec_ref(v_k_4877_);
    return v_res_4880_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(
    mut v_____do__lift_4881_: *mut LeanObject,
    mut v_i_4882_: *mut LeanObject,
    mut v_____do__lift_4883_: *mut LeanObject,
    mut v_toPure_4884_: *mut LeanObject,
    mut v_y_4885_: *mut LeanObject,
    mut v_k_4886_: *mut LeanObject,
    mut v_c_4887_: *mut LeanObject,
    mut v_fvarId_4888_: *mut LeanObject,
    mut v_____do__lift_4889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4891_: u8 = 0;
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: usize = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: u8 = 0;
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: u8 = 0;
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: usize = 0;
    let mut v___x_4906_: usize = 0;
    let mut v___x_4907_: u8 = 0;
    let mut v___x_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4905_ = lean_ptr_addr(v_fvarId_4888_);
                v___x_4906_ = lean_ptr_addr(v_____do__lift_4881_);
                v___x_4907_ = lean_usize_dec_eq(v___x_4905_, v___x_4906_);
                if v___x_4907_ == 0 {
                    v___y_4891_ = v___x_4907_;
                    state = 1;
                    continue;
                } else {
                    v___x_4908_ = lean_nat_dec_eq(v_i_4882_, v_i_4882_);
                    v___y_4891_ = v___x_4908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4891_ == 0 {
                    lean_dec_ref(v_c_4887_);
                    v___x_4892_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v___x_4892_, 0, v_____do__lift_4881_);
                    lean_ctor_set(v___x_4892_, 1, v_i_4882_);
                    lean_ctor_set(v___x_4892_, 2, v_____do__lift_4883_);
                    lean_ctor_set(v___x_4892_, 3, v_____do__lift_4889_);
                    v___x_4893_ = lean_apply_2(v_toPure_4884_, lean_box(0), v___x_4892_);
                    return v___x_4893_;
                } else {
                    v___x_4894_ = lean_ptr_addr(v_y_4885_);
                    v___x_4895_ = lean_ptr_addr(v_____do__lift_4883_);
                    v___x_4896_ = lean_usize_dec_eq(v___x_4894_, v___x_4895_);
                    if v___x_4896_ == 0 {
                        lean_dec_ref(v_c_4887_);
                        v___x_4897_ = lean_alloc_ctor(8, 4, (0) as u32);
                        lean_ctor_set(v___x_4897_, 0, v_____do__lift_4881_);
                        lean_ctor_set(v___x_4897_, 1, v_i_4882_);
                        lean_ctor_set(v___x_4897_, 2, v_____do__lift_4883_);
                        lean_ctor_set(v___x_4897_, 3, v_____do__lift_4889_);
                        v___x_4898_ = lean_apply_2(v_toPure_4884_, lean_box(0), v___x_4897_);
                        return v___x_4898_;
                    } else {
                        v___x_4899_ = lean_ptr_addr(v_k_4886_);
                        v___x_4900_ = lean_ptr_addr(v_____do__lift_4889_);
                        v___x_4901_ = lean_usize_dec_eq(v___x_4899_, v___x_4900_);
                        if v___x_4901_ == 0 {
                            lean_dec_ref(v_c_4887_);
                            v___x_4902_ = lean_alloc_ctor(8, 4, (0) as u32);
                            lean_ctor_set(v___x_4902_, 0, v_____do__lift_4881_);
                            lean_ctor_set(v___x_4902_, 1, v_i_4882_);
                            lean_ctor_set(v___x_4902_, 2, v_____do__lift_4883_);
                            lean_ctor_set(v___x_4902_, 3, v_____do__lift_4889_);
                            v___x_4903_ = lean_apply_2(v_toPure_4884_, lean_box(0), v___x_4902_);
                            return v___x_4903_;
                        } else {
                            lean_dec_ref(v_____do__lift_4889_);
                            lean_dec(v_____do__lift_4883_);
                            lean_dec(v_i_4882_);
                            lean_dec(v_____do__lift_4881_);
                            v___x_4904_ = lean_apply_2(v_toPure_4884_, lean_box(0), v_c_4887_);
                            return v___x_4904_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(
    mut v_____do__lift_4909_: *mut LeanObject,
    mut v_i_4910_: *mut LeanObject,
    mut v_____do__lift_4911_: *mut LeanObject,
    mut v_toPure_4912_: *mut LeanObject,
    mut v_y_4913_: *mut LeanObject,
    mut v_k_4914_: *mut LeanObject,
    mut v_c_4915_: *mut LeanObject,
    mut v_fvarId_4916_: *mut LeanObject,
    mut v_____do__lift_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4918_: *mut LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(
        v_____do__lift_4909_,
        v_i_4910_,
        v_____do__lift_4911_,
        v_toPure_4912_,
        v_y_4913_,
        v_k_4914_,
        v_c_4915_,
        v_fvarId_4916_,
        v_____do__lift_4917_,
    );
    lean_dec(v_fvarId_4916_);
    lean_dec_ref(v_k_4914_);
    lean_dec(v_y_4913_);
    return v_res_4918_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(
    mut v_____do__lift_4919_: *mut LeanObject,
    mut v_toPure_4920_: *mut LeanObject,
    mut v_c_4921_: *mut LeanObject,
    mut v_fvarId_4922_: *mut LeanObject,
    mut v_k_4923_: *mut LeanObject,
    mut v_____do__lift_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4926_: u8 = 0;
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: usize = 0;
    let mut v___x_4932_: u8 = 0;
    let mut v___x_4933_: usize = 0;
    let mut v___x_4934_: usize = 0;
    let mut v___x_4935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4930_ = lean_ptr_addr(v_fvarId_4922_);
                v___x_4931_ = lean_ptr_addr(v_____do__lift_4919_);
                v___x_4932_ = lean_usize_dec_eq(v___x_4930_, v___x_4931_);
                if v___x_4932_ == 0 {
                    v___y_4926_ = v___x_4932_;
                    state = 1;
                    continue;
                } else {
                    v___x_4933_ = lean_ptr_addr(v_k_4923_);
                    v___x_4934_ = lean_ptr_addr(v_____do__lift_4924_);
                    v___x_4935_ = lean_usize_dec_eq(v___x_4933_, v___x_4934_);
                    v___y_4926_ = v___x_4935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4926_ == 0 {
                    lean_dec_ref(v_c_4921_);
                    v___x_4927_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v___x_4927_, 0, v_____do__lift_4919_);
                    lean_ctor_set(v___x_4927_, 1, v_____do__lift_4924_);
                    v___x_4928_ = lean_apply_2(v_toPure_4920_, lean_box(0), v___x_4927_);
                    return v___x_4928_;
                } else {
                    lean_dec_ref(v_____do__lift_4924_);
                    lean_dec(v_____do__lift_4919_);
                    v___x_4929_ = lean_apply_2(v_toPure_4920_, lean_box(0), v_c_4921_);
                    return v___x_4929_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(
    mut v_____do__lift_4936_: *mut LeanObject,
    mut v_toPure_4937_: *mut LeanObject,
    mut v_c_4938_: *mut LeanObject,
    mut v_fvarId_4939_: *mut LeanObject,
    mut v_k_4940_: *mut LeanObject,
    mut v_____do__lift_4941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4942_: *mut LeanObject = core::ptr::null_mut();
    v_res_4942_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(
        v_____do__lift_4936_,
        v_toPure_4937_,
        v_c_4938_,
        v_fvarId_4939_,
        v_k_4940_,
        v_____do__lift_4941_,
    );
    lean_dec_ref(v_k_4940_);
    lean_dec(v_fvarId_4939_);
    return v_res_4942_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(
    mut v_type_4943_: *mut LeanObject,
    mut v_toPure_4944_: *mut LeanObject,
    mut v_c_4945_: *mut LeanObject,
    mut v_____do__lift_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4947_: usize = 0;
    let mut v___x_4948_: usize = 0;
    let mut v___x_4949_: u8 = 0;
    v___x_4947_ = lean_ptr_addr(v_type_4943_);
    v___x_4948_ = lean_ptr_addr(v_____do__lift_4946_);
    v___x_4949_ = lean_usize_dec_eq(v___x_4947_, v___x_4948_);
    if v___x_4949_ == 0 {
        let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_c_4945_);
        v___x_4950_ = lean_alloc_ctor(6, 1, (0) as u32);
        lean_ctor_set(v___x_4950_, 0, v_____do__lift_4946_);
        v___x_4951_ = lean_apply_2(v_toPure_4944_, lean_box(0), v___x_4950_);
        return v___x_4951_;
    } else {
        let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____do__lift_4946_);
        v___x_4952_ = lean_apply_2(v_toPure_4944_, lean_box(0), v_c_4945_);
        return v___x_4952_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(
    mut v_type_4953_: *mut LeanObject,
    mut v_toPure_4954_: *mut LeanObject,
    mut v_c_4955_: *mut LeanObject,
    mut v_____do__lift_4956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4957_: *mut LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(
        v_type_4953_,
        v_toPure_4954_,
        v_c_4955_,
        v_____do__lift_4956_,
    );
    lean_dec_ref(v_type_4953_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(
    mut v_toPure_4958_: *mut LeanObject,
    mut v_c_4959_: *mut LeanObject,
    mut v_k_4960_: *mut LeanObject,
    mut v_decl_4961_: *mut LeanObject,
    mut v_pu_4962_: u8,
    mut v_inst_4963_: *mut LeanObject,
    mut v_inst_4964_: *mut LeanObject,
    mut v_f_4965_: *mut LeanObject,
    mut v_toBind_4966_: *mut LeanObject,
    mut v_decl_4967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_4960_);
    v___f_4968_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4968_, 0, v_decl_4967_);
    lean_closure_set(v___f_4968_, 1, v_toPure_4958_);
    lean_closure_set(v___f_4968_, 2, v_c_4959_);
    lean_closure_set(v___f_4968_, 3, v_k_4960_);
    lean_closure_set(v___f_4968_, 4, v_decl_4961_);
    v___x_4969_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_4962_,
        v_inst_4963_,
        v_inst_4964_,
        v_f_4965_,
        v_k_4960_,
    );
    v___x_4970_ = lean_apply_4(
        v_toBind_4966_,
        lean_box(0),
        lean_box(0),
        v___x_4969_,
        v___f_4968_,
    );
    return v___x_4970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(
    mut v_toPure_4971_: *mut LeanObject,
    mut v_c_4972_: *mut LeanObject,
    mut v_k_4973_: *mut LeanObject,
    mut v_decl_4974_: *mut LeanObject,
    mut v_pu_4975_: *mut LeanObject,
    mut v_inst_4976_: *mut LeanObject,
    mut v_inst_4977_: *mut LeanObject,
    mut v_f_4978_: *mut LeanObject,
    mut v_toBind_4979_: *mut LeanObject,
    mut v_decl_4980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4981_ = (lean_unbox(v_pu_4975_) as u8);
    v_res_4982_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(
        v_toPure_4971_,
        v_c_4972_,
        v_k_4973_,
        v_decl_4974_,
        v_pu_boxed_4981_,
        v_inst_4976_,
        v_inst_4977_,
        v_f_4978_,
        v_toBind_4979_,
        v_decl_4980_,
    );
    return v_res_4982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(
    mut v_toPure_4983_: *mut LeanObject,
    mut v_c_4984_: *mut LeanObject,
    mut v_k_4985_: *mut LeanObject,
    mut v_decl_4986_: *mut LeanObject,
    mut v_pu_4987_: u8,
    mut v_inst_4988_: *mut LeanObject,
    mut v_inst_4989_: *mut LeanObject,
    mut v_f_4990_: *mut LeanObject,
    mut v_toBind_4991_: *mut LeanObject,
    mut v_decl_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_4985_);
    v___f_4993_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4993_, 0, v_decl_4992_);
    lean_closure_set(v___f_4993_, 1, v_toPure_4983_);
    lean_closure_set(v___f_4993_, 2, v_c_4984_);
    lean_closure_set(v___f_4993_, 3, v_k_4985_);
    lean_closure_set(v___f_4993_, 4, v_decl_4986_);
    v___x_4994_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_4987_,
        v_inst_4988_,
        v_inst_4989_,
        v_f_4990_,
        v_k_4985_,
    );
    v___x_4995_ = lean_apply_4(
        v_toBind_4991_,
        lean_box(0),
        lean_box(0),
        v___x_4994_,
        v___f_4993_,
    );
    return v___x_4995_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(
    mut v_toPure_4996_: *mut LeanObject,
    mut v_c_4997_: *mut LeanObject,
    mut v_k_4998_: *mut LeanObject,
    mut v_decl_4999_: *mut LeanObject,
    mut v_pu_5000_: *mut LeanObject,
    mut v_inst_5001_: *mut LeanObject,
    mut v_inst_5002_: *mut LeanObject,
    mut v_f_5003_: *mut LeanObject,
    mut v_toBind_5004_: *mut LeanObject,
    mut v_decl_5005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5006_: u8 = 0;
    let mut v_res_5007_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5006_ = (lean_unbox(v_pu_5000_) as u8);
    v_res_5007_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(
        v_toPure_4996_,
        v_c_4997_,
        v_k_4998_,
        v_decl_4999_,
        v_pu_boxed_5006_,
        v_inst_5001_,
        v_inst_5002_,
        v_f_5003_,
        v_toBind_5004_,
        v_decl_5005_,
    );
    return v_res_5007_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(
    mut v_pu_5008_: u8,
    mut v_decl_5009_: *mut LeanObject,
    mut v_params_5010_: *mut LeanObject,
    mut v_inst_5011_: *mut LeanObject,
    mut v_toBind_5012_: *mut LeanObject,
    mut v___f_5013_: *mut LeanObject,
    mut v_inst_5014_: *mut LeanObject,
    mut v_f_5015_: *mut LeanObject,
    mut v_value_5016_: *mut LeanObject,
    mut v_____do__lift_5017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    v___x_5018_ = lean_box((v_pu_5008_) as usize);
    lean_inc(v_toBind_5012_);
    lean_inc(v_inst_5011_);
    v___f_5019_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_5019_, 0, v___x_5018_);
    lean_closure_set(v___f_5019_, 1, v_decl_5009_);
    lean_closure_set(v___f_5019_, 2, v_____do__lift_5017_);
    lean_closure_set(v___f_5019_, 3, v_params_5010_);
    lean_closure_set(v___f_5019_, 4, v_inst_5011_);
    lean_closure_set(v___f_5019_, 5, v_toBind_5012_);
    lean_closure_set(v___f_5019_, 6, v___f_5013_);
    v___x_5020_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5008_,
        v_inst_5011_,
        v_inst_5014_,
        v_f_5015_,
        v_value_5016_,
    );
    v___x_5021_ = lean_apply_4(
        v_toBind_5012_,
        lean_box(0),
        lean_box(0),
        v___x_5020_,
        v___f_5019_,
    );
    return v___x_5021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(
    mut v_pu_5022_: *mut LeanObject,
    mut v_decl_5023_: *mut LeanObject,
    mut v_params_5024_: *mut LeanObject,
    mut v_inst_5025_: *mut LeanObject,
    mut v_toBind_5026_: *mut LeanObject,
    mut v___f_5027_: *mut LeanObject,
    mut v_inst_5028_: *mut LeanObject,
    mut v_f_5029_: *mut LeanObject,
    mut v_value_5030_: *mut LeanObject,
    mut v_____do__lift_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5032_: u8 = 0;
    let mut v_res_5033_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5032_ = (lean_unbox(v_pu_5022_) as u8);
    v_res_5033_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(
        v_pu_boxed_5032_,
        v_decl_5023_,
        v_params_5024_,
        v_inst_5025_,
        v_toBind_5026_,
        v___f_5027_,
        v_inst_5028_,
        v_f_5029_,
        v_value_5030_,
        v_____do__lift_5031_,
    );
    return v_res_5033_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(
    mut v_pu_5034_: u8,
    mut v_decl_5035_: *mut LeanObject,
    mut v_inst_5036_: *mut LeanObject,
    mut v_toBind_5037_: *mut LeanObject,
    mut v___f_5038_: *mut LeanObject,
    mut v_inst_5039_: *mut LeanObject,
    mut v_f_5040_: *mut LeanObject,
    mut v_value_5041_: *mut LeanObject,
    mut v_type_5042_: *mut LeanObject,
    mut v_params_5043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    v___x_5044_ = lean_box((v_pu_5034_) as usize);
    lean_inc(v_f_5040_);
    lean_inc_ref(v_inst_5039_);
    lean_inc(v_toBind_5037_);
    v___f_5045_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_5045_, 0, v___x_5044_);
    lean_closure_set(v___f_5045_, 1, v_decl_5035_);
    lean_closure_set(v___f_5045_, 2, v_params_5043_);
    lean_closure_set(v___f_5045_, 3, v_inst_5036_);
    lean_closure_set(v___f_5045_, 4, v_toBind_5037_);
    lean_closure_set(v___f_5045_, 5, v___f_5038_);
    lean_closure_set(v___f_5045_, 6, v_inst_5039_);
    lean_closure_set(v___f_5045_, 7, v_f_5040_);
    lean_closure_set(v___f_5045_, 8, v_value_5041_);
    v___x_5046_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5039_, v_f_5040_, v_type_5042_);
    v___x_5047_ = lean_apply_4(
        v_toBind_5037_,
        lean_box(0),
        lean_box(0),
        v___x_5046_,
        v___f_5045_,
    );
    return v___x_5047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(
    mut v_pu_5048_: *mut LeanObject,
    mut v_decl_5049_: *mut LeanObject,
    mut v_inst_5050_: *mut LeanObject,
    mut v_toBind_5051_: *mut LeanObject,
    mut v___f_5052_: *mut LeanObject,
    mut v_inst_5053_: *mut LeanObject,
    mut v_f_5054_: *mut LeanObject,
    mut v_value_5055_: *mut LeanObject,
    mut v_type_5056_: *mut LeanObject,
    mut v_params_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5058_ = (lean_unbox(v_pu_5048_) as u8);
    v_res_5059_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(
        v_pu_boxed_5058_,
        v_decl_5049_,
        v_inst_5050_,
        v_toBind_5051_,
        v___f_5052_,
        v_inst_5053_,
        v_f_5054_,
        v_value_5055_,
        v_type_5056_,
        v_params_5057_,
    );
    return v_res_5059_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(
    mut v_toPure_5060_: *mut LeanObject,
    mut v_c_5061_: *mut LeanObject,
    mut v_k_5062_: *mut LeanObject,
    mut v_decl_5063_: *mut LeanObject,
    mut v_pu_5064_: u8,
    mut v_inst_5065_: *mut LeanObject,
    mut v_inst_5066_: *mut LeanObject,
    mut v_f_5067_: *mut LeanObject,
    mut v_toBind_5068_: *mut LeanObject,
    mut v_decl_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5062_);
    v___f_5070_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5070_, 0, v_decl_5069_);
    lean_closure_set(v___f_5070_, 1, v_toPure_5060_);
    lean_closure_set(v___f_5070_, 2, v_c_5061_);
    lean_closure_set(v___f_5070_, 3, v_k_5062_);
    lean_closure_set(v___f_5070_, 4, v_decl_5063_);
    v___x_5071_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5064_,
        v_inst_5065_,
        v_inst_5066_,
        v_f_5067_,
        v_k_5062_,
    );
    v___x_5072_ = lean_apply_4(
        v_toBind_5068_,
        lean_box(0),
        lean_box(0),
        v___x_5071_,
        v___f_5070_,
    );
    return v___x_5072_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(
    mut v_toPure_5073_: *mut LeanObject,
    mut v_c_5074_: *mut LeanObject,
    mut v_k_5075_: *mut LeanObject,
    mut v_decl_5076_: *mut LeanObject,
    mut v_pu_5077_: *mut LeanObject,
    mut v_inst_5078_: *mut LeanObject,
    mut v_inst_5079_: *mut LeanObject,
    mut v_f_5080_: *mut LeanObject,
    mut v_toBind_5081_: *mut LeanObject,
    mut v_decl_5082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5083_: u8 = 0;
    let mut v_res_5084_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5083_ = (lean_unbox(v_pu_5077_) as u8);
    v_res_5084_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(
        v_toPure_5073_,
        v_c_5074_,
        v_k_5075_,
        v_decl_5076_,
        v_pu_boxed_5083_,
        v_inst_5078_,
        v_inst_5079_,
        v_f_5080_,
        v_toBind_5081_,
        v_decl_5082_,
    );
    return v_res_5084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(
    mut v_pu_5085_: *mut LeanObject,
    mut v_inst_5086_: *mut LeanObject,
    mut v_inst_5087_: *mut LeanObject,
    mut v_f_5088_: *mut LeanObject,
    mut v_x_5089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5090_: u8 = 0;
    let mut v_res_5091_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5090_ = (lean_unbox(v_pu_5085_) as u8);
    v_res_5091_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(
        v_pu_boxed_5090_,
        v_inst_5086_,
        v_inst_5087_,
        v_f_5088_,
        v_x_5089_,
    );
    return v_res_5091_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(
    mut v_____do__lift_5092_: *mut LeanObject,
    mut v_i_5093_: *mut LeanObject,
    mut v_toPure_5094_: *mut LeanObject,
    mut v_y_5095_: *mut LeanObject,
    mut v_k_5096_: *mut LeanObject,
    mut v_c_5097_: *mut LeanObject,
    mut v_fvarId_5098_: *mut LeanObject,
    mut v_pu_5099_: u8,
    mut v_inst_5100_: *mut LeanObject,
    mut v_inst_5101_: *mut LeanObject,
    mut v_f_5102_: *mut LeanObject,
    mut v_toBind_5103_: *mut LeanObject,
    mut v_____do__lift_5104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5096_);
    v___f_5105_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5105_, 0, v_____do__lift_5092_);
    lean_closure_set(v___f_5105_, 1, v_i_5093_);
    lean_closure_set(v___f_5105_, 2, v_____do__lift_5104_);
    lean_closure_set(v___f_5105_, 3, v_toPure_5094_);
    lean_closure_set(v___f_5105_, 4, v_y_5095_);
    lean_closure_set(v___f_5105_, 5, v_k_5096_);
    lean_closure_set(v___f_5105_, 6, v_c_5097_);
    lean_closure_set(v___f_5105_, 7, v_fvarId_5098_);
    v___x_5106_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5099_,
        v_inst_5100_,
        v_inst_5101_,
        v_f_5102_,
        v_k_5096_,
    );
    v___x_5107_ = lean_apply_4(
        v_toBind_5103_,
        lean_box(0),
        lean_box(0),
        v___x_5106_,
        v___f_5105_,
    );
    return v___x_5107_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(
    mut v_____do__lift_5108_: *mut LeanObject,
    mut v_i_5109_: *mut LeanObject,
    mut v_toPure_5110_: *mut LeanObject,
    mut v_y_5111_: *mut LeanObject,
    mut v_k_5112_: *mut LeanObject,
    mut v_c_5113_: *mut LeanObject,
    mut v_fvarId_5114_: *mut LeanObject,
    mut v_pu_5115_: *mut LeanObject,
    mut v_inst_5116_: *mut LeanObject,
    mut v_inst_5117_: *mut LeanObject,
    mut v_f_5118_: *mut LeanObject,
    mut v_toBind_5119_: *mut LeanObject,
    mut v_____do__lift_5120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5121_: u8 = 0;
    let mut v_res_5122_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5121_ = (lean_unbox(v_pu_5115_) as u8);
    v_res_5122_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(
        v_____do__lift_5108_,
        v_i_5109_,
        v_toPure_5110_,
        v_y_5111_,
        v_k_5112_,
        v_c_5113_,
        v_fvarId_5114_,
        v_pu_boxed_5121_,
        v_inst_5116_,
        v_inst_5117_,
        v_f_5118_,
        v_toBind_5119_,
        v_____do__lift_5120_,
    );
    return v_res_5122_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(
    mut v_i_5123_: *mut LeanObject,
    mut v_toPure_5124_: *mut LeanObject,
    mut v_y_5125_: *mut LeanObject,
    mut v_k_5126_: *mut LeanObject,
    mut v_c_5127_: *mut LeanObject,
    mut v_fvarId_5128_: *mut LeanObject,
    mut v_pu_5129_: u8,
    mut v_inst_5130_: *mut LeanObject,
    mut v_inst_5131_: *mut LeanObject,
    mut v_f_5132_: *mut LeanObject,
    mut v_toBind_5133_: *mut LeanObject,
    mut v_____do__lift_5134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    v___x_5135_ = lean_box((v_pu_5129_) as usize);
    lean_inc(v_toBind_5133_);
    lean_inc(v_f_5132_);
    lean_inc_ref(v_inst_5131_);
    lean_inc(v_y_5125_);
    v___f_5136_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_5136_, 0, v_____do__lift_5134_);
    lean_closure_set(v___f_5136_, 1, v_i_5123_);
    lean_closure_set(v___f_5136_, 2, v_toPure_5124_);
    lean_closure_set(v___f_5136_, 3, v_y_5125_);
    lean_closure_set(v___f_5136_, 4, v_k_5126_);
    lean_closure_set(v___f_5136_, 5, v_c_5127_);
    lean_closure_set(v___f_5136_, 6, v_fvarId_5128_);
    lean_closure_set(v___f_5136_, 7, v___x_5135_);
    lean_closure_set(v___f_5136_, 8, v_inst_5130_);
    lean_closure_set(v___f_5136_, 9, v_inst_5131_);
    lean_closure_set(v___f_5136_, 10, v_f_5132_);
    lean_closure_set(v___f_5136_, 11, v_toBind_5133_);
    v___x_5137_ =
        l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_5129_, v_inst_5131_, v_f_5132_, v_y_5125_);
    v___x_5138_ = lean_apply_4(
        v_toBind_5133_,
        lean_box(0),
        lean_box(0),
        v___x_5137_,
        v___f_5136_,
    );
    return v___x_5138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(
    mut v_i_5139_: *mut LeanObject,
    mut v_toPure_5140_: *mut LeanObject,
    mut v_y_5141_: *mut LeanObject,
    mut v_k_5142_: *mut LeanObject,
    mut v_c_5143_: *mut LeanObject,
    mut v_fvarId_5144_: *mut LeanObject,
    mut v_pu_5145_: *mut LeanObject,
    mut v_inst_5146_: *mut LeanObject,
    mut v_inst_5147_: *mut LeanObject,
    mut v_f_5148_: *mut LeanObject,
    mut v_toBind_5149_: *mut LeanObject,
    mut v_____do__lift_5150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5151_: u8 = 0;
    let mut v_res_5152_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5151_ = (lean_unbox(v_pu_5145_) as u8);
    v_res_5152_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(
        v_i_5139_,
        v_toPure_5140_,
        v_y_5141_,
        v_k_5142_,
        v_c_5143_,
        v_fvarId_5144_,
        v_pu_boxed_5151_,
        v_inst_5146_,
        v_inst_5147_,
        v_f_5148_,
        v_toBind_5149_,
        v_____do__lift_5150_,
    );
    return v_res_5152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(
    mut v_____do__lift_5153_: *mut LeanObject,
    mut v_i_5154_: *mut LeanObject,
    mut v_toPure_5155_: *mut LeanObject,
    mut v_y_5156_: *mut LeanObject,
    mut v_k_5157_: *mut LeanObject,
    mut v_c_5158_: *mut LeanObject,
    mut v_fvarId_5159_: *mut LeanObject,
    mut v_pu_5160_: u8,
    mut v_inst_5161_: *mut LeanObject,
    mut v_inst_5162_: *mut LeanObject,
    mut v_f_5163_: *mut LeanObject,
    mut v_toBind_5164_: *mut LeanObject,
    mut v_____do__lift_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5157_);
    v___f_5166_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5166_, 0, v_____do__lift_5153_);
    lean_closure_set(v___f_5166_, 1, v_i_5154_);
    lean_closure_set(v___f_5166_, 2, v_____do__lift_5165_);
    lean_closure_set(v___f_5166_, 3, v_toPure_5155_);
    lean_closure_set(v___f_5166_, 4, v_y_5156_);
    lean_closure_set(v___f_5166_, 5, v_k_5157_);
    lean_closure_set(v___f_5166_, 6, v_c_5158_);
    lean_closure_set(v___f_5166_, 7, v_fvarId_5159_);
    v___x_5167_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5160_,
        v_inst_5161_,
        v_inst_5162_,
        v_f_5163_,
        v_k_5157_,
    );
    v___x_5168_ = lean_apply_4(
        v_toBind_5164_,
        lean_box(0),
        lean_box(0),
        v___x_5167_,
        v___f_5166_,
    );
    return v___x_5168_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(
    mut v_____do__lift_5169_: *mut LeanObject,
    mut v_i_5170_: *mut LeanObject,
    mut v_toPure_5171_: *mut LeanObject,
    mut v_y_5172_: *mut LeanObject,
    mut v_k_5173_: *mut LeanObject,
    mut v_c_5174_: *mut LeanObject,
    mut v_fvarId_5175_: *mut LeanObject,
    mut v_pu_5176_: *mut LeanObject,
    mut v_inst_5177_: *mut LeanObject,
    mut v_inst_5178_: *mut LeanObject,
    mut v_f_5179_: *mut LeanObject,
    mut v_toBind_5180_: *mut LeanObject,
    mut v_____do__lift_5181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5182_: u8 = 0;
    let mut v_res_5183_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5182_ = (lean_unbox(v_pu_5176_) as u8);
    v_res_5183_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(
        v_____do__lift_5169_,
        v_i_5170_,
        v_toPure_5171_,
        v_y_5172_,
        v_k_5173_,
        v_c_5174_,
        v_fvarId_5175_,
        v_pu_boxed_5182_,
        v_inst_5177_,
        v_inst_5178_,
        v_f_5179_,
        v_toBind_5180_,
        v_____do__lift_5181_,
    );
    return v_res_5183_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(
    mut v_i_5184_: *mut LeanObject,
    mut v_toPure_5185_: *mut LeanObject,
    mut v_y_5186_: *mut LeanObject,
    mut v_k_5187_: *mut LeanObject,
    mut v_c_5188_: *mut LeanObject,
    mut v_fvarId_5189_: *mut LeanObject,
    mut v_pu_5190_: u8,
    mut v_inst_5191_: *mut LeanObject,
    mut v_inst_5192_: *mut LeanObject,
    mut v_f_5193_: *mut LeanObject,
    mut v_toBind_5194_: *mut LeanObject,
    mut v_____do__lift_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    v___x_5196_ = lean_box((v_pu_5190_) as usize);
    lean_inc(v_toBind_5194_);
    lean_inc(v_f_5193_);
    lean_inc(v_y_5186_);
    v___f_5197_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_5197_, 0, v_____do__lift_5195_);
    lean_closure_set(v___f_5197_, 1, v_i_5184_);
    lean_closure_set(v___f_5197_, 2, v_toPure_5185_);
    lean_closure_set(v___f_5197_, 3, v_y_5186_);
    lean_closure_set(v___f_5197_, 4, v_k_5187_);
    lean_closure_set(v___f_5197_, 5, v_c_5188_);
    lean_closure_set(v___f_5197_, 6, v_fvarId_5189_);
    lean_closure_set(v___f_5197_, 7, v___x_5196_);
    lean_closure_set(v___f_5197_, 8, v_inst_5191_);
    lean_closure_set(v___f_5197_, 9, v_inst_5192_);
    lean_closure_set(v___f_5197_, 10, v_f_5193_);
    lean_closure_set(v___f_5197_, 11, v_toBind_5194_);
    v___x_5198_ = lean_apply_1(v_f_5193_, v_y_5186_);
    v___x_5199_ = lean_apply_4(
        v_toBind_5194_,
        lean_box(0),
        lean_box(0),
        v___x_5198_,
        v___f_5197_,
    );
    return v___x_5199_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(
    mut v_i_5200_: *mut LeanObject,
    mut v_toPure_5201_: *mut LeanObject,
    mut v_y_5202_: *mut LeanObject,
    mut v_k_5203_: *mut LeanObject,
    mut v_c_5204_: *mut LeanObject,
    mut v_fvarId_5205_: *mut LeanObject,
    mut v_pu_5206_: *mut LeanObject,
    mut v_inst_5207_: *mut LeanObject,
    mut v_inst_5208_: *mut LeanObject,
    mut v_f_5209_: *mut LeanObject,
    mut v_toBind_5210_: *mut LeanObject,
    mut v_____do__lift_5211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5212_: u8 = 0;
    let mut v_res_5213_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5212_ = (lean_unbox(v_pu_5206_) as u8);
    v_res_5213_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(
        v_i_5200_,
        v_toPure_5201_,
        v_y_5202_,
        v_k_5203_,
        v_c_5204_,
        v_fvarId_5205_,
        v_pu_boxed_5212_,
        v_inst_5207_,
        v_inst_5208_,
        v_f_5209_,
        v_toBind_5210_,
        v_____do__lift_5211_,
    );
    return v_res_5213_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(
    mut v_____do__lift_5214_: *mut LeanObject,
    mut v_i_5215_: *mut LeanObject,
    mut v_offset_5216_: *mut LeanObject,
    mut v_____do__lift_5217_: *mut LeanObject,
    mut v_toPure_5218_: *mut LeanObject,
    mut v_y_5219_: *mut LeanObject,
    mut v_ty_5220_: *mut LeanObject,
    mut v_k_5221_: *mut LeanObject,
    mut v_c_5222_: *mut LeanObject,
    mut v_fvarId_5223_: *mut LeanObject,
    mut v_pu_5224_: u8,
    mut v_inst_5225_: *mut LeanObject,
    mut v_inst_5226_: *mut LeanObject,
    mut v_f_5227_: *mut LeanObject,
    mut v_toBind_5228_: *mut LeanObject,
    mut v_____do__lift_5229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5221_);
    v___f_5230_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_5230_, 0, v_____do__lift_5214_);
    lean_closure_set(v___f_5230_, 1, v_i_5215_);
    lean_closure_set(v___f_5230_, 2, v_offset_5216_);
    lean_closure_set(v___f_5230_, 3, v_____do__lift_5217_);
    lean_closure_set(v___f_5230_, 4, v_____do__lift_5229_);
    lean_closure_set(v___f_5230_, 5, v_toPure_5218_);
    lean_closure_set(v___f_5230_, 6, v_y_5219_);
    lean_closure_set(v___f_5230_, 7, v_ty_5220_);
    lean_closure_set(v___f_5230_, 8, v_k_5221_);
    lean_closure_set(v___f_5230_, 9, v_c_5222_);
    lean_closure_set(v___f_5230_, 10, v_fvarId_5223_);
    v___x_5231_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5224_,
        v_inst_5225_,
        v_inst_5226_,
        v_f_5227_,
        v_k_5221_,
    );
    v___x_5232_ = lean_apply_4(
        v_toBind_5228_,
        lean_box(0),
        lean_box(0),
        v___x_5231_,
        v___f_5230_,
    );
    return v___x_5232_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(
    mut v_____do__lift_5233_: *mut LeanObject,
    mut v_i_5234_: *mut LeanObject,
    mut v_offset_5235_: *mut LeanObject,
    mut v_____do__lift_5236_: *mut LeanObject,
    mut v_toPure_5237_: *mut LeanObject,
    mut v_y_5238_: *mut LeanObject,
    mut v_ty_5239_: *mut LeanObject,
    mut v_k_5240_: *mut LeanObject,
    mut v_c_5241_: *mut LeanObject,
    mut v_fvarId_5242_: *mut LeanObject,
    mut v_pu_5243_: *mut LeanObject,
    mut v_inst_5244_: *mut LeanObject,
    mut v_inst_5245_: *mut LeanObject,
    mut v_f_5246_: *mut LeanObject,
    mut v_toBind_5247_: *mut LeanObject,
    mut v_____do__lift_5248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5249_: u8 = 0;
    let mut v_res_5250_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5249_ = (lean_unbox(v_pu_5243_) as u8);
    v_res_5250_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(
        v_____do__lift_5233_,
        v_i_5234_,
        v_offset_5235_,
        v_____do__lift_5236_,
        v_toPure_5237_,
        v_y_5238_,
        v_ty_5239_,
        v_k_5240_,
        v_c_5241_,
        v_fvarId_5242_,
        v_pu_boxed_5249_,
        v_inst_5244_,
        v_inst_5245_,
        v_f_5246_,
        v_toBind_5247_,
        v_____do__lift_5248_,
    );
    return v_res_5250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(
    mut v_____do__lift_5251_: *mut LeanObject,
    mut v_i_5252_: *mut LeanObject,
    mut v_offset_5253_: *mut LeanObject,
    mut v_toPure_5254_: *mut LeanObject,
    mut v_y_5255_: *mut LeanObject,
    mut v_ty_5256_: *mut LeanObject,
    mut v_k_5257_: *mut LeanObject,
    mut v_c_5258_: *mut LeanObject,
    mut v_fvarId_5259_: *mut LeanObject,
    mut v_pu_5260_: u8,
    mut v_inst_5261_: *mut LeanObject,
    mut v_inst_5262_: *mut LeanObject,
    mut v_f_5263_: *mut LeanObject,
    mut v_toBind_5264_: *mut LeanObject,
    mut v_____do__lift_5265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    v___x_5266_ = lean_box((v_pu_5260_) as usize);
    lean_inc(v_toBind_5264_);
    lean_inc(v_f_5263_);
    lean_inc_ref(v_inst_5262_);
    lean_inc_ref(v_ty_5256_);
    v___f_5267_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_5267_, 0, v_____do__lift_5251_);
    lean_closure_set(v___f_5267_, 1, v_i_5252_);
    lean_closure_set(v___f_5267_, 2, v_offset_5253_);
    lean_closure_set(v___f_5267_, 3, v_____do__lift_5265_);
    lean_closure_set(v___f_5267_, 4, v_toPure_5254_);
    lean_closure_set(v___f_5267_, 5, v_y_5255_);
    lean_closure_set(v___f_5267_, 6, v_ty_5256_);
    lean_closure_set(v___f_5267_, 7, v_k_5257_);
    lean_closure_set(v___f_5267_, 8, v_c_5258_);
    lean_closure_set(v___f_5267_, 9, v_fvarId_5259_);
    lean_closure_set(v___f_5267_, 10, v___x_5266_);
    lean_closure_set(v___f_5267_, 11, v_inst_5261_);
    lean_closure_set(v___f_5267_, 12, v_inst_5262_);
    lean_closure_set(v___f_5267_, 13, v_f_5263_);
    lean_closure_set(v___f_5267_, 14, v_toBind_5264_);
    v___x_5268_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5262_, v_f_5263_, v_ty_5256_);
    v___x_5269_ = lean_apply_4(
        v_toBind_5264_,
        lean_box(0),
        lean_box(0),
        v___x_5268_,
        v___f_5267_,
    );
    return v___x_5269_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(
    mut v_____do__lift_5270_: *mut LeanObject,
    mut v_i_5271_: *mut LeanObject,
    mut v_offset_5272_: *mut LeanObject,
    mut v_toPure_5273_: *mut LeanObject,
    mut v_y_5274_: *mut LeanObject,
    mut v_ty_5275_: *mut LeanObject,
    mut v_k_5276_: *mut LeanObject,
    mut v_c_5277_: *mut LeanObject,
    mut v_fvarId_5278_: *mut LeanObject,
    mut v_pu_5279_: *mut LeanObject,
    mut v_inst_5280_: *mut LeanObject,
    mut v_inst_5281_: *mut LeanObject,
    mut v_f_5282_: *mut LeanObject,
    mut v_toBind_5283_: *mut LeanObject,
    mut v_____do__lift_5284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5285_: u8 = 0;
    let mut v_res_5286_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5285_ = (lean_unbox(v_pu_5279_) as u8);
    v_res_5286_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(
        v_____do__lift_5270_,
        v_i_5271_,
        v_offset_5272_,
        v_toPure_5273_,
        v_y_5274_,
        v_ty_5275_,
        v_k_5276_,
        v_c_5277_,
        v_fvarId_5278_,
        v_pu_boxed_5285_,
        v_inst_5280_,
        v_inst_5281_,
        v_f_5282_,
        v_toBind_5283_,
        v_____do__lift_5284_,
    );
    return v_res_5286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(
    mut v_i_5287_: *mut LeanObject,
    mut v_offset_5288_: *mut LeanObject,
    mut v_toPure_5289_: *mut LeanObject,
    mut v_y_5290_: *mut LeanObject,
    mut v_ty_5291_: *mut LeanObject,
    mut v_k_5292_: *mut LeanObject,
    mut v_c_5293_: *mut LeanObject,
    mut v_fvarId_5294_: *mut LeanObject,
    mut v_pu_5295_: u8,
    mut v_inst_5296_: *mut LeanObject,
    mut v_inst_5297_: *mut LeanObject,
    mut v_f_5298_: *mut LeanObject,
    mut v_toBind_5299_: *mut LeanObject,
    mut v_____do__lift_5300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    v___x_5301_ = lean_box((v_pu_5295_) as usize);
    lean_inc(v_toBind_5299_);
    lean_inc(v_f_5298_);
    lean_inc(v_y_5290_);
    v___f_5302_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    lean_closure_set(v___f_5302_, 0, v_____do__lift_5300_);
    lean_closure_set(v___f_5302_, 1, v_i_5287_);
    lean_closure_set(v___f_5302_, 2, v_offset_5288_);
    lean_closure_set(v___f_5302_, 3, v_toPure_5289_);
    lean_closure_set(v___f_5302_, 4, v_y_5290_);
    lean_closure_set(v___f_5302_, 5, v_ty_5291_);
    lean_closure_set(v___f_5302_, 6, v_k_5292_);
    lean_closure_set(v___f_5302_, 7, v_c_5293_);
    lean_closure_set(v___f_5302_, 8, v_fvarId_5294_);
    lean_closure_set(v___f_5302_, 9, v___x_5301_);
    lean_closure_set(v___f_5302_, 10, v_inst_5296_);
    lean_closure_set(v___f_5302_, 11, v_inst_5297_);
    lean_closure_set(v___f_5302_, 12, v_f_5298_);
    lean_closure_set(v___f_5302_, 13, v_toBind_5299_);
    v___x_5303_ = lean_apply_1(v_f_5298_, v_y_5290_);
    v___x_5304_ = lean_apply_4(
        v_toBind_5299_,
        lean_box(0),
        lean_box(0),
        v___x_5303_,
        v___f_5302_,
    );
    return v___x_5304_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(
    mut v_i_5305_: *mut LeanObject,
    mut v_offset_5306_: *mut LeanObject,
    mut v_toPure_5307_: *mut LeanObject,
    mut v_y_5308_: *mut LeanObject,
    mut v_ty_5309_: *mut LeanObject,
    mut v_k_5310_: *mut LeanObject,
    mut v_c_5311_: *mut LeanObject,
    mut v_fvarId_5312_: *mut LeanObject,
    mut v_pu_5313_: *mut LeanObject,
    mut v_inst_5314_: *mut LeanObject,
    mut v_inst_5315_: *mut LeanObject,
    mut v_f_5316_: *mut LeanObject,
    mut v_toBind_5317_: *mut LeanObject,
    mut v_____do__lift_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5319_: u8 = 0;
    let mut v_res_5320_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5319_ = (lean_unbox(v_pu_5313_) as u8);
    v_res_5320_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(
        v_i_5305_,
        v_offset_5306_,
        v_toPure_5307_,
        v_y_5308_,
        v_ty_5309_,
        v_k_5310_,
        v_c_5311_,
        v_fvarId_5312_,
        v_pu_boxed_5319_,
        v_inst_5314_,
        v_inst_5315_,
        v_f_5316_,
        v_toBind_5317_,
        v_____do__lift_5318_,
    );
    return v_res_5320_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(
    mut v_cidx_5321_: *mut LeanObject,
    mut v_toPure_5322_: *mut LeanObject,
    mut v_k_5323_: *mut LeanObject,
    mut v_c_5324_: *mut LeanObject,
    mut v_fvarId_5325_: *mut LeanObject,
    mut v_pu_5326_: u8,
    mut v_inst_5327_: *mut LeanObject,
    mut v_inst_5328_: *mut LeanObject,
    mut v_f_5329_: *mut LeanObject,
    mut v_toBind_5330_: *mut LeanObject,
    mut v_____do__lift_5331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5323_);
    v___f_5332_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_5332_, 0, v_____do__lift_5331_);
    lean_closure_set(v___f_5332_, 1, v_cidx_5321_);
    lean_closure_set(v___f_5332_, 2, v_toPure_5322_);
    lean_closure_set(v___f_5332_, 3, v_k_5323_);
    lean_closure_set(v___f_5332_, 4, v_c_5324_);
    lean_closure_set(v___f_5332_, 5, v_fvarId_5325_);
    v___x_5333_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5326_,
        v_inst_5327_,
        v_inst_5328_,
        v_f_5329_,
        v_k_5323_,
    );
    v___x_5334_ = lean_apply_4(
        v_toBind_5330_,
        lean_box(0),
        lean_box(0),
        v___x_5333_,
        v___f_5332_,
    );
    return v___x_5334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(
    mut v_cidx_5335_: *mut LeanObject,
    mut v_toPure_5336_: *mut LeanObject,
    mut v_k_5337_: *mut LeanObject,
    mut v_c_5338_: *mut LeanObject,
    mut v_fvarId_5339_: *mut LeanObject,
    mut v_pu_5340_: *mut LeanObject,
    mut v_inst_5341_: *mut LeanObject,
    mut v_inst_5342_: *mut LeanObject,
    mut v_f_5343_: *mut LeanObject,
    mut v_toBind_5344_: *mut LeanObject,
    mut v_____do__lift_5345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5346_: u8 = 0;
    let mut v_res_5347_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5346_ = (lean_unbox(v_pu_5340_) as u8);
    v_res_5347_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(
        v_cidx_5335_,
        v_toPure_5336_,
        v_k_5337_,
        v_c_5338_,
        v_fvarId_5339_,
        v_pu_boxed_5346_,
        v_inst_5341_,
        v_inst_5342_,
        v_f_5343_,
        v_toBind_5344_,
        v_____do__lift_5345_,
    );
    return v_res_5347_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(
    mut v_n_5348_: *mut LeanObject,
    mut v_check_5349_: u8,
    mut v_persistent_5350_: u8,
    mut v_toPure_5351_: *mut LeanObject,
    mut v_k_5352_: *mut LeanObject,
    mut v_c_5353_: *mut LeanObject,
    mut v_fvarId_5354_: *mut LeanObject,
    mut v_pu_5355_: u8,
    mut v_inst_5356_: *mut LeanObject,
    mut v_inst_5357_: *mut LeanObject,
    mut v_f_5358_: *mut LeanObject,
    mut v_toBind_5359_: *mut LeanObject,
    mut v_____do__lift_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    v___x_5361_ = lean_box((v_check_5349_) as usize);
    v___x_5362_ = lean_box((v_persistent_5350_) as usize);
    lean_inc_ref(v_k_5352_);
    v___f_5363_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5363_, 0, v_____do__lift_5360_);
    lean_closure_set(v___f_5363_, 1, v_n_5348_);
    lean_closure_set(v___f_5363_, 2, v___x_5361_);
    lean_closure_set(v___f_5363_, 3, v___x_5362_);
    lean_closure_set(v___f_5363_, 4, v_toPure_5351_);
    lean_closure_set(v___f_5363_, 5, v_k_5352_);
    lean_closure_set(v___f_5363_, 6, v_c_5353_);
    lean_closure_set(v___f_5363_, 7, v_fvarId_5354_);
    v___x_5364_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5355_,
        v_inst_5356_,
        v_inst_5357_,
        v_f_5358_,
        v_k_5352_,
    );
    v___x_5365_ = lean_apply_4(
        v_toBind_5359_,
        lean_box(0),
        lean_box(0),
        v___x_5364_,
        v___f_5363_,
    );
    return v___x_5365_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(
    mut v_n_5366_: *mut LeanObject,
    mut v_check_5367_: *mut LeanObject,
    mut v_persistent_5368_: *mut LeanObject,
    mut v_toPure_5369_: *mut LeanObject,
    mut v_k_5370_: *mut LeanObject,
    mut v_c_5371_: *mut LeanObject,
    mut v_fvarId_5372_: *mut LeanObject,
    mut v_pu_5373_: *mut LeanObject,
    mut v_inst_5374_: *mut LeanObject,
    mut v_inst_5375_: *mut LeanObject,
    mut v_f_5376_: *mut LeanObject,
    mut v_toBind_5377_: *mut LeanObject,
    mut v_____do__lift_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_2471__boxed_5379_: u8 = 0;
    let mut v_persistent_2472__boxed_5380_: u8 = 0;
    let mut v_pu_boxed_5381_: u8 = 0;
    let mut v_res_5382_: *mut LeanObject = core::ptr::null_mut();
    v_check_2471__boxed_5379_ = (lean_unbox(v_check_5367_) as u8);
    v_persistent_2472__boxed_5380_ = (lean_unbox(v_persistent_5368_) as u8);
    v_pu_boxed_5381_ = (lean_unbox(v_pu_5373_) as u8);
    v_res_5382_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(
        v_n_5366_,
        v_check_2471__boxed_5379_,
        v_persistent_2472__boxed_5380_,
        v_toPure_5369_,
        v_k_5370_,
        v_c_5371_,
        v_fvarId_5372_,
        v_pu_boxed_5381_,
        v_inst_5374_,
        v_inst_5375_,
        v_f_5376_,
        v_toBind_5377_,
        v_____do__lift_5378_,
    );
    return v_res_5382_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(
    mut v_n_5383_: *mut LeanObject,
    mut v_check_5384_: u8,
    mut v_persistent_5385_: u8,
    mut v_objs_x3f_5386_: *mut LeanObject,
    mut v_toPure_5387_: *mut LeanObject,
    mut v_k_5388_: *mut LeanObject,
    mut v_c_5389_: *mut LeanObject,
    mut v_fvarId_5390_: *mut LeanObject,
    mut v_pu_5391_: u8,
    mut v_inst_5392_: *mut LeanObject,
    mut v_inst_5393_: *mut LeanObject,
    mut v_f_5394_: *mut LeanObject,
    mut v_toBind_5395_: *mut LeanObject,
    mut v_____do__lift_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    v___x_5397_ = lean_box((v_check_5384_) as usize);
    v___x_5398_ = lean_box((v_persistent_5385_) as usize);
    lean_inc_ref(v_k_5388_);
    v___f_5399_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_5399_, 0, v_____do__lift_5396_);
    lean_closure_set(v___f_5399_, 1, v_n_5383_);
    lean_closure_set(v___f_5399_, 2, v___x_5397_);
    lean_closure_set(v___f_5399_, 3, v___x_5398_);
    lean_closure_set(v___f_5399_, 4, v_objs_x3f_5386_);
    lean_closure_set(v___f_5399_, 5, v_toPure_5387_);
    lean_closure_set(v___f_5399_, 6, v_k_5388_);
    lean_closure_set(v___f_5399_, 7, v_c_5389_);
    lean_closure_set(v___f_5399_, 8, v_fvarId_5390_);
    v___x_5400_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5391_,
        v_inst_5392_,
        v_inst_5393_,
        v_f_5394_,
        v_k_5388_,
    );
    v___x_5401_ = lean_apply_4(
        v_toBind_5395_,
        lean_box(0),
        lean_box(0),
        v___x_5400_,
        v___f_5399_,
    );
    return v___x_5401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(
    mut v_n_5402_: *mut LeanObject,
    mut v_check_5403_: *mut LeanObject,
    mut v_persistent_5404_: *mut LeanObject,
    mut v_objs_x3f_5405_: *mut LeanObject,
    mut v_toPure_5406_: *mut LeanObject,
    mut v_k_5407_: *mut LeanObject,
    mut v_c_5408_: *mut LeanObject,
    mut v_fvarId_5409_: *mut LeanObject,
    mut v_pu_5410_: *mut LeanObject,
    mut v_inst_5411_: *mut LeanObject,
    mut v_inst_5412_: *mut LeanObject,
    mut v_f_5413_: *mut LeanObject,
    mut v_toBind_5414_: *mut LeanObject,
    mut v_____do__lift_5415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_2482__boxed_5416_: u8 = 0;
    let mut v_persistent_2483__boxed_5417_: u8 = 0;
    let mut v_pu_boxed_5418_: u8 = 0;
    let mut v_res_5419_: *mut LeanObject = core::ptr::null_mut();
    v_check_2482__boxed_5416_ = (lean_unbox(v_check_5403_) as u8);
    v_persistent_2483__boxed_5417_ = (lean_unbox(v_persistent_5404_) as u8);
    v_pu_boxed_5418_ = (lean_unbox(v_pu_5410_) as u8);
    v_res_5419_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(
        v_n_5402_,
        v_check_2482__boxed_5416_,
        v_persistent_2483__boxed_5417_,
        v_objs_x3f_5405_,
        v_toPure_5406_,
        v_k_5407_,
        v_c_5408_,
        v_fvarId_5409_,
        v_pu_boxed_5418_,
        v_inst_5411_,
        v_inst_5412_,
        v_f_5413_,
        v_toBind_5414_,
        v_____do__lift_5415_,
    );
    return v_res_5419_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(
    mut v_toPure_5420_: *mut LeanObject,
    mut v_c_5421_: *mut LeanObject,
    mut v_fvarId_5422_: *mut LeanObject,
    mut v_k_5423_: *mut LeanObject,
    mut v_pu_5424_: u8,
    mut v_inst_5425_: *mut LeanObject,
    mut v_inst_5426_: *mut LeanObject,
    mut v_f_5427_: *mut LeanObject,
    mut v_toBind_5428_: *mut LeanObject,
    mut v_____do__lift_5429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_k_5423_);
    v___f_5430_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5430_, 0, v_____do__lift_5429_);
    lean_closure_set(v___f_5430_, 1, v_toPure_5420_);
    lean_closure_set(v___f_5430_, 2, v_c_5421_);
    lean_closure_set(v___f_5430_, 3, v_fvarId_5422_);
    lean_closure_set(v___f_5430_, 4, v_k_5423_);
    v___x_5431_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5424_,
        v_inst_5425_,
        v_inst_5426_,
        v_f_5427_,
        v_k_5423_,
    );
    v___x_5432_ = lean_apply_4(
        v_toBind_5428_,
        lean_box(0),
        lean_box(0),
        v___x_5431_,
        v___f_5430_,
    );
    return v___x_5432_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(
    mut v_toPure_5433_: *mut LeanObject,
    mut v_c_5434_: *mut LeanObject,
    mut v_fvarId_5435_: *mut LeanObject,
    mut v_k_5436_: *mut LeanObject,
    mut v_pu_5437_: *mut LeanObject,
    mut v_inst_5438_: *mut LeanObject,
    mut v_inst_5439_: *mut LeanObject,
    mut v_f_5440_: *mut LeanObject,
    mut v_toBind_5441_: *mut LeanObject,
    mut v_____do__lift_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5443_: u8 = 0;
    let mut v_res_5444_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5443_ = (lean_unbox(v_pu_5437_) as u8);
    v_res_5444_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(
        v_toPure_5433_,
        v_c_5434_,
        v_fvarId_5435_,
        v_k_5436_,
        v_pu_boxed_5443_,
        v_inst_5438_,
        v_inst_5439_,
        v_f_5440_,
        v_toBind_5441_,
        v_____do__lift_5442_,
    );
    return v_res_5444_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
    mut v_pu_5445_: u8,
    mut v_inst_5446_: *mut LeanObject,
    mut v_inst_5447_: *mut LeanObject,
    mut v_f_5448_: *mut LeanObject,
    mut v_c_5449_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_c_5449_) {
        0 => {
            let mut v_toApplicative_5450_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5451_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_5453_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5454_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5450_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5451_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5451_, 2);
            v_toPure_5452_ = lean_ctor_get(v_toApplicative_5450_, 1);
            v_decl_5453_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_ref_n(v_decl_5453_, 2);
            v_k_5454_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc_ref(v_k_5454_);
            v___x_5455_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            lean_inc_ref(v_inst_5447_);
            lean_inc(v_inst_5446_);
            lean_inc(v_toPure_5452_);
            v___f_5456_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5456_, 0, v_toPure_5452_);
            lean_closure_set(v___f_5456_, 1, v_c_5449_);
            lean_closure_set(v___f_5456_, 2, v_k_5454_);
            lean_closure_set(v___f_5456_, 3, v_decl_5453_);
            lean_closure_set(v___f_5456_, 4, v___x_5455_);
            lean_closure_set(v___f_5456_, 5, v_inst_5446_);
            lean_closure_set(v___f_5456_, 6, v_inst_5447_);
            lean_closure_set(v___f_5456_, 7, v_f_5448_);
            lean_closure_set(v___f_5456_, 8, v_toBind_5451_);
            v___x_5457_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
                v_pu_5445_,
                v_inst_5446_,
                v_inst_5447_,
                v_f_5448_,
                v_decl_5453_,
            );
            v___x_5458_ = lean_apply_4(
                v_toBind_5451_,
                lean_box(0),
                lean_box(0),
                v___x_5457_,
                v___f_5456_,
            );
            return v___x_5458_;
        }
        1 => {
            let mut v_toApplicative_5459_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_5460_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5461_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5462_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5463_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_5464_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_5465_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_5466_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5468_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5470_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_5473_: usize = 0;
            let mut v___x_5474_: usize = 0;
            let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5459_ = lean_ctor_get(v_inst_5447_, 0);
            v_decl_5460_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_ref_n(v_decl_5460_, 2);
            v_toBind_5461_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5461_, 3);
            v_toPure_5462_ = lean_ctor_get(v_toApplicative_5459_, 1);
            v_k_5463_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc_ref(v_k_5463_);
            v_params_5464_ = lean_ctor_get(v_decl_5460_, 2);
            lean_inc_ref(v_params_5464_);
            v_type_5465_ = lean_ctor_get(v_decl_5460_, 3);
            lean_inc_ref(v_type_5465_);
            v_value_5466_ = lean_ctor_get(v_decl_5460_, 4);
            lean_inc_ref(v_value_5466_);
            v___x_5467_ = lean_box((v_pu_5445_) as usize);
            lean_inc_n(v_f_5448_, 2);
            lean_inc_ref_n(v_inst_5447_, 3);
            lean_inc_n(v_inst_5446_, 2);
            lean_inc(v_toPure_5462_);
            v___f_5468_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5468_, 0, v_toPure_5462_);
            lean_closure_set(v___f_5468_, 1, v_c_5449_);
            lean_closure_set(v___f_5468_, 2, v_k_5463_);
            lean_closure_set(v___f_5468_, 3, v_decl_5460_);
            lean_closure_set(v___f_5468_, 4, v___x_5467_);
            lean_closure_set(v___f_5468_, 5, v_inst_5446_);
            lean_closure_set(v___f_5468_, 6, v_inst_5447_);
            lean_closure_set(v___f_5468_, 7, v_f_5448_);
            lean_closure_set(v___f_5468_, 8, v_toBind_5461_);
            v___x_5469_ = lean_box((v_pu_5445_) as usize);
            v___f_5470_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5470_, 0, v___x_5469_);
            lean_closure_set(v___f_5470_, 1, v_decl_5460_);
            lean_closure_set(v___f_5470_, 2, v_inst_5446_);
            lean_closure_set(v___f_5470_, 3, v_toBind_5461_);
            lean_closure_set(v___f_5470_, 4, v___f_5468_);
            lean_closure_set(v___f_5470_, 5, v_inst_5447_);
            lean_closure_set(v___f_5470_, 6, v_f_5448_);
            lean_closure_set(v___f_5470_, 7, v_value_5466_);
            lean_closure_set(v___f_5470_, 8, v_type_5465_);
            v___x_5471_ = lean_box((v_pu_5445_) as usize);
            v___x_5472_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___x_5472_, 0, lean_box(0));
            lean_closure_set(v___x_5472_, 1, v___x_5471_);
            lean_closure_set(v___x_5472_, 2, v_inst_5446_);
            lean_closure_set(v___x_5472_, 3, v_inst_5447_);
            lean_closure_set(v___x_5472_, 4, v_f_5448_);
            v_sz_5473_ = lean_array_size(v_params_5464_);
            v___x_5474_ = 0usize;
            v___x_5475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_5447_,
                v___x_5472_,
                v_sz_5473_,
                v___x_5474_,
                v_params_5464_,
            );
            v___x_5476_ = lean_apply_4(
                v_toBind_5461_,
                lean_box(0),
                lean_box(0),
                v___x_5475_,
                v___f_5470_,
            );
            return v___x_5476_;
        }
        2 => {
            let mut v_toApplicative_5477_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_5478_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5479_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5480_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5481_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_5482_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_5483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_5484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5488_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_5491_: usize = 0;
            let mut v___x_5492_: usize = 0;
            let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5477_ = lean_ctor_get(v_inst_5447_, 0);
            v_decl_5478_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_ref_n(v_decl_5478_, 2);
            v_toBind_5479_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5479_, 3);
            v_toPure_5480_ = lean_ctor_get(v_toApplicative_5477_, 1);
            v_k_5481_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc_ref(v_k_5481_);
            v_params_5482_ = lean_ctor_get(v_decl_5478_, 2);
            lean_inc_ref(v_params_5482_);
            v_type_5483_ = lean_ctor_get(v_decl_5478_, 3);
            lean_inc_ref(v_type_5483_);
            v_value_5484_ = lean_ctor_get(v_decl_5478_, 4);
            lean_inc_ref(v_value_5484_);
            v___x_5485_ = lean_box((v_pu_5445_) as usize);
            lean_inc_n(v_f_5448_, 2);
            lean_inc_ref_n(v_inst_5447_, 3);
            lean_inc_n(v_inst_5446_, 2);
            lean_inc(v_toPure_5480_);
            v___f_5486_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5486_, 0, v_toPure_5480_);
            lean_closure_set(v___f_5486_, 1, v_c_5449_);
            lean_closure_set(v___f_5486_, 2, v_k_5481_);
            lean_closure_set(v___f_5486_, 3, v_decl_5478_);
            lean_closure_set(v___f_5486_, 4, v___x_5485_);
            lean_closure_set(v___f_5486_, 5, v_inst_5446_);
            lean_closure_set(v___f_5486_, 6, v_inst_5447_);
            lean_closure_set(v___f_5486_, 7, v_f_5448_);
            lean_closure_set(v___f_5486_, 8, v_toBind_5479_);
            v___x_5487_ = lean_box((v_pu_5445_) as usize);
            v___f_5488_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5488_, 0, v___x_5487_);
            lean_closure_set(v___f_5488_, 1, v_decl_5478_);
            lean_closure_set(v___f_5488_, 2, v_inst_5446_);
            lean_closure_set(v___f_5488_, 3, v_toBind_5479_);
            lean_closure_set(v___f_5488_, 4, v___f_5486_);
            lean_closure_set(v___f_5488_, 5, v_inst_5447_);
            lean_closure_set(v___f_5488_, 6, v_f_5448_);
            lean_closure_set(v___f_5488_, 7, v_value_5484_);
            lean_closure_set(v___f_5488_, 8, v_type_5483_);
            v___x_5489_ = lean_box((v_pu_5445_) as usize);
            v___x_5490_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___x_5490_, 0, lean_box(0));
            lean_closure_set(v___x_5490_, 1, v___x_5489_);
            lean_closure_set(v___x_5490_, 2, v_inst_5446_);
            lean_closure_set(v___x_5490_, 3, v_inst_5447_);
            lean_closure_set(v___x_5490_, 4, v_f_5448_);
            v_sz_5491_ = lean_array_size(v_params_5482_);
            v___x_5492_ = 0usize;
            v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_5447_,
                v___x_5490_,
                v_sz_5491_,
                v___x_5492_,
                v_params_5482_,
            );
            v___x_5494_ = lean_apply_4(
                v_toBind_5479_,
                lean_box(0),
                lean_box(0),
                v___x_5493_,
                v___f_5488_,
            );
            return v___x_5494_;
        }
        3 => {
            let mut v_toApplicative_5495_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5496_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5497_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5498_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_5499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5501_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5495_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5496_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5496_, 2);
            v_toPure_5497_ = lean_ctor_get(v_toApplicative_5495_, 1);
            lean_inc(v_toPure_5497_);
            v_fvarId_5498_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5498_, 2);
            v_args_5499_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc_ref(v_args_5499_);
            v___x_5500_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5501_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5501_, 0, v_toPure_5497_);
            lean_closure_set(v___f_5501_, 1, v_c_5449_);
            lean_closure_set(v___f_5501_, 2, v_fvarId_5498_);
            lean_closure_set(v___f_5501_, 3, v_args_5499_);
            lean_closure_set(v___f_5501_, 4, v___x_5500_);
            lean_closure_set(v___f_5501_, 5, v_inst_5446_);
            lean_closure_set(v___f_5501_, 6, v_inst_5447_);
            lean_closure_set(v___f_5501_, 7, v_f_5448_);
            lean_closure_set(v___f_5501_, 8, v_toBind_5496_);
            v___x_5502_ = lean_apply_1(v_f_5448_, v_fvarId_5498_);
            v___x_5503_ = lean_apply_4(
                v_toBind_5496_,
                lean_box(0),
                lean_box(0),
                v___x_5502_,
                v___f_5501_,
            );
            return v___x_5503_;
        }
        4 => {
            let mut v_toApplicative_5504_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cases_5505_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5506_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5507_: *mut LeanObject = core::ptr::null_mut();
            let mut v_typeName_5508_: *mut LeanObject = core::ptr::null_mut();
            let mut v_resultType_5509_: *mut LeanObject = core::ptr::null_mut();
            let mut v_discr_5510_: *mut LeanObject = core::ptr::null_mut();
            let mut v_alts_5511_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5513_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5504_ = lean_ctor_get(v_inst_5447_, 0);
            v_cases_5505_ = lean_ctor_get(v_c_5449_, 0);
            v_toBind_5506_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5506_, 2);
            v_toPure_5507_ = lean_ctor_get(v_toApplicative_5504_, 1);
            v_typeName_5508_ = lean_ctor_get(v_cases_5505_, 0);
            lean_inc(v_typeName_5508_);
            v_resultType_5509_ = lean_ctor_get(v_cases_5505_, 1);
            lean_inc_ref_n(v_resultType_5509_, 2);
            v_discr_5510_ = lean_ctor_get(v_cases_5505_, 2);
            lean_inc(v_discr_5510_);
            v_alts_5511_ = lean_ctor_get(v_cases_5505_, 3);
            lean_inc_ref(v_alts_5511_);
            v___x_5512_ = lean_box((v_pu_5445_) as usize);
            lean_inc_n(v_f_5448_, 2);
            lean_inc_ref_n(v_inst_5447_, 2);
            v___f_5513_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5513_, 0, v___x_5512_);
            lean_closure_set(v___f_5513_, 1, v_inst_5446_);
            lean_closure_set(v___f_5513_, 2, v_inst_5447_);
            lean_closure_set(v___f_5513_, 3, v_f_5448_);
            lean_inc(v_toPure_5507_);
            v___f_5514_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14 as *mut core::ffi::c_void,
                11,
                10,
            );
            lean_closure_set(v___f_5514_, 0, v_typeName_5508_);
            lean_closure_set(v___f_5514_, 1, v_toPure_5507_);
            lean_closure_set(v___f_5514_, 2, v_discr_5510_);
            lean_closure_set(v___f_5514_, 3, v_c_5449_);
            lean_closure_set(v___f_5514_, 4, v_alts_5511_);
            lean_closure_set(v___f_5514_, 5, v_resultType_5509_);
            lean_closure_set(v___f_5514_, 6, v_inst_5447_);
            lean_closure_set(v___f_5514_, 7, v___f_5513_);
            lean_closure_set(v___f_5514_, 8, v_toBind_5506_);
            lean_closure_set(v___f_5514_, 9, v_f_5448_);
            v___x_5515_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                v_inst_5447_,
                v_f_5448_,
                v_resultType_5509_,
            );
            v___x_5516_ = lean_apply_4(
                v_toBind_5506_,
                lean_box(0),
                lean_box(0),
                v___x_5515_,
                v___f_5514_,
            );
            return v___x_5516_;
        }
        5 => {
            let mut v_toApplicative_5517_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5518_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5519_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5520_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5517_ = lean_ctor_get(v_inst_5447_, 0);
            lean_inc_ref(v_toApplicative_5517_);
            lean_dec(v_inst_5446_);
            v_toBind_5518_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc(v_toBind_5518_);
            lean_dec_ref(v_inst_5447_);
            v_toPure_5519_ = lean_ctor_get(v_toApplicative_5517_, 1);
            lean_inc(v_toPure_5519_);
            lean_dec_ref(v_toApplicative_5517_);
            v_fvarId_5520_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5520_, 2);
            v___f_5521_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5521_, 0, v_fvarId_5520_);
            lean_closure_set(v___f_5521_, 1, v_toPure_5519_);
            lean_closure_set(v___f_5521_, 2, v_c_5449_);
            v___x_5522_ = lean_apply_1(v_f_5448_, v_fvarId_5520_);
            v___x_5523_ = lean_apply_4(
                v_toBind_5518_,
                lean_box(0),
                lean_box(0),
                v___x_5522_,
                v___f_5521_,
            );
            return v___x_5523_;
        }
        6 => {
            let mut v_toApplicative_5524_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5525_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5526_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_5527_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5524_ = lean_ctor_get(v_inst_5447_, 0);
            lean_dec(v_inst_5446_);
            v_toBind_5525_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc(v_toBind_5525_);
            v_toPure_5526_ = lean_ctor_get(v_toApplicative_5524_, 1);
            v_type_5527_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_ref_n(v_type_5527_, 2);
            lean_inc(v_toPure_5526_);
            v___f_5528_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5528_, 0, v_type_5527_);
            lean_closure_set(v___f_5528_, 1, v_toPure_5526_);
            lean_closure_set(v___f_5528_, 2, v_c_5449_);
            v___x_5529_ =
                l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5447_, v_f_5448_, v_type_5527_);
            v___x_5530_ = lean_apply_4(
                v_toBind_5525_,
                lean_box(0),
                lean_box(0),
                v___x_5529_,
                v___f_5528_,
            );
            return v___x_5530_;
        }
        7 => {
            let mut v_toApplicative_5531_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5532_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5533_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5534_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_5535_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5537_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5539_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5531_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5532_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5532_, 2);
            v_toPure_5533_ = lean_ctor_get(v_toApplicative_5531_, 1);
            lean_inc(v_toPure_5533_);
            v_fvarId_5534_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5534_, 2);
            v_i_5535_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_i_5535_);
            v_y_5536_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc(v_y_5536_);
            v_k_5537_ = lean_ctor_get(v_c_5449_, 3);
            lean_inc_ref(v_k_5537_);
            v___x_5538_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5539_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed
                    as *mut core::ffi::c_void,
                12,
                11,
            );
            lean_closure_set(v___f_5539_, 0, v_i_5535_);
            lean_closure_set(v___f_5539_, 1, v_toPure_5533_);
            lean_closure_set(v___f_5539_, 2, v_y_5536_);
            lean_closure_set(v___f_5539_, 3, v_k_5537_);
            lean_closure_set(v___f_5539_, 4, v_c_5449_);
            lean_closure_set(v___f_5539_, 5, v_fvarId_5534_);
            lean_closure_set(v___f_5539_, 6, v___x_5538_);
            lean_closure_set(v___f_5539_, 7, v_inst_5446_);
            lean_closure_set(v___f_5539_, 8, v_inst_5447_);
            lean_closure_set(v___f_5539_, 9, v_f_5448_);
            lean_closure_set(v___f_5539_, 10, v_toBind_5532_);
            v___x_5540_ = lean_apply_1(v_f_5448_, v_fvarId_5534_);
            v___x_5541_ = lean_apply_4(
                v_toBind_5532_,
                lean_box(0),
                lean_box(0),
                v___x_5540_,
                v___f_5539_,
            );
            return v___x_5541_;
        }
        8 => {
            let mut v_toApplicative_5542_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5543_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5544_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5545_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_5546_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5547_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5548_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5550_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5542_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5543_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5543_, 2);
            v_toPure_5544_ = lean_ctor_get(v_toApplicative_5542_, 1);
            lean_inc(v_toPure_5544_);
            v_fvarId_5545_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5545_, 2);
            v_i_5546_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_i_5546_);
            v_y_5547_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc(v_y_5547_);
            v_k_5548_ = lean_ctor_get(v_c_5449_, 3);
            lean_inc_ref(v_k_5548_);
            v___x_5549_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5550_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed
                    as *mut core::ffi::c_void,
                12,
                11,
            );
            lean_closure_set(v___f_5550_, 0, v_i_5546_);
            lean_closure_set(v___f_5550_, 1, v_toPure_5544_);
            lean_closure_set(v___f_5550_, 2, v_y_5547_);
            lean_closure_set(v___f_5550_, 3, v_k_5548_);
            lean_closure_set(v___f_5550_, 4, v_c_5449_);
            lean_closure_set(v___f_5550_, 5, v_fvarId_5545_);
            lean_closure_set(v___f_5550_, 6, v___x_5549_);
            lean_closure_set(v___f_5550_, 7, v_inst_5446_);
            lean_closure_set(v___f_5550_, 8, v_inst_5447_);
            lean_closure_set(v___f_5550_, 9, v_f_5448_);
            lean_closure_set(v___f_5550_, 10, v_toBind_5543_);
            v___x_5551_ = lean_apply_1(v_f_5448_, v_fvarId_5545_);
            v___x_5552_ = lean_apply_4(
                v_toBind_5543_,
                lean_box(0),
                lean_box(0),
                v___x_5551_,
                v___f_5550_,
            );
            return v___x_5552_;
        }
        9 => {
            let mut v_toApplicative_5553_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5554_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5555_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5556_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_5557_: *mut LeanObject = core::ptr::null_mut();
            let mut v_offset_5558_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5559_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_5560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5561_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5563_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5553_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5554_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5554_, 2);
            v_toPure_5555_ = lean_ctor_get(v_toApplicative_5553_, 1);
            lean_inc(v_toPure_5555_);
            v_fvarId_5556_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5556_, 2);
            v_i_5557_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_i_5557_);
            v_offset_5558_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc(v_offset_5558_);
            v_y_5559_ = lean_ctor_get(v_c_5449_, 3);
            lean_inc(v_y_5559_);
            v_ty_5560_ = lean_ctor_get(v_c_5449_, 4);
            lean_inc_ref(v_ty_5560_);
            v_k_5561_ = lean_ctor_get(v_c_5449_, 5);
            lean_inc_ref(v_k_5561_);
            v___x_5562_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5563_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed
                    as *mut core::ffi::c_void,
                14,
                13,
            );
            lean_closure_set(v___f_5563_, 0, v_i_5557_);
            lean_closure_set(v___f_5563_, 1, v_offset_5558_);
            lean_closure_set(v___f_5563_, 2, v_toPure_5555_);
            lean_closure_set(v___f_5563_, 3, v_y_5559_);
            lean_closure_set(v___f_5563_, 4, v_ty_5560_);
            lean_closure_set(v___f_5563_, 5, v_k_5561_);
            lean_closure_set(v___f_5563_, 6, v_c_5449_);
            lean_closure_set(v___f_5563_, 7, v_fvarId_5556_);
            lean_closure_set(v___f_5563_, 8, v___x_5562_);
            lean_closure_set(v___f_5563_, 9, v_inst_5446_);
            lean_closure_set(v___f_5563_, 10, v_inst_5447_);
            lean_closure_set(v___f_5563_, 11, v_f_5448_);
            lean_closure_set(v___f_5563_, 12, v_toBind_5554_);
            v___x_5564_ = lean_apply_1(v_f_5448_, v_fvarId_5556_);
            v___x_5565_ = lean_apply_4(
                v_toBind_5554_,
                lean_box(0),
                lean_box(0),
                v___x_5564_,
                v___f_5563_,
            );
            return v___x_5565_;
        }
        10 => {
            let mut v_toApplicative_5566_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5567_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5568_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5569_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cidx_5570_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5566_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5567_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5567_, 2);
            v_toPure_5568_ = lean_ctor_get(v_toApplicative_5566_, 1);
            lean_inc(v_toPure_5568_);
            v_fvarId_5569_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5569_, 2);
            v_cidx_5570_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_cidx_5570_);
            v_k_5571_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc_ref(v_k_5571_);
            v___x_5572_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5573_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed
                    as *mut core::ffi::c_void,
                11,
                10,
            );
            lean_closure_set(v___f_5573_, 0, v_cidx_5570_);
            lean_closure_set(v___f_5573_, 1, v_toPure_5568_);
            lean_closure_set(v___f_5573_, 2, v_k_5571_);
            lean_closure_set(v___f_5573_, 3, v_c_5449_);
            lean_closure_set(v___f_5573_, 4, v_fvarId_5569_);
            lean_closure_set(v___f_5573_, 5, v___x_5572_);
            lean_closure_set(v___f_5573_, 6, v_inst_5446_);
            lean_closure_set(v___f_5573_, 7, v_inst_5447_);
            lean_closure_set(v___f_5573_, 8, v_f_5448_);
            lean_closure_set(v___f_5573_, 9, v_toBind_5567_);
            v___x_5574_ = lean_apply_1(v_f_5448_, v_fvarId_5569_);
            v___x_5575_ = lean_apply_4(
                v_toBind_5567_,
                lean_box(0),
                lean_box(0),
                v___x_5574_,
                v___f_5573_,
            );
            return v___x_5575_;
        }
        11 => {
            let mut v_toApplicative_5576_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5577_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5578_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5579_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_5580_: *mut LeanObject = core::ptr::null_mut();
            let mut v_check_5581_: u8 = 0;
            let mut v_persistent_5582_: u8 = 0;
            let mut v_k_5583_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5587_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5576_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5577_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5577_, 2);
            v_toPure_5578_ = lean_ctor_get(v_toApplicative_5576_, 1);
            lean_inc(v_toPure_5578_);
            v_fvarId_5579_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5579_, 2);
            v_n_5580_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_n_5580_);
            v_check_5581_ = lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_persistent_5582_ = lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
            );
            v_k_5583_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc_ref(v_k_5583_);
            v___x_5584_ = lean_box((v_check_5581_) as usize);
            v___x_5585_ = lean_box((v_persistent_5582_) as usize);
            v___x_5586_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5587_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            lean_closure_set(v___f_5587_, 0, v_n_5580_);
            lean_closure_set(v___f_5587_, 1, v___x_5584_);
            lean_closure_set(v___f_5587_, 2, v___x_5585_);
            lean_closure_set(v___f_5587_, 3, v_toPure_5578_);
            lean_closure_set(v___f_5587_, 4, v_k_5583_);
            lean_closure_set(v___f_5587_, 5, v_c_5449_);
            lean_closure_set(v___f_5587_, 6, v_fvarId_5579_);
            lean_closure_set(v___f_5587_, 7, v___x_5586_);
            lean_closure_set(v___f_5587_, 8, v_inst_5446_);
            lean_closure_set(v___f_5587_, 9, v_inst_5447_);
            lean_closure_set(v___f_5587_, 10, v_f_5448_);
            lean_closure_set(v___f_5587_, 11, v_toBind_5577_);
            v___x_5588_ = lean_apply_1(v_f_5448_, v_fvarId_5579_);
            v___x_5589_ = lean_apply_4(
                v_toBind_5577_,
                lean_box(0),
                lean_box(0),
                v___x_5588_,
                v___f_5587_,
            );
            return v___x_5589_;
        }
        12 => {
            let mut v_toApplicative_5590_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5591_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5592_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5593_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_5594_: *mut LeanObject = core::ptr::null_mut();
            let mut v_check_5595_: u8 = 0;
            let mut v_persistent_5596_: u8 = 0;
            let mut v_objs_x3f_5597_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5598_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5602_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5590_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5591_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5591_, 2);
            v_toPure_5592_ = lean_ctor_get(v_toApplicative_5590_, 1);
            lean_inc(v_toPure_5592_);
            v_fvarId_5593_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5593_, 2);
            v_n_5594_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc(v_n_5594_);
            v_check_5595_ = lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
            );
            v_persistent_5596_ = lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
            );
            v_objs_x3f_5597_ = lean_ctor_get(v_c_5449_, 2);
            lean_inc(v_objs_x3f_5597_);
            v_k_5598_ = lean_ctor_get(v_c_5449_, 3);
            lean_inc_ref(v_k_5598_);
            v___x_5599_ = lean_box((v_check_5595_) as usize);
            v___x_5600_ = lean_box((v_persistent_5596_) as usize);
            v___x_5601_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5602_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed
                    as *mut core::ffi::c_void,
                14,
                13,
            );
            lean_closure_set(v___f_5602_, 0, v_n_5594_);
            lean_closure_set(v___f_5602_, 1, v___x_5599_);
            lean_closure_set(v___f_5602_, 2, v___x_5600_);
            lean_closure_set(v___f_5602_, 3, v_objs_x3f_5597_);
            lean_closure_set(v___f_5602_, 4, v_toPure_5592_);
            lean_closure_set(v___f_5602_, 5, v_k_5598_);
            lean_closure_set(v___f_5602_, 6, v_c_5449_);
            lean_closure_set(v___f_5602_, 7, v_fvarId_5593_);
            lean_closure_set(v___f_5602_, 8, v___x_5601_);
            lean_closure_set(v___f_5602_, 9, v_inst_5446_);
            lean_closure_set(v___f_5602_, 10, v_inst_5447_);
            lean_closure_set(v___f_5602_, 11, v_f_5448_);
            lean_closure_set(v___f_5602_, 12, v_toBind_5591_);
            v___x_5603_ = lean_apply_1(v_f_5448_, v_fvarId_5593_);
            v___x_5604_ = lean_apply_4(
                v_toBind_5591_,
                lean_box(0),
                lean_box(0),
                v___x_5603_,
                v___f_5602_,
            );
            return v___x_5604_;
        }
        _ => {
            let mut v_toApplicative_5605_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5606_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5607_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5608_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5609_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5605_ = lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5606_ = lean_ctor_get(v_inst_5447_, 1);
            lean_inc_n(v_toBind_5606_, 2);
            v_toPure_5607_ = lean_ctor_get(v_toApplicative_5605_, 1);
            lean_inc(v_toPure_5607_);
            v_fvarId_5608_ = lean_ctor_get(v_c_5449_, 0);
            lean_inc_n(v_fvarId_5608_, 2);
            v_k_5609_ = lean_ctor_get(v_c_5449_, 1);
            lean_inc_ref(v_k_5609_);
            v___x_5610_ = lean_box((v_pu_5445_) as usize);
            lean_inc(v_f_5448_);
            v___f_5611_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_5611_, 0, v_toPure_5607_);
            lean_closure_set(v___f_5611_, 1, v_c_5449_);
            lean_closure_set(v___f_5611_, 2, v_fvarId_5608_);
            lean_closure_set(v___f_5611_, 3, v_k_5609_);
            lean_closure_set(v___f_5611_, 4, v___x_5610_);
            lean_closure_set(v___f_5611_, 5, v_inst_5446_);
            lean_closure_set(v___f_5611_, 6, v_inst_5447_);
            lean_closure_set(v___f_5611_, 7, v_f_5448_);
            lean_closure_set(v___f_5611_, 8, v_toBind_5606_);
            v___x_5612_ = lean_apply_1(v_f_5448_, v_fvarId_5608_);
            v___x_5613_ = lean_apply_4(
                v_toBind_5606_,
                lean_box(0),
                lean_box(0),
                v___x_5612_,
                v___f_5611_,
            );
            return v___x_5613_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(
    mut v_pu_5614_: *mut LeanObject,
    mut v_inst_5615_: *mut LeanObject,
    mut v_inst_5616_: *mut LeanObject,
    mut v_f_5617_: *mut LeanObject,
    mut v_c_5618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5619_: u8 = 0;
    let mut v_res_5620_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5619_ = (lean_unbox(v_pu_5614_) as u8);
    v_res_5620_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_boxed_5619_,
        v_inst_5615_,
        v_inst_5616_,
        v_f_5617_,
        v_c_5618_,
    );
    return v_res_5620_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(
    mut v_pu_5621_: u8,
    mut v_inst_5622_: *mut LeanObject,
    mut v_inst_5623_: *mut LeanObject,
    mut v_f_5624_: *mut LeanObject,
    mut v_x_5625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    v___x_5626_ = lean_box((v_pu_5621_) as usize);
    lean_inc_ref(v_inst_5623_);
    v___x_5627_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_5627_, 0, v___x_5626_);
    lean_closure_set(v___x_5627_, 1, v_inst_5622_);
    lean_closure_set(v___x_5627_, 2, v_inst_5623_);
    lean_closure_set(v___x_5627_, 3, v_f_5624_);
    v___x_5628_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_5623_, v_x_5625_, v___x_5627_);
    return v___x_5628_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM(
    mut v_m_5629_: *mut LeanObject,
    mut v_pu_5630_: u8,
    mut v_inst_5631_: *mut LeanObject,
    mut v_inst_5632_: *mut LeanObject,
    mut v_f_5633_: *mut LeanObject,
    mut v_c_5634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    v___x_5635_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5630_,
        v_inst_5631_,
        v_inst_5632_,
        v_f_5633_,
        v_c_5634_,
    );
    return v___x_5635_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(
    mut v_m_5636_: *mut LeanObject,
    mut v_pu_5637_: *mut LeanObject,
    mut v_inst_5638_: *mut LeanObject,
    mut v_inst_5639_: *mut LeanObject,
    mut v_f_5640_: *mut LeanObject,
    mut v_c_5641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5642_: u8 = 0;
    let mut v_res_5643_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5642_ = (lean_unbox(v_pu_5637_) as u8);
    v_res_5643_ = l_Lean_Compiler_LCNF_Code_mapFVarM(
        v_m_5636_,
        v_pu_boxed_5642_,
        v_inst_5638_,
        v_inst_5639_,
        v_f_5640_,
        v_c_5641_,
    );
    return v_res_5643_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(
    mut v_inst_5644_: *mut LeanObject,
    mut v_f_5645_: *mut LeanObject,
    mut v_type_5646_: *mut LeanObject,
    mut v_toBind_5647_: *mut LeanObject,
    mut v___f_5648_: *mut LeanObject,
    mut v_____r_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    v___x_5650_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5644_, v_f_5645_, v_type_5646_);
    v___x_5651_ = lean_apply_4(
        v_toBind_5647_,
        lean_box(0),
        lean_box(0),
        v___x_5650_,
        v___f_5648_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(
    mut v_inst_5652_: *mut LeanObject,
    mut v_f_5653_: *mut LeanObject,
    mut v_ty_5654_: *mut LeanObject,
    mut v_toBind_5655_: *mut LeanObject,
    mut v___f_5656_: *mut LeanObject,
    mut v_____r_5657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    v___x_5658_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5652_, v_f_5653_, v_ty_5654_);
    v___x_5659_ = lean_apply_4(
        v_toBind_5655_,
        lean_box(0),
        lean_box(0),
        v___x_5658_,
        v___f_5656_,
    );
    return v___x_5659_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(
    mut v_args_5660_: *mut LeanObject,
    mut v_toApplicative_5661_: *mut LeanObject,
    mut v_inst_5662_: *mut LeanObject,
    mut v___f_5663_: *mut LeanObject,
    mut v_____r_5664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    v___x_5665_ = lean_unsigned_to_nat(0);
    v___x_5666_ = lean_array_get_size(v_args_5660_);
    v___x_5667_ = lean_box(0);
    v___x_5668_ = lean_nat_dec_lt(v___x_5665_, v___x_5666_);
    if v___x_5668_ == 0 {
        let mut v_toPure_5669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_5663_);
        lean_dec_ref(v_inst_5662_);
        lean_dec_ref(v_args_5660_);
        v_toPure_5669_ = lean_ctor_get(v_toApplicative_5661_, 1);
        lean_inc(v_toPure_5669_);
        lean_dec_ref(v_toApplicative_5661_);
        v___x_5670_ = lean_apply_2(v_toPure_5669_, lean_box(0), v___x_5667_);
        return v___x_5670_;
    } else {
        let mut v___x_5671_: u8 = 0;
        v___x_5671_ = lean_nat_dec_le(v___x_5666_, v___x_5666_);
        if v___x_5671_ == 0 {
            if v___x_5668_ == 0 {
                let mut v_toPure_5672_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_5663_);
                lean_dec_ref(v_inst_5662_);
                lean_dec_ref(v_args_5660_);
                v_toPure_5672_ = lean_ctor_get(v_toApplicative_5661_, 1);
                lean_inc(v_toPure_5672_);
                lean_dec_ref(v_toApplicative_5661_);
                v___x_5673_ = lean_apply_2(v_toPure_5672_, lean_box(0), v___x_5667_);
                return v___x_5673_;
            } else {
                let mut v___x_5674_: usize = 0;
                let mut v___x_5675_: usize = 0;
                let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_5661_);
                v___x_5674_ = 0usize;
                v___x_5675_ = lean_usize_of_nat(v___x_5666_);
                v___x_5676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_5662_,
                    v___f_5663_,
                    v_args_5660_,
                    v___x_5674_,
                    v___x_5675_,
                    v___x_5667_,
                );
                return v___x_5676_;
            }
        } else {
            let mut v___x_5677_: usize = 0;
            let mut v___x_5678_: usize = 0;
            let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_5661_);
            v___x_5677_ = 0usize;
            v___x_5678_ = lean_usize_of_nat(v___x_5666_);
            v___x_5679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_5662_,
                v___f_5663_,
                v_args_5660_,
                v___x_5677_,
                v___x_5678_,
                v___x_5667_,
            );
            return v___x_5679_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(
    mut v_inst_5680_: *mut LeanObject,
    mut v_f_5681_: *mut LeanObject,
    mut v_x_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    v___x_5684_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_5680_, v_f_5681_, v___y_5683_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(
    mut v_inst_5685_: *mut LeanObject,
    mut v_f_5686_: *mut LeanObject,
    mut v_y_5687_: *mut LeanObject,
    mut v_toBind_5688_: *mut LeanObject,
    mut v___f_5689_: *mut LeanObject,
    mut v_____r_5690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_5685_, v_f_5686_, v_y_5687_);
    v___x_5692_ = lean_apply_4(
        v_toBind_5688_,
        lean_box(0),
        lean_box(0),
        v___x_5691_,
        v___f_5689_,
    );
    return v___x_5692_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(
    mut v_f_5693_: *mut LeanObject,
    mut v_y_5694_: *mut LeanObject,
    mut v_toBind_5695_: *mut LeanObject,
    mut v___f_5696_: *mut LeanObject,
    mut v_____r_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    v___x_5698_ = lean_apply_1(v_f_5693_, v_y_5694_);
    v___x_5699_ = lean_apply_4(
        v_toBind_5695_,
        lean_box(0),
        lean_box(0),
        v___x_5698_,
        v___f_5696_,
    );
    return v___x_5699_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(
    mut v_f_5700_: *mut LeanObject,
    mut v_discr_5701_: *mut LeanObject,
    mut v_toBind_5702_: *mut LeanObject,
    mut v___f_5703_: *mut LeanObject,
    mut v_____r_5704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    v___x_5705_ = lean_apply_1(v_f_5700_, v_discr_5701_);
    v___x_5706_ = lean_apply_4(
        v_toBind_5702_,
        lean_box(0),
        lean_box(0),
        v___x_5705_,
        v___f_5703_,
    );
    return v___x_5706_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(
    mut v_alts_5707_: *mut LeanObject,
    mut v_toApplicative_5708_: *mut LeanObject,
    mut v_inst_5709_: *mut LeanObject,
    mut v___f_5710_: *mut LeanObject,
    mut v_____r_5711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: u8 = 0;
    v___x_5712_ = lean_unsigned_to_nat(0);
    v___x_5713_ = lean_array_get_size(v_alts_5707_);
    v___x_5714_ = lean_box(0);
    v___x_5715_ = lean_nat_dec_lt(v___x_5712_, v___x_5713_);
    if v___x_5715_ == 0 {
        let mut v_toPure_5716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_5710_);
        lean_dec_ref(v_inst_5709_);
        lean_dec_ref(v_alts_5707_);
        v_toPure_5716_ = lean_ctor_get(v_toApplicative_5708_, 1);
        lean_inc(v_toPure_5716_);
        lean_dec_ref(v_toApplicative_5708_);
        v___x_5717_ = lean_apply_2(v_toPure_5716_, lean_box(0), v___x_5714_);
        return v___x_5717_;
    } else {
        let mut v___x_5718_: u8 = 0;
        v___x_5718_ = lean_nat_dec_le(v___x_5713_, v___x_5713_);
        if v___x_5718_ == 0 {
            if v___x_5715_ == 0 {
                let mut v_toPure_5719_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_5710_);
                lean_dec_ref(v_inst_5709_);
                lean_dec_ref(v_alts_5707_);
                v_toPure_5719_ = lean_ctor_get(v_toApplicative_5708_, 1);
                lean_inc(v_toPure_5719_);
                lean_dec_ref(v_toApplicative_5708_);
                v___x_5720_ = lean_apply_2(v_toPure_5719_, lean_box(0), v___x_5714_);
                return v___x_5720_;
            } else {
                let mut v___x_5721_: usize = 0;
                let mut v___x_5722_: usize = 0;
                let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_5708_);
                v___x_5721_ = 0usize;
                v___x_5722_ = lean_usize_of_nat(v___x_5713_);
                v___x_5723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_5709_,
                    v___f_5710_,
                    v_alts_5707_,
                    v___x_5721_,
                    v___x_5722_,
                    v___x_5714_,
                );
                return v___x_5723_;
            }
        } else {
            let mut v___x_5724_: usize = 0;
            let mut v___x_5725_: usize = 0;
            let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_5708_);
            v___x_5724_ = 0usize;
            v___x_5725_ = lean_usize_of_nat(v___x_5713_);
            v___x_5726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_5709_,
                v___f_5710_,
                v_alts_5707_,
                v___x_5724_,
                v___x_5725_,
                v___x_5714_,
            );
            return v___x_5726_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(
    mut v_inst_5727_: *mut LeanObject,
    mut v_f_5728_: *mut LeanObject,
    mut v_x_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    v___x_5731_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_5727_, v_f_5728_, v___y_5730_);
    return v___x_5731_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(
    mut v_inst_5732_: *mut LeanObject,
    mut v_f_5733_: *mut LeanObject,
    mut v_x_5734_: *mut LeanObject,
    mut v___y_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    v___x_5736_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_5736_, 0, v_inst_5732_);
    lean_closure_set(v___x_5736_, 1, v_f_5733_);
    v___x_5737_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_5735_, v___x_5736_);
    return v___x_5737_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(
    mut v_inst_5738_: *mut LeanObject,
    mut v_f_5739_: *mut LeanObject,
    mut v_value_5740_: *mut LeanObject,
    mut v_toBind_5741_: *mut LeanObject,
    mut v___f_5742_: *mut LeanObject,
    mut v_____r_5743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    v___x_5744_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5738_, v_f_5739_, v_value_5740_);
    v___x_5745_ = lean_apply_4(
        v_toBind_5741_,
        lean_box(0),
        lean_box(0),
        v___x_5744_,
        v___f_5742_,
    );
    return v___x_5745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg(
    mut v_inst_5746_: *mut LeanObject,
    mut v_f_5747_: *mut LeanObject,
    mut v_c_5748_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_c_5748_) {
        0 => {
            let mut v_toBind_5749_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_5750_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5751_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5752_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5749_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5749_);
            v_decl_5750_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc_ref(v_decl_5750_);
            v_k_5751_ = lean_ctor_get(v_c_5748_, 1);
            lean_inc_ref(v_k_5751_);
            lean_dec_ref_known(v_c_5748_, 2);
            lean_inc(v_f_5747_);
            lean_inc_ref(v_inst_5746_);
            v___f_5752_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5752_, 0, v_inst_5746_);
            lean_closure_set(v___f_5752_, 1, v_f_5747_);
            lean_closure_set(v___f_5752_, 2, v_k_5751_);
            v___x_5753_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
                v_inst_5746_,
                v_f_5747_,
                v_decl_5750_,
            );
            v___x_5754_ = lean_apply_4(
                v_toBind_5749_,
                lean_box(0),
                lean_box(0),
                v___x_5753_,
                v___f_5752_,
            );
            return v___x_5754_;
        }
        3 => {
            let mut v_toApplicative_5755_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5756_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5757_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_5758_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5759_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5760_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_5755_ = lean_ctor_get(v_inst_5746_, 0);
            lean_inc_ref(v_toApplicative_5755_);
            v_toBind_5756_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5756_);
            v_fvarId_5757_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5757_);
            v_args_5758_ = lean_ctor_get(v_c_5748_, 1);
            lean_inc_ref(v_args_5758_);
            lean_dec_ref_known(v_c_5748_, 2);
            lean_inc(v_f_5747_);
            lean_inc_ref(v_inst_5746_);
            v___f_5759_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8 as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_5759_, 0, v_inst_5746_);
            lean_closure_set(v___f_5759_, 1, v_f_5747_);
            v___f_5760_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5760_, 0, v_args_5758_);
            lean_closure_set(v___f_5760_, 1, v_toApplicative_5755_);
            lean_closure_set(v___f_5760_, 2, v_inst_5746_);
            lean_closure_set(v___f_5760_, 3, v___f_5759_);
            v___x_5761_ = lean_apply_1(v_f_5747_, v_fvarId_5757_);
            v___x_5762_ = lean_apply_4(
                v_toBind_5756_,
                lean_box(0),
                lean_box(0),
                v___x_5761_,
                v___f_5760_,
            );
            return v___x_5762_;
        }
        4 => {
            let mut v_cases_5763_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_5764_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5765_: *mut LeanObject = core::ptr::null_mut();
            let mut v_resultType_5766_: *mut LeanObject = core::ptr::null_mut();
            let mut v_discr_5767_: *mut LeanObject = core::ptr::null_mut();
            let mut v_alts_5768_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5769_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5771_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
            v_cases_5763_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc_ref(v_cases_5763_);
            lean_dec_ref_known(v_c_5748_, 1);
            v_toApplicative_5764_ = lean_ctor_get(v_inst_5746_, 0);
            v_toBind_5765_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc_n(v_toBind_5765_, 2);
            v_resultType_5766_ = lean_ctor_get(v_cases_5763_, 1);
            lean_inc_ref(v_resultType_5766_);
            v_discr_5767_ = lean_ctor_get(v_cases_5763_, 2);
            lean_inc(v_discr_5767_);
            v_alts_5768_ = lean_ctor_get(v_cases_5763_, 3);
            lean_inc_ref(v_alts_5768_);
            lean_dec_ref(v_cases_5763_);
            lean_inc_n(v_f_5747_, 2);
            lean_inc_ref_n(v_inst_5746_, 2);
            v___f_5769_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5 as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_5769_, 0, v_inst_5746_);
            lean_closure_set(v___f_5769_, 1, v_f_5747_);
            lean_inc_ref(v_toApplicative_5764_);
            v___f_5770_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5770_, 0, v_alts_5768_);
            lean_closure_set(v___f_5770_, 1, v_toApplicative_5764_);
            lean_closure_set(v___f_5770_, 2, v_inst_5746_);
            lean_closure_set(v___f_5770_, 3, v___f_5769_);
            v___f_5771_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5771_, 0, v_f_5747_);
            lean_closure_set(v___f_5771_, 1, v_discr_5767_);
            lean_closure_set(v___f_5771_, 2, v_toBind_5765_);
            lean_closure_set(v___f_5771_, 3, v___f_5770_);
            v___x_5772_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                v_inst_5746_,
                v_f_5747_,
                v_resultType_5766_,
            );
            v___x_5773_ = lean_apply_4(
                v_toBind_5765_,
                lean_box(0),
                lean_box(0),
                v___x_5772_,
                v___f_5771_,
            );
            return v___x_5773_;
        }
        5 => {
            let mut v_fvarId_5774_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_5746_);
            v_fvarId_5774_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5774_);
            lean_dec_ref_known(v_c_5748_, 1);
            v___x_5775_ = lean_apply_1(v_f_5747_, v_fvarId_5774_);
            return v___x_5775_;
        }
        6 => {
            let mut v_type_5776_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
            v_type_5776_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc_ref(v_type_5776_);
            lean_dec_ref_known(v_c_5748_, 1);
            v___x_5777_ =
                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5746_, v_f_5747_, v_type_5776_);
            return v___x_5777_;
        }
        7 => {
            let mut v_toBind_5778_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5779_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5780_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5782_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5783_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5778_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc_n(v_toBind_5778_, 2);
            v_fvarId_5779_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5779_);
            v_y_5780_ = lean_ctor_get(v_c_5748_, 2);
            lean_inc(v_y_5780_);
            v_k_5781_ = lean_ctor_get(v_c_5748_, 3);
            lean_inc_ref(v_k_5781_);
            lean_dec_ref_known(v_c_5748_, 4);
            lean_inc_n(v_f_5747_, 2);
            lean_inc_ref(v_inst_5746_);
            v___f_5782_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5782_, 0, v_inst_5746_);
            lean_closure_set(v___f_5782_, 1, v_f_5747_);
            lean_closure_set(v___f_5782_, 2, v_k_5781_);
            v___f_5783_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_5783_, 0, v_inst_5746_);
            lean_closure_set(v___f_5783_, 1, v_f_5747_);
            lean_closure_set(v___f_5783_, 2, v_y_5780_);
            lean_closure_set(v___f_5783_, 3, v_toBind_5778_);
            lean_closure_set(v___f_5783_, 4, v___f_5782_);
            v___x_5784_ = lean_apply_1(v_f_5747_, v_fvarId_5779_);
            v___x_5785_ = lean_apply_4(
                v_toBind_5778_,
                lean_box(0),
                lean_box(0),
                v___x_5784_,
                v___f_5783_,
            );
            return v___x_5785_;
        }
        8 => {
            let mut v_toBind_5786_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5787_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5791_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5786_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc_n(v_toBind_5786_, 2);
            v_fvarId_5787_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5787_);
            v_y_5788_ = lean_ctor_get(v_c_5748_, 2);
            lean_inc(v_y_5788_);
            v_k_5789_ = lean_ctor_get(v_c_5748_, 3);
            lean_inc_ref(v_k_5789_);
            lean_dec_ref_known(v_c_5748_, 4);
            lean_inc_n(v_f_5747_, 2);
            v___f_5790_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5790_, 0, v_inst_5746_);
            lean_closure_set(v___f_5790_, 1, v_f_5747_);
            lean_closure_set(v___f_5790_, 2, v_k_5789_);
            v___f_5791_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5791_, 0, v_f_5747_);
            lean_closure_set(v___f_5791_, 1, v_y_5788_);
            lean_closure_set(v___f_5791_, 2, v_toBind_5786_);
            lean_closure_set(v___f_5791_, 3, v___f_5790_);
            v___x_5792_ = lean_apply_1(v_f_5747_, v_fvarId_5787_);
            v___x_5793_ = lean_apply_4(
                v_toBind_5786_,
                lean_box(0),
                lean_box(0),
                v___x_5792_,
                v___f_5791_,
            );
            return v___x_5793_;
        }
        9 => {
            let mut v_toBind_5794_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5795_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5796_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_5797_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5798_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5799_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5800_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5801_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5794_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc_n(v_toBind_5794_, 3);
            v_fvarId_5795_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5795_);
            v_y_5796_ = lean_ctor_get(v_c_5748_, 3);
            lean_inc(v_y_5796_);
            v_ty_5797_ = lean_ctor_get(v_c_5748_, 4);
            lean_inc_ref(v_ty_5797_);
            v_k_5798_ = lean_ctor_get(v_c_5748_, 5);
            lean_inc_ref(v_k_5798_);
            lean_dec_ref_known(v_c_5748_, 6);
            lean_inc_n(v_f_5747_, 3);
            lean_inc_ref(v_inst_5746_);
            v___f_5799_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5799_, 0, v_inst_5746_);
            lean_closure_set(v___f_5799_, 1, v_f_5747_);
            lean_closure_set(v___f_5799_, 2, v_k_5798_);
            v___f_5800_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_5800_, 0, v_inst_5746_);
            lean_closure_set(v___f_5800_, 1, v_f_5747_);
            lean_closure_set(v___f_5800_, 2, v_ty_5797_);
            lean_closure_set(v___f_5800_, 3, v_toBind_5794_);
            lean_closure_set(v___f_5800_, 4, v___f_5799_);
            v___f_5801_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_5801_, 0, v_f_5747_);
            lean_closure_set(v___f_5801_, 1, v_y_5796_);
            lean_closure_set(v___f_5801_, 2, v_toBind_5794_);
            lean_closure_set(v___f_5801_, 3, v___f_5800_);
            v___x_5802_ = lean_apply_1(v_f_5747_, v_fvarId_5795_);
            v___x_5803_ = lean_apply_4(
                v_toBind_5794_,
                lean_box(0),
                lean_box(0),
                v___x_5802_,
                v___f_5801_,
            );
            return v___x_5803_;
        }
        10 => {
            let mut v_toBind_5804_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5805_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5806_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5807_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5804_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5804_);
            v_fvarId_5805_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5805_);
            v_k_5806_ = lean_ctor_get(v_c_5748_, 2);
            lean_inc_ref(v_k_5806_);
            lean_dec_ref_known(v_c_5748_, 3);
            lean_inc(v_f_5747_);
            v___f_5807_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5807_, 0, v_inst_5746_);
            lean_closure_set(v___f_5807_, 1, v_f_5747_);
            lean_closure_set(v___f_5807_, 2, v_k_5806_);
            v___x_5808_ = lean_apply_1(v_f_5747_, v_fvarId_5805_);
            v___x_5809_ = lean_apply_4(
                v_toBind_5804_,
                lean_box(0),
                lean_box(0),
                v___x_5808_,
                v___f_5807_,
            );
            return v___x_5809_;
        }
        11 => {
            let mut v_toBind_5810_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5811_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5812_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5813_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5810_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5810_);
            v_fvarId_5811_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5811_);
            v_k_5812_ = lean_ctor_get(v_c_5748_, 2);
            lean_inc_ref(v_k_5812_);
            lean_dec_ref_known(v_c_5748_, 3);
            lean_inc(v_f_5747_);
            v___f_5813_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5813_, 0, v_inst_5746_);
            lean_closure_set(v___f_5813_, 1, v_f_5747_);
            lean_closure_set(v___f_5813_, 2, v_k_5812_);
            v___x_5814_ = lean_apply_1(v_f_5747_, v_fvarId_5811_);
            v___x_5815_ = lean_apply_4(
                v_toBind_5810_,
                lean_box(0),
                lean_box(0),
                v___x_5814_,
                v___f_5813_,
            );
            return v___x_5815_;
        }
        12 => {
            let mut v_toBind_5816_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5817_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5818_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5816_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5816_);
            v_fvarId_5817_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5817_);
            v_k_5818_ = lean_ctor_get(v_c_5748_, 3);
            lean_inc_ref(v_k_5818_);
            lean_dec_ref_known(v_c_5748_, 4);
            lean_inc(v_f_5747_);
            v___f_5819_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5819_, 0, v_inst_5746_);
            lean_closure_set(v___f_5819_, 1, v_f_5747_);
            lean_closure_set(v___f_5819_, 2, v_k_5818_);
            v___x_5820_ = lean_apply_1(v_f_5747_, v_fvarId_5817_);
            v___x_5821_ = lean_apply_4(
                v_toBind_5816_,
                lean_box(0),
                lean_box(0),
                v___x_5820_,
                v___f_5819_,
            );
            return v___x_5821_;
        }
        13 => {
            let mut v_toBind_5822_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5823_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5822_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc(v_toBind_5822_);
            v_fvarId_5823_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc(v_fvarId_5823_);
            v_k_5824_ = lean_ctor_get(v_c_5748_, 1);
            lean_inc_ref(v_k_5824_);
            lean_dec_ref_known(v_c_5748_, 2);
            lean_inc(v_f_5747_);
            v___f_5825_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5825_, 0, v_inst_5746_);
            lean_closure_set(v___f_5825_, 1, v_f_5747_);
            lean_closure_set(v___f_5825_, 2, v_k_5824_);
            v___x_5826_ = lean_apply_1(v_f_5747_, v_fvarId_5823_);
            v___x_5827_ = lean_apply_4(
                v_toBind_5822_,
                lean_box(0),
                lean_box(0),
                v___x_5826_,
                v___f_5825_,
            );
            return v___x_5827_;
        }
        _ => {
            let mut v_decl_5828_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_5829_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_5830_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5831_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_5832_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_5833_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_5834_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5835_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5836_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5837_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5841_: u8 = 0;
            v_decl_5828_ = lean_ctor_get(v_c_5748_, 0);
            lean_inc_ref(v_decl_5828_);
            v_toApplicative_5829_ = lean_ctor_get(v_inst_5746_, 0);
            v_toBind_5830_ = lean_ctor_get(v_inst_5746_, 1);
            lean_inc_n(v_toBind_5830_, 3);
            v_k_5831_ = lean_ctor_get(v_c_5748_, 1);
            lean_inc_ref(v_k_5831_);
            lean_dec_ref(v_c_5748_);
            v_params_5832_ = lean_ctor_get(v_decl_5828_, 2);
            lean_inc_ref(v_params_5832_);
            v_type_5833_ = lean_ctor_get(v_decl_5828_, 3);
            lean_inc_ref(v_type_5833_);
            v_value_5834_ = lean_ctor_get(v_decl_5828_, 4);
            lean_inc_ref(v_value_5834_);
            lean_dec_ref(v_decl_5828_);
            lean_inc_n(v_f_5747_, 3);
            lean_inc_ref_n(v_inst_5746_, 3);
            v___f_5835_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5835_, 0, v_inst_5746_);
            lean_closure_set(v___f_5835_, 1, v_f_5747_);
            lean_closure_set(v___f_5835_, 2, v_k_5831_);
            v___f_5836_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_5836_, 0, v_inst_5746_);
            lean_closure_set(v___f_5836_, 1, v_f_5747_);
            lean_closure_set(v___f_5836_, 2, v_value_5834_);
            lean_closure_set(v___f_5836_, 3, v_toBind_5830_);
            lean_closure_set(v___f_5836_, 4, v___f_5835_);
            v___f_5837_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_5837_, 0, v_inst_5746_);
            lean_closure_set(v___f_5837_, 1, v_f_5747_);
            lean_closure_set(v___f_5837_, 2, v_type_5833_);
            lean_closure_set(v___f_5837_, 3, v_toBind_5830_);
            lean_closure_set(v___f_5837_, 4, v___f_5836_);
            v___x_5838_ = lean_unsigned_to_nat(0);
            v___x_5839_ = lean_array_get_size(v_params_5832_);
            v___x_5840_ = lean_box(0);
            v___x_5841_ = lean_nat_dec_lt(v___x_5838_, v___x_5839_);
            if v___x_5841_ == 0 {
                let mut v_toPure_5842_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_5829_);
                lean_dec_ref(v_params_5832_);
                lean_dec(v_f_5747_);
                lean_dec_ref(v_inst_5746_);
                v_toPure_5842_ = lean_ctor_get(v_toApplicative_5829_, 1);
                lean_inc(v_toPure_5842_);
                lean_dec_ref(v_toApplicative_5829_);
                v___x_5843_ = lean_apply_2(v_toPure_5842_, lean_box(0), v___x_5840_);
                v___x_5844_ = lean_apply_4(
                    v_toBind_5830_,
                    lean_box(0),
                    lean_box(0),
                    v___x_5843_,
                    v___f_5837_,
                );
                return v___x_5844_;
            } else {
                let mut v___f_5845_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5846_: u8 = 0;
                lean_inc_ref(v_inst_5746_);
                v___f_5845_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_5845_, 0, v_inst_5746_);
                lean_closure_set(v___f_5845_, 1, v_f_5747_);
                v___x_5846_ = lean_nat_dec_le(v___x_5839_, v___x_5839_);
                if v___x_5846_ == 0 {
                    if v___x_5841_ == 0 {
                        let mut v_toPure_5847_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
                        lean_inc_ref(v_toApplicative_5829_);
                        lean_dec_ref(v___f_5845_);
                        lean_dec_ref(v_params_5832_);
                        lean_dec_ref(v_inst_5746_);
                        v_toPure_5847_ = lean_ctor_get(v_toApplicative_5829_, 1);
                        lean_inc(v_toPure_5847_);
                        lean_dec_ref(v_toApplicative_5829_);
                        v___x_5848_ = lean_apply_2(v_toPure_5847_, lean_box(0), v___x_5840_);
                        v___x_5849_ = lean_apply_4(
                            v_toBind_5830_,
                            lean_box(0),
                            lean_box(0),
                            v___x_5848_,
                            v___f_5837_,
                        );
                        return v___x_5849_;
                    } else {
                        let mut v___x_5850_: usize = 0;
                        let mut v___x_5851_: usize = 0;
                        let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5850_ = 0usize;
                        v___x_5851_ = lean_usize_of_nat(v___x_5839_);
                        v___x_5852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_5746_,
                            v___f_5845_,
                            v_params_5832_,
                            v___x_5850_,
                            v___x_5851_,
                            v___x_5840_,
                        );
                        v___x_5853_ = lean_apply_4(
                            v_toBind_5830_,
                            lean_box(0),
                            lean_box(0),
                            v___x_5852_,
                            v___f_5837_,
                        );
                        return v___x_5853_;
                    }
                } else {
                    let mut v___x_5854_: usize = 0;
                    let mut v___x_5855_: usize = 0;
                    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5854_ = 0usize;
                    v___x_5855_ = lean_usize_of_nat(v___x_5839_);
                    v___x_5856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_5746_,
                        v___f_5845_,
                        v_params_5832_,
                        v___x_5854_,
                        v___x_5855_,
                        v___x_5840_,
                    );
                    v___x_5857_ = lean_apply_4(
                        v_toBind_5830_,
                        lean_box(0),
                        lean_box(0),
                        v___x_5856_,
                        v___f_5837_,
                    );
                    return v___x_5857_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(
    mut v_inst_5858_: *mut LeanObject,
    mut v_f_5859_: *mut LeanObject,
    mut v_k_5860_: *mut LeanObject,
    mut v_____r_5861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    v___x_5862_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5858_, v_f_5859_, v_k_5860_);
    return v___x_5862_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM(
    mut v_m_5863_: *mut LeanObject,
    mut v_pu_5864_: u8,
    mut v_inst_5865_: *mut LeanObject,
    mut v_f_5866_: *mut LeanObject,
    mut v_c_5867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    v___x_5868_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5865_, v_f_5866_, v_c_5867_);
    return v___x_5868_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___boxed(
    mut v_m_5869_: *mut LeanObject,
    mut v_pu_5870_: *mut LeanObject,
    mut v_inst_5871_: *mut LeanObject,
    mut v_f_5872_: *mut LeanObject,
    mut v_c_5873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5874_: u8 = 0;
    let mut v_res_5875_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5874_ = (lean_unbox(v_pu_5870_) as u8);
    v_res_5875_ = l_Lean_Compiler_LCNF_Code_forFVarM(
        v_m_5869_,
        v_pu_boxed_5874_,
        v_inst_5871_,
        v_f_5872_,
        v_c_5873_,
    );
    return v_res_5875_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(
    mut v_pu_5876_: u8,
    mut v_m_5877_: *mut LeanObject,
    mut v_inst_5878_: *mut LeanObject,
    mut v_inst_5879_: *mut LeanObject,
    mut v___y_5880_: *mut LeanObject,
    mut v___y_5881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    v___x_5882_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5876_,
        v_inst_5878_,
        v_inst_5879_,
        v___y_5880_,
        v___y_5881_,
    );
    return v___x_5882_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(
    mut v_pu_5883_: *mut LeanObject,
    mut v_m_5884_: *mut LeanObject,
    mut v_inst_5885_: *mut LeanObject,
    mut v_inst_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5889_: u8 = 0;
    let mut v_res_5890_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5889_ = (lean_unbox(v_pu_5883_) as u8);
    v_res_5890_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(
        v_pu_boxed_5889_,
        v_m_5884_,
        v_inst_5885_,
        v_inst_5886_,
        v___y_5887_,
        v___y_5888_,
    );
    return v_res_5890_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(
    mut v_m_5891_: *mut LeanObject,
    mut v_inst_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    v___x_5895_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5892_, v___y_5893_, v___y_5894_);
    return v___x_5895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode(mut v_pu_5897_: u8) -> *mut LeanObject {
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    v___x_5898_ = lean_box((v_pu_5897_) as usize);
    v___f_5899_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5899_, 0, v___x_5898_);
    v___f_5900_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0;
    v___x_5901_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5901_, 0, v___f_5899_);
    lean_ctor_set(v___x_5901_, 1, v___f_5900_);
    return v___x_5901_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(
    mut v_pu_5902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5903_: u8 = 0;
    let mut v_res_5904_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5903_ = (lean_unbox(v_pu_5902_) as u8);
    v_res_5904_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_5903_);
    return v_res_5904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(
    mut v_pu_5905_: u8,
    mut v_decl_5906_: *mut LeanObject,
    mut v_____do__lift_5907_: *mut LeanObject,
    mut v_params_5908_: *mut LeanObject,
    mut v_inst_5909_: *mut LeanObject,
    mut v_____do__lift_5910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    v___x_5911_ = lean_box((v_pu_5905_) as usize);
    v___x_5912_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___x_5912_, 0, v___x_5911_);
    lean_closure_set(v___x_5912_, 1, v_decl_5906_);
    lean_closure_set(v___x_5912_, 2, v_____do__lift_5907_);
    lean_closure_set(v___x_5912_, 3, v_params_5908_);
    lean_closure_set(v___x_5912_, 4, v_____do__lift_5910_);
    v___x_5913_ = lean_apply_2(v_inst_5909_, lean_box(0), v___x_5912_);
    return v___x_5913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_5914_: *mut LeanObject,
    mut v_decl_5915_: *mut LeanObject,
    mut v_____do__lift_5916_: *mut LeanObject,
    mut v_params_5917_: *mut LeanObject,
    mut v_inst_5918_: *mut LeanObject,
    mut v_____do__lift_5919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5920_: u8 = 0;
    let mut v_res_5921_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5920_ = (lean_unbox(v_pu_5914_) as u8);
    v_res_5921_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(
        v_pu_boxed_5920_,
        v_decl_5915_,
        v_____do__lift_5916_,
        v_params_5917_,
        v_inst_5918_,
        v_____do__lift_5919_,
    );
    return v_res_5921_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(
    mut v_pu_5922_: u8,
    mut v_decl_5923_: *mut LeanObject,
    mut v_params_5924_: *mut LeanObject,
    mut v_inst_5925_: *mut LeanObject,
    mut v_inst_5926_: *mut LeanObject,
    mut v_f_5927_: *mut LeanObject,
    mut v_value_5928_: *mut LeanObject,
    mut v_toBind_5929_: *mut LeanObject,
    mut v_____do__lift_5930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    v___x_5931_ = lean_box((v_pu_5922_) as usize);
    lean_inc(v_inst_5925_);
    v___f_5932_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5932_, 0, v___x_5931_);
    lean_closure_set(v___f_5932_, 1, v_decl_5923_);
    lean_closure_set(v___f_5932_, 2, v_____do__lift_5930_);
    lean_closure_set(v___f_5932_, 3, v_params_5924_);
    lean_closure_set(v___f_5932_, 4, v_inst_5925_);
    v___x_5933_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5922_,
        v_inst_5925_,
        v_inst_5926_,
        v_f_5927_,
        v_value_5928_,
    );
    v___x_5934_ = lean_apply_4(
        v_toBind_5929_,
        lean_box(0),
        lean_box(0),
        v___x_5933_,
        v___f_5932_,
    );
    return v___x_5934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_5935_: *mut LeanObject,
    mut v_decl_5936_: *mut LeanObject,
    mut v_params_5937_: *mut LeanObject,
    mut v_inst_5938_: *mut LeanObject,
    mut v_inst_5939_: *mut LeanObject,
    mut v_f_5940_: *mut LeanObject,
    mut v_value_5941_: *mut LeanObject,
    mut v_toBind_5942_: *mut LeanObject,
    mut v_____do__lift_5943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5944_: u8 = 0;
    let mut v_res_5945_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5944_ = (lean_unbox(v_pu_5935_) as u8);
    v_res_5945_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(
        v_pu_boxed_5944_,
        v_decl_5936_,
        v_params_5937_,
        v_inst_5938_,
        v_inst_5939_,
        v_f_5940_,
        v_value_5941_,
        v_toBind_5942_,
        v_____do__lift_5943_,
    );
    return v_res_5945_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(
    mut v_pu_5946_: u8,
    mut v_decl_5947_: *mut LeanObject,
    mut v_inst_5948_: *mut LeanObject,
    mut v_inst_5949_: *mut LeanObject,
    mut v_f_5950_: *mut LeanObject,
    mut v_value_5951_: *mut LeanObject,
    mut v_toBind_5952_: *mut LeanObject,
    mut v_type_5953_: *mut LeanObject,
    mut v_params_5954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    v___x_5955_ = lean_box((v_pu_5946_) as usize);
    lean_inc(v_toBind_5952_);
    lean_inc(v_f_5950_);
    lean_inc_ref(v_inst_5949_);
    v___f_5956_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5956_, 0, v___x_5955_);
    lean_closure_set(v___f_5956_, 1, v_decl_5947_);
    lean_closure_set(v___f_5956_, 2, v_params_5954_);
    lean_closure_set(v___f_5956_, 3, v_inst_5948_);
    lean_closure_set(v___f_5956_, 4, v_inst_5949_);
    lean_closure_set(v___f_5956_, 5, v_f_5950_);
    lean_closure_set(v___f_5956_, 6, v_value_5951_);
    lean_closure_set(v___f_5956_, 7, v_toBind_5952_);
    v___x_5957_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5949_, v_f_5950_, v_type_5953_);
    v___x_5958_ = lean_apply_4(
        v_toBind_5952_,
        lean_box(0),
        lean_box(0),
        v___x_5957_,
        v___f_5956_,
    );
    return v___x_5958_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(
    mut v_pu_5959_: *mut LeanObject,
    mut v_decl_5960_: *mut LeanObject,
    mut v_inst_5961_: *mut LeanObject,
    mut v_inst_5962_: *mut LeanObject,
    mut v_f_5963_: *mut LeanObject,
    mut v_value_5964_: *mut LeanObject,
    mut v_toBind_5965_: *mut LeanObject,
    mut v_type_5966_: *mut LeanObject,
    mut v_params_5967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5968_: u8 = 0;
    let mut v_res_5969_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5968_ = (lean_unbox(v_pu_5959_) as u8);
    v_res_5969_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(
        v_pu_boxed_5968_,
        v_decl_5960_,
        v_inst_5961_,
        v_inst_5962_,
        v_f_5963_,
        v_value_5964_,
        v_toBind_5965_,
        v_type_5966_,
        v_params_5967_,
    );
    return v_res_5969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
    mut v_pu_5970_: u8,
    mut v_inst_5971_: *mut LeanObject,
    mut v_inst_5972_: *mut LeanObject,
    mut v_f_5973_: *mut LeanObject,
    mut v_decl_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5983_: usize = 0;
    let mut v___x_5984_: usize = 0;
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_5975_ = lean_ctor_get(v_inst_5972_, 1);
    lean_inc_n(v_toBind_5975_, 2);
    v_params_5976_ = lean_ctor_get(v_decl_5974_, 2);
    lean_inc_ref(v_params_5976_);
    v_type_5977_ = lean_ctor_get(v_decl_5974_, 3);
    lean_inc_ref(v_type_5977_);
    v_value_5978_ = lean_ctor_get(v_decl_5974_, 4);
    lean_inc_ref(v_value_5978_);
    v___x_5979_ = lean_box((v_pu_5970_) as usize);
    lean_inc(v_f_5973_);
    lean_inc_ref_n(v_inst_5972_, 2);
    lean_inc(v_inst_5971_);
    v___f_5980_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5980_, 0, v___x_5979_);
    lean_closure_set(v___f_5980_, 1, v_decl_5974_);
    lean_closure_set(v___f_5980_, 2, v_inst_5971_);
    lean_closure_set(v___f_5980_, 3, v_inst_5972_);
    lean_closure_set(v___f_5980_, 4, v_f_5973_);
    lean_closure_set(v___f_5980_, 5, v_value_5978_);
    lean_closure_set(v___f_5980_, 6, v_toBind_5975_);
    lean_closure_set(v___f_5980_, 7, v_type_5977_);
    v___x_5981_ = lean_box((v_pu_5970_) as usize);
    v___x_5982_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_5982_, 0, lean_box(0));
    lean_closure_set(v___x_5982_, 1, v___x_5981_);
    lean_closure_set(v___x_5982_, 2, v_inst_5971_);
    lean_closure_set(v___x_5982_, 3, v_inst_5972_);
    lean_closure_set(v___x_5982_, 4, v_f_5973_);
    v_sz_5983_ = lean_array_size(v_params_5976_);
    v___x_5984_ = 0usize;
    v___x_5985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5972_,
        v___x_5982_,
        v_sz_5983_,
        v___x_5984_,
        v_params_5976_,
    );
    v___x_5986_ = lean_apply_4(
        v_toBind_5975_,
        lean_box(0),
        lean_box(0),
        v___x_5985_,
        v___f_5980_,
    );
    return v___x_5986_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(
    mut v_pu_5987_: *mut LeanObject,
    mut v_inst_5988_: *mut LeanObject,
    mut v_inst_5989_: *mut LeanObject,
    mut v_f_5990_: *mut LeanObject,
    mut v_decl_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5992_: u8 = 0;
    let mut v_res_5993_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5992_ = (lean_unbox(v_pu_5987_) as u8);
    v_res_5993_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_boxed_5992_,
        v_inst_5988_,
        v_inst_5989_,
        v_f_5990_,
        v_decl_5991_,
    );
    return v_res_5993_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM(
    mut v_m_5994_: *mut LeanObject,
    mut v_pu_5995_: u8,
    mut v_inst_5996_: *mut LeanObject,
    mut v_inst_5997_: *mut LeanObject,
    mut v_f_5998_: *mut LeanObject,
    mut v_decl_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    v___x_6000_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_5995_,
        v_inst_5996_,
        v_inst_5997_,
        v_f_5998_,
        v_decl_5999_,
    );
    return v___x_6000_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(
    mut v_m_6001_: *mut LeanObject,
    mut v_pu_6002_: *mut LeanObject,
    mut v_inst_6003_: *mut LeanObject,
    mut v_inst_6004_: *mut LeanObject,
    mut v_f_6005_: *mut LeanObject,
    mut v_decl_6006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6007_: u8 = 0;
    let mut v_res_6008_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6007_ = (lean_unbox(v_pu_6002_) as u8);
    v_res_6008_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(
        v_m_6001_,
        v_pu_boxed_6007_,
        v_inst_6003_,
        v_inst_6004_,
        v_f_6005_,
        v_decl_6006_,
    );
    return v_res_6008_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(
    mut v_inst_6009_: *mut LeanObject,
    mut v_f_6010_: *mut LeanObject,
    mut v_value_6011_: *mut LeanObject,
    mut v_____r_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    v___x_6013_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6009_, v_f_6010_, v_value_6011_);
    return v___x_6013_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(
    mut v_inst_6014_: *mut LeanObject,
    mut v_f_6015_: *mut LeanObject,
    mut v_type_6016_: *mut LeanObject,
    mut v_toBind_6017_: *mut LeanObject,
    mut v___f_6018_: *mut LeanObject,
    mut v_____r_6019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    v___x_6020_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_6014_, v_f_6015_, v_type_6016_);
    v___x_6021_ = lean_apply_4(
        v_toBind_6017_,
        lean_box(0),
        lean_box(0),
        v___x_6020_,
        v___f_6018_,
    );
    return v___x_6021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(
    mut v_inst_6022_: *mut LeanObject,
    mut v_f_6023_: *mut LeanObject,
    mut v_x_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    v___x_6026_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_6022_, v_f_6023_, v___y_6025_);
    return v___x_6026_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
    mut v_inst_6027_: *mut LeanObject,
    mut v_f_6028_: *mut LeanObject,
    mut v_decl_6029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: u8 = 0;
    v_toApplicative_6030_ = lean_ctor_get(v_inst_6027_, 0);
    v_toBind_6031_ = lean_ctor_get(v_inst_6027_, 1);
    lean_inc_n(v_toBind_6031_, 2);
    v_params_6032_ = lean_ctor_get(v_decl_6029_, 2);
    lean_inc_ref(v_params_6032_);
    v_type_6033_ = lean_ctor_get(v_decl_6029_, 3);
    lean_inc_ref(v_type_6033_);
    v_value_6034_ = lean_ctor_get(v_decl_6029_, 4);
    lean_inc_ref(v_value_6034_);
    lean_dec_ref(v_decl_6029_);
    lean_inc_n(v_f_6028_, 2);
    lean_inc_ref_n(v_inst_6027_, 2);
    v___f_6035_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6035_, 0, v_inst_6027_);
    lean_closure_set(v___f_6035_, 1, v_f_6028_);
    lean_closure_set(v___f_6035_, 2, v_value_6034_);
    v___f_6036_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6036_, 0, v_inst_6027_);
    lean_closure_set(v___f_6036_, 1, v_f_6028_);
    lean_closure_set(v___f_6036_, 2, v_type_6033_);
    lean_closure_set(v___f_6036_, 3, v_toBind_6031_);
    lean_closure_set(v___f_6036_, 4, v___f_6035_);
    v___x_6037_ = lean_unsigned_to_nat(0);
    v___x_6038_ = lean_array_get_size(v_params_6032_);
    v___x_6039_ = lean_box(0);
    v___x_6040_ = lean_nat_dec_lt(v___x_6037_, v___x_6038_);
    if v___x_6040_ == 0 {
        let mut v_toPure_6041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_6030_);
        lean_dec_ref(v_params_6032_);
        lean_dec(v_f_6028_);
        lean_dec_ref(v_inst_6027_);
        v_toPure_6041_ = lean_ctor_get(v_toApplicative_6030_, 1);
        lean_inc(v_toPure_6041_);
        lean_dec_ref(v_toApplicative_6030_);
        v___x_6042_ = lean_apply_2(v_toPure_6041_, lean_box(0), v___x_6039_);
        v___x_6043_ = lean_apply_4(
            v_toBind_6031_,
            lean_box(0),
            lean_box(0),
            v___x_6042_,
            v___f_6036_,
        );
        return v___x_6043_;
    } else {
        let mut v___f_6044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6045_: u8 = 0;
        lean_inc_ref(v_inst_6027_);
        v___f_6044_ = lean_alloc_closure(
            l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_6044_, 0, v_inst_6027_);
        lean_closure_set(v___f_6044_, 1, v_f_6028_);
        v___x_6045_ = lean_nat_dec_le(v___x_6038_, v___x_6038_);
        if v___x_6045_ == 0 {
            if v___x_6040_ == 0 {
                let mut v_toPure_6046_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_6030_);
                lean_dec_ref(v___f_6044_);
                lean_dec_ref(v_params_6032_);
                lean_dec_ref(v_inst_6027_);
                v_toPure_6046_ = lean_ctor_get(v_toApplicative_6030_, 1);
                lean_inc(v_toPure_6046_);
                lean_dec_ref(v_toApplicative_6030_);
                v___x_6047_ = lean_apply_2(v_toPure_6046_, lean_box(0), v___x_6039_);
                v___x_6048_ = lean_apply_4(
                    v_toBind_6031_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6047_,
                    v___f_6036_,
                );
                return v___x_6048_;
            } else {
                let mut v___x_6049_: usize = 0;
                let mut v___x_6050_: usize = 0;
                let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
                v___x_6049_ = 0usize;
                v___x_6050_ = lean_usize_of_nat(v___x_6038_);
                v___x_6051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_6027_,
                    v___f_6044_,
                    v_params_6032_,
                    v___x_6049_,
                    v___x_6050_,
                    v___x_6039_,
                );
                v___x_6052_ = lean_apply_4(
                    v_toBind_6031_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6051_,
                    v___f_6036_,
                );
                return v___x_6052_;
            }
        } else {
            let mut v___x_6053_: usize = 0;
            let mut v___x_6054_: usize = 0;
            let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
            v___x_6053_ = 0usize;
            v___x_6054_ = lean_usize_of_nat(v___x_6038_);
            v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_6027_,
                v___f_6044_,
                v_params_6032_,
                v___x_6053_,
                v___x_6054_,
                v___x_6039_,
            );
            v___x_6056_ = lean_apply_4(
                v_toBind_6031_,
                lean_box(0),
                lean_box(0),
                v___x_6055_,
                v___f_6036_,
            );
            return v___x_6056_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM(
    mut v_m_6057_: *mut LeanObject,
    mut v_pu_6058_: u8,
    mut v_inst_6059_: *mut LeanObject,
    mut v_f_6060_: *mut LeanObject,
    mut v_decl_6061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    v___x_6062_ =
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_6059_, v_f_6060_, v_decl_6061_);
    return v___x_6062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(
    mut v_m_6063_: *mut LeanObject,
    mut v_pu_6064_: *mut LeanObject,
    mut v_inst_6065_: *mut LeanObject,
    mut v_f_6066_: *mut LeanObject,
    mut v_decl_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6068_: u8 = 0;
    let mut v_res_6069_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6068_ = (lean_unbox(v_pu_6064_) as u8);
    v_res_6069_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(
        v_m_6063_,
        v_pu_boxed_6068_,
        v_inst_6065_,
        v_f_6066_,
        v_decl_6067_,
    );
    return v_res_6069_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(
    mut v_pu_6070_: u8,
    mut v_m_6071_: *mut LeanObject,
    mut v_inst_6072_: *mut LeanObject,
    mut v_inst_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    v___x_6076_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_6070_,
        v_inst_6072_,
        v_inst_6073_,
        v___y_6074_,
        v___y_6075_,
    );
    return v___x_6076_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(
    mut v_pu_6077_: *mut LeanObject,
    mut v_m_6078_: *mut LeanObject,
    mut v_inst_6079_: *mut LeanObject,
    mut v_inst_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6083_: u8 = 0;
    let mut v_res_6084_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6083_ = (lean_unbox(v_pu_6077_) as u8);
    v_res_6084_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(
        v_pu_boxed_6083_,
        v_m_6078_,
        v_inst_6079_,
        v_inst_6080_,
        v___y_6081_,
        v___y_6082_,
    );
    return v_res_6084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(
    mut v_m_6085_: *mut LeanObject,
    mut v_inst_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    v___x_6089_ =
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_6086_, v___y_6087_, v___y_6088_);
    return v___x_6089_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(mut v_pu_6091_: u8) -> *mut LeanObject {
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    v___x_6092_ = lean_box((v_pu_6091_) as usize);
    v___f_6093_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_6093_, 0, v___x_6092_);
    v___f_6094_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0;
    v___x_6095_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6095_, 0, v___f_6093_);
    lean_ctor_set(v___x_6095_, 1, v___f_6094_);
    return v___x_6095_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(
    mut v_pu_6096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6097_: u8 = 0;
    let mut v_res_6098_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6097_ = (lean_unbox(v_pu_6096_) as u8);
    v_res_6098_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_6097_);
    return v_res_6098_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(
    mut v_toPure_6099_: *mut LeanObject,
    mut v_____do__lift_6100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    v___x_6101_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6101_, 0, v_____do__lift_6100_);
    v___x_6102_ = lean_apply_2(v_toPure_6099_, lean_box(0), v___x_6101_);
    return v___x_6102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(
    mut v_toPure_6103_: *mut LeanObject,
    mut v_____do__lift_6104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    v___x_6105_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6105_, 0, v_____do__lift_6104_);
    v___x_6106_ = lean_apply_2(v_toPure_6103_, lean_box(0), v___x_6105_);
    return v___x_6106_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(
    mut v_toPure_6107_: *mut LeanObject,
    mut v_____do__lift_6108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    v___x_6109_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_6109_, 0, v_____do__lift_6108_);
    v___x_6110_ = lean_apply_2(v_toPure_6107_, lean_box(0), v___x_6109_);
    return v___x_6110_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(
    mut v_____do__lift_6111_: *mut LeanObject,
    mut v_i_6112_: *mut LeanObject,
    mut v_toPure_6113_: *mut LeanObject,
    mut v_____do__lift_6114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    v___x_6115_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_6115_, 0, v_____do__lift_6111_);
    lean_ctor_set(v___x_6115_, 1, v_i_6112_);
    lean_ctor_set(v___x_6115_, 2, v_____do__lift_6114_);
    v___x_6116_ = lean_apply_2(v_toPure_6113_, lean_box(0), v___x_6115_);
    return v___x_6116_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(
    mut v_i_6117_: *mut LeanObject,
    mut v_toPure_6118_: *mut LeanObject,
    mut v_pu_6119_: u8,
    mut v_inst_6120_: *mut LeanObject,
    mut v_f_6121_: *mut LeanObject,
    mut v_y_6122_: *mut LeanObject,
    mut v_toBind_6123_: *mut LeanObject,
    mut v_____do__lift_6124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    v___f_6125_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6125_, 0, v_____do__lift_6124_);
    lean_closure_set(v___f_6125_, 1, v_i_6117_);
    lean_closure_set(v___f_6125_, 2, v_toPure_6118_);
    v___x_6126_ =
        l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_6119_, v_inst_6120_, v_f_6121_, v_y_6122_);
    v___x_6127_ = lean_apply_4(
        v_toBind_6123_,
        lean_box(0),
        lean_box(0),
        v___x_6126_,
        v___f_6125_,
    );
    return v___x_6127_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(
    mut v_i_6128_: *mut LeanObject,
    mut v_toPure_6129_: *mut LeanObject,
    mut v_pu_6130_: *mut LeanObject,
    mut v_inst_6131_: *mut LeanObject,
    mut v_f_6132_: *mut LeanObject,
    mut v_y_6133_: *mut LeanObject,
    mut v_toBind_6134_: *mut LeanObject,
    mut v_____do__lift_6135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6136_: u8 = 0;
    let mut v_res_6137_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6136_ = (lean_unbox(v_pu_6130_) as u8);
    v_res_6137_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(
        v_i_6128_,
        v_toPure_6129_,
        v_pu_boxed_6136_,
        v_inst_6131_,
        v_f_6132_,
        v_y_6133_,
        v_toBind_6134_,
        v_____do__lift_6135_,
    );
    return v_res_6137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(
    mut v_____do__lift_6138_: *mut LeanObject,
    mut v_i_6139_: *mut LeanObject,
    mut v_toPure_6140_: *mut LeanObject,
    mut v_____do__lift_6141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    v___x_6142_ = lean_alloc_ctor(4, 3, (0) as u32);
    lean_ctor_set(v___x_6142_, 0, v_____do__lift_6138_);
    lean_ctor_set(v___x_6142_, 1, v_i_6139_);
    lean_ctor_set(v___x_6142_, 2, v_____do__lift_6141_);
    v___x_6143_ = lean_apply_2(v_toPure_6140_, lean_box(0), v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(
    mut v_i_6144_: *mut LeanObject,
    mut v_toPure_6145_: *mut LeanObject,
    mut v_f_6146_: *mut LeanObject,
    mut v_y_6147_: *mut LeanObject,
    mut v_toBind_6148_: *mut LeanObject,
    mut v_____do__lift_6149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    v___f_6150_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6150_, 0, v_____do__lift_6149_);
    lean_closure_set(v___f_6150_, 1, v_i_6144_);
    lean_closure_set(v___f_6150_, 2, v_toPure_6145_);
    v___x_6151_ = lean_apply_1(v_f_6146_, v_y_6147_);
    v___x_6152_ = lean_apply_4(
        v_toBind_6148_,
        lean_box(0),
        lean_box(0),
        v___x_6151_,
        v___f_6150_,
    );
    return v___x_6152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(
    mut v_____do__lift_6153_: *mut LeanObject,
    mut v_i_6154_: *mut LeanObject,
    mut v_offset_6155_: *mut LeanObject,
    mut v_____do__lift_6156_: *mut LeanObject,
    mut v_toPure_6157_: *mut LeanObject,
    mut v_____do__lift_6158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    v___x_6159_ = lean_alloc_ctor(5, 5, (0) as u32);
    lean_ctor_set(v___x_6159_, 0, v_____do__lift_6153_);
    lean_ctor_set(v___x_6159_, 1, v_i_6154_);
    lean_ctor_set(v___x_6159_, 2, v_offset_6155_);
    lean_ctor_set(v___x_6159_, 3, v_____do__lift_6156_);
    lean_ctor_set(v___x_6159_, 4, v_____do__lift_6158_);
    v___x_6160_ = lean_apply_2(v_toPure_6157_, lean_box(0), v___x_6159_);
    return v___x_6160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(
    mut v_____do__lift_6161_: *mut LeanObject,
    mut v_i_6162_: *mut LeanObject,
    mut v_offset_6163_: *mut LeanObject,
    mut v_toPure_6164_: *mut LeanObject,
    mut v_inst_6165_: *mut LeanObject,
    mut v_f_6166_: *mut LeanObject,
    mut v_ty_6167_: *mut LeanObject,
    mut v_toBind_6168_: *mut LeanObject,
    mut v_____do__lift_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    v___f_6170_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6170_, 0, v_____do__lift_6161_);
    lean_closure_set(v___f_6170_, 1, v_i_6162_);
    lean_closure_set(v___f_6170_, 2, v_offset_6163_);
    lean_closure_set(v___f_6170_, 3, v_____do__lift_6169_);
    lean_closure_set(v___f_6170_, 4, v_toPure_6164_);
    v___x_6171_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_6165_, v_f_6166_, v_ty_6167_);
    v___x_6172_ = lean_apply_4(
        v_toBind_6168_,
        lean_box(0),
        lean_box(0),
        v___x_6171_,
        v___f_6170_,
    );
    return v___x_6172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(
    mut v_i_6173_: *mut LeanObject,
    mut v_offset_6174_: *mut LeanObject,
    mut v_toPure_6175_: *mut LeanObject,
    mut v_inst_6176_: *mut LeanObject,
    mut v_f_6177_: *mut LeanObject,
    mut v_ty_6178_: *mut LeanObject,
    mut v_toBind_6179_: *mut LeanObject,
    mut v_y_6180_: *mut LeanObject,
    mut v_____do__lift_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_6179_);
    lean_inc(v_f_6177_);
    v___f_6182_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_6182_, 0, v_____do__lift_6181_);
    lean_closure_set(v___f_6182_, 1, v_i_6173_);
    lean_closure_set(v___f_6182_, 2, v_offset_6174_);
    lean_closure_set(v___f_6182_, 3, v_toPure_6175_);
    lean_closure_set(v___f_6182_, 4, v_inst_6176_);
    lean_closure_set(v___f_6182_, 5, v_f_6177_);
    lean_closure_set(v___f_6182_, 6, v_ty_6178_);
    lean_closure_set(v___f_6182_, 7, v_toBind_6179_);
    v___x_6183_ = lean_apply_1(v_f_6177_, v_y_6180_);
    v___x_6184_ = lean_apply_4(
        v_toBind_6179_,
        lean_box(0),
        lean_box(0),
        v___x_6183_,
        v___f_6182_,
    );
    return v___x_6184_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(
    mut v_cidx_6185_: *mut LeanObject,
    mut v_toPure_6186_: *mut LeanObject,
    mut v_____do__lift_6187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    v___x_6188_ = lean_alloc_ctor(6, 2, (0) as u32);
    lean_ctor_set(v___x_6188_, 0, v_____do__lift_6187_);
    lean_ctor_set(v___x_6188_, 1, v_cidx_6185_);
    v___x_6189_ = lean_apply_2(v_toPure_6186_, lean_box(0), v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(
    mut v_n_6190_: *mut LeanObject,
    mut v_check_6191_: u8,
    mut v_persistent_6192_: u8,
    mut v_toPure_6193_: *mut LeanObject,
    mut v_____do__lift_6194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    v___x_6195_ = lean_alloc_ctor(7, 2, (2) as u32);
    lean_ctor_set(v___x_6195_, 0, v_____do__lift_6194_);
    lean_ctor_set(v___x_6195_, 1, v_n_6190_);
    lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_check_6191_,
    );
    lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
        v_persistent_6192_,
    );
    v___x_6196_ = lean_apply_2(v_toPure_6193_, lean_box(0), v___x_6195_);
    return v___x_6196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(
    mut v_n_6197_: *mut LeanObject,
    mut v_check_6198_: *mut LeanObject,
    mut v_persistent_6199_: *mut LeanObject,
    mut v_toPure_6200_: *mut LeanObject,
    mut v_____do__lift_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_923__boxed_6202_: u8 = 0;
    let mut v_persistent_924__boxed_6203_: u8 = 0;
    let mut v_res_6204_: *mut LeanObject = core::ptr::null_mut();
    v_check_923__boxed_6202_ = (lean_unbox(v_check_6198_) as u8);
    v_persistent_924__boxed_6203_ = (lean_unbox(v_persistent_6199_) as u8);
    v_res_6204_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(
        v_n_6197_,
        v_check_923__boxed_6202_,
        v_persistent_924__boxed_6203_,
        v_toPure_6200_,
        v_____do__lift_6201_,
    );
    return v_res_6204_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(
    mut v_n_6205_: *mut LeanObject,
    mut v_check_6206_: u8,
    mut v_persistent_6207_: u8,
    mut v_objs_x3f_6208_: *mut LeanObject,
    mut v_toPure_6209_: *mut LeanObject,
    mut v_____do__lift_6210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    v___x_6211_ = lean_alloc_ctor(8, 3, (2) as u32);
    lean_ctor_set(v___x_6211_, 0, v_____do__lift_6210_);
    lean_ctor_set(v___x_6211_, 1, v_n_6205_);
    lean_ctor_set(v___x_6211_, 2, v_objs_x3f_6208_);
    lean_ctor_set_uint8(
        v___x_6211_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_check_6206_,
    );
    lean_ctor_set_uint8(
        v___x_6211_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v_persistent_6207_,
    );
    v___x_6212_ = lean_apply_2(v_toPure_6209_, lean_box(0), v___x_6211_);
    return v___x_6212_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(
    mut v_n_6213_: *mut LeanObject,
    mut v_check_6214_: *mut LeanObject,
    mut v_persistent_6215_: *mut LeanObject,
    mut v_objs_x3f_6216_: *mut LeanObject,
    mut v_toPure_6217_: *mut LeanObject,
    mut v_____do__lift_6218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_check_939__boxed_6219_: u8 = 0;
    let mut v_persistent_940__boxed_6220_: u8 = 0;
    let mut v_res_6221_: *mut LeanObject = core::ptr::null_mut();
    v_check_939__boxed_6219_ = (lean_unbox(v_check_6214_) as u8);
    v_persistent_940__boxed_6220_ = (lean_unbox(v_persistent_6215_) as u8);
    v_res_6221_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(
        v_n_6213_,
        v_check_939__boxed_6219_,
        v_persistent_940__boxed_6220_,
        v_objs_x3f_6216_,
        v_toPure_6217_,
        v_____do__lift_6218_,
    );
    return v_res_6221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(
    mut v_toPure_6222_: *mut LeanObject,
    mut v_____do__lift_6223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    v___x_6224_ = lean_alloc_ctor(9, 1, (0) as u32);
    lean_ctor_set(v___x_6224_, 0, v_____do__lift_6223_);
    v___x_6225_ = lean_apply_2(v_toPure_6222_, lean_box(0), v___x_6224_);
    return v___x_6225_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(
    mut v_pu_6226_: u8,
    mut v_m_6227_: *mut LeanObject,
    mut v_inst_6228_: *mut LeanObject,
    mut v_inst_6229_: *mut LeanObject,
    mut v_f_6230_: *mut LeanObject,
    mut v_decl_6231_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_6231_) {
        0 => {
            let mut v_toApplicative_6232_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6233_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6234_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_6235_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6236_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6232_ = lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6233_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6233_);
            v_toPure_6234_ = lean_ctor_get(v_toApplicative_6232_, 1);
            v_decl_6235_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc_ref(v_decl_6235_);
            lean_dec_ref_known(v_decl_6231_, 1);
            lean_inc(v_toPure_6234_);
            v___f_6236_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0 as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_6236_, 0, v_toPure_6234_);
            v___x_6237_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6235_,
            );
            v___x_6238_ = lean_apply_4(
                v_toBind_6233_,
                lean_box(0),
                lean_box(0),
                v___x_6237_,
                v___f_6236_,
            );
            return v___x_6238_;
        }
        1 => {
            let mut v_toApplicative_6239_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6240_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6241_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_6242_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6239_ = lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6240_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6240_);
            v_toPure_6241_ = lean_ctor_get(v_toApplicative_6239_, 1);
            v_decl_6242_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc_ref(v_decl_6242_);
            lean_dec_ref_known(v_decl_6231_, 1);
            lean_inc(v_toPure_6241_);
            v___f_6243_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1 as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_6243_, 0, v_toPure_6241_);
            v___x_6244_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6242_,
            );
            v___x_6245_ = lean_apply_4(
                v_toBind_6240_,
                lean_box(0),
                lean_box(0),
                v___x_6244_,
                v___f_6243_,
            );
            return v___x_6245_;
        }
        2 => {
            let mut v_toApplicative_6246_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6248_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decl_6249_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6246_ = lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6247_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6247_);
            v_toPure_6248_ = lean_ctor_get(v_toApplicative_6246_, 1);
            v_decl_6249_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc_ref(v_decl_6249_);
            lean_dec_ref_known(v_decl_6231_, 1);
            lean_inc(v_toPure_6248_);
            v___f_6250_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2 as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_6250_, 0, v_toPure_6248_);
            v___x_6251_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6249_,
            );
            v___x_6252_ = lean_apply_4(
                v_toBind_6247_,
                lean_box(0),
                lean_box(0),
                v___x_6251_,
                v___f_6250_,
            );
            return v___x_6252_;
        }
        3 => {
            let mut v_toApplicative_6253_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6254_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6255_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6256_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_6257_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6253_ = lean_ctor_get(v_inst_6229_, 0);
            lean_dec(v_inst_6228_);
            v_toBind_6254_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc_n(v_toBind_6254_, 2);
            v_toPure_6255_ = lean_ctor_get(v_toApplicative_6253_, 1);
            lean_inc(v_toPure_6255_);
            v_fvarId_6256_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6256_);
            v_i_6257_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_i_6257_);
            v_y_6258_ = lean_ctor_get(v_decl_6231_, 2);
            lean_inc(v_y_6258_);
            lean_dec_ref_known(v_decl_6231_, 3);
            v___x_6259_ = lean_box((v_pu_6226_) as usize);
            lean_inc(v_f_6230_);
            v___f_6260_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed
                    as *mut core::ffi::c_void,
                8,
                7,
            );
            lean_closure_set(v___f_6260_, 0, v_i_6257_);
            lean_closure_set(v___f_6260_, 1, v_toPure_6255_);
            lean_closure_set(v___f_6260_, 2, v___x_6259_);
            lean_closure_set(v___f_6260_, 3, v_inst_6229_);
            lean_closure_set(v___f_6260_, 4, v_f_6230_);
            lean_closure_set(v___f_6260_, 5, v_y_6258_);
            lean_closure_set(v___f_6260_, 6, v_toBind_6254_);
            v___x_6261_ = lean_apply_1(v_f_6230_, v_fvarId_6256_);
            v___x_6262_ = lean_apply_4(
                v_toBind_6254_,
                lean_box(0),
                lean_box(0),
                v___x_6261_,
                v___f_6260_,
            );
            return v___x_6262_;
        }
        4 => {
            let mut v_toApplicative_6263_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6264_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6265_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6266_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_6267_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6268_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6263_ = lean_ctor_get(v_inst_6229_, 0);
            lean_inc_ref(v_toApplicative_6263_);
            lean_dec(v_inst_6228_);
            v_toBind_6264_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc_n(v_toBind_6264_, 2);
            lean_dec_ref(v_inst_6229_);
            v_toPure_6265_ = lean_ctor_get(v_toApplicative_6263_, 1);
            lean_inc(v_toPure_6265_);
            lean_dec_ref(v_toApplicative_6263_);
            v_fvarId_6266_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6266_);
            v_i_6267_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_i_6267_);
            v_y_6268_ = lean_ctor_get(v_decl_6231_, 2);
            lean_inc(v_y_6268_);
            lean_dec_ref_known(v_decl_6231_, 3);
            lean_inc(v_f_6230_);
            v___f_6269_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_6269_, 0, v_i_6267_);
            lean_closure_set(v___f_6269_, 1, v_toPure_6265_);
            lean_closure_set(v___f_6269_, 2, v_f_6230_);
            lean_closure_set(v___f_6269_, 3, v_y_6268_);
            lean_closure_set(v___f_6269_, 4, v_toBind_6264_);
            v___x_6270_ = lean_apply_1(v_f_6230_, v_fvarId_6266_);
            v___x_6271_ = lean_apply_4(
                v_toBind_6264_,
                lean_box(0),
                lean_box(0),
                v___x_6270_,
                v___f_6269_,
            );
            return v___x_6271_;
        }
        5 => {
            let mut v_toApplicative_6272_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6273_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6274_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6275_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_6276_: *mut LeanObject = core::ptr::null_mut();
            let mut v_offset_6277_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6278_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_6279_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6280_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6272_ = lean_ctor_get(v_inst_6229_, 0);
            lean_dec(v_inst_6228_);
            v_toBind_6273_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc_n(v_toBind_6273_, 2);
            v_toPure_6274_ = lean_ctor_get(v_toApplicative_6272_, 1);
            lean_inc(v_toPure_6274_);
            v_fvarId_6275_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6275_);
            v_i_6276_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_i_6276_);
            v_offset_6277_ = lean_ctor_get(v_decl_6231_, 2);
            lean_inc(v_offset_6277_);
            v_y_6278_ = lean_ctor_get(v_decl_6231_, 3);
            lean_inc(v_y_6278_);
            v_ty_6279_ = lean_ctor_get(v_decl_6231_, 4);
            lean_inc_ref(v_ty_6279_);
            lean_dec_ref_known(v_decl_6231_, 5);
            lean_inc(v_f_6230_);
            v___f_6280_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9 as *mut core::ffi::c_void,
                9,
                8,
            );
            lean_closure_set(v___f_6280_, 0, v_i_6276_);
            lean_closure_set(v___f_6280_, 1, v_offset_6277_);
            lean_closure_set(v___f_6280_, 2, v_toPure_6274_);
            lean_closure_set(v___f_6280_, 3, v_inst_6229_);
            lean_closure_set(v___f_6280_, 4, v_f_6230_);
            lean_closure_set(v___f_6280_, 5, v_ty_6279_);
            lean_closure_set(v___f_6280_, 6, v_toBind_6273_);
            lean_closure_set(v___f_6280_, 7, v_y_6278_);
            v___x_6281_ = lean_apply_1(v_f_6230_, v_fvarId_6275_);
            v___x_6282_ = lean_apply_4(
                v_toBind_6273_,
                lean_box(0),
                lean_box(0),
                v___x_6281_,
                v___f_6280_,
            );
            return v___x_6282_;
        }
        6 => {
            let mut v_toApplicative_6283_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6284_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6285_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6286_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cidx_6287_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6288_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6283_ = lean_ctor_get(v_inst_6229_, 0);
            lean_inc_ref(v_toApplicative_6283_);
            lean_dec(v_inst_6228_);
            v_toBind_6284_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6284_);
            lean_dec_ref(v_inst_6229_);
            v_toPure_6285_ = lean_ctor_get(v_toApplicative_6283_, 1);
            lean_inc(v_toPure_6285_);
            lean_dec_ref(v_toApplicative_6283_);
            v_fvarId_6286_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6286_);
            v_cidx_6287_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_cidx_6287_);
            lean_dec_ref_known(v_decl_6231_, 2);
            v___f_6288_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_6288_, 0, v_cidx_6287_);
            lean_closure_set(v___f_6288_, 1, v_toPure_6285_);
            v___x_6289_ = lean_apply_1(v_f_6230_, v_fvarId_6286_);
            v___x_6290_ = lean_apply_4(
                v_toBind_6284_,
                lean_box(0),
                lean_box(0),
                v___x_6289_,
                v___f_6288_,
            );
            return v___x_6290_;
        }
        7 => {
            let mut v_toApplicative_6291_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6292_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6293_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6294_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_6295_: *mut LeanObject = core::ptr::null_mut();
            let mut v_check_6296_: u8 = 0;
            let mut v_persistent_6297_: u8 = 0;
            let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6291_ = lean_ctor_get(v_inst_6229_, 0);
            lean_inc_ref(v_toApplicative_6291_);
            lean_dec(v_inst_6228_);
            v_toBind_6292_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6292_);
            lean_dec_ref(v_inst_6229_);
            v_toPure_6293_ = lean_ctor_get(v_toApplicative_6291_, 1);
            lean_inc(v_toPure_6293_);
            lean_dec_ref(v_toApplicative_6291_);
            v_fvarId_6294_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6294_);
            v_n_6295_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_n_6295_);
            v_check_6296_ = lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_persistent_6297_ = lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
            );
            lean_dec_ref_known(v_decl_6231_, 2);
            v___x_6298_ = lean_box((v_check_6296_) as usize);
            v___x_6299_ = lean_box((v_persistent_6297_) as usize);
            v___f_6300_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_6300_, 0, v_n_6295_);
            lean_closure_set(v___f_6300_, 1, v___x_6298_);
            lean_closure_set(v___f_6300_, 2, v___x_6299_);
            lean_closure_set(v___f_6300_, 3, v_toPure_6293_);
            v___x_6301_ = lean_apply_1(v_f_6230_, v_fvarId_6294_);
            v___x_6302_ = lean_apply_4(
                v_toBind_6292_,
                lean_box(0),
                lean_box(0),
                v___x_6301_,
                v___f_6300_,
            );
            return v___x_6302_;
        }
        8 => {
            let mut v_toApplicative_6303_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6304_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6305_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6306_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_6307_: *mut LeanObject = core::ptr::null_mut();
            let mut v_check_6308_: u8 = 0;
            let mut v_persistent_6309_: u8 = 0;
            let mut v_objs_x3f_6310_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6303_ = lean_ctor_get(v_inst_6229_, 0);
            lean_inc_ref(v_toApplicative_6303_);
            lean_dec(v_inst_6228_);
            v_toBind_6304_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6304_);
            lean_dec_ref(v_inst_6229_);
            v_toPure_6305_ = lean_ctor_get(v_toApplicative_6303_, 1);
            lean_inc(v_toPure_6305_);
            lean_dec_ref(v_toApplicative_6303_);
            v_fvarId_6306_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6306_);
            v_n_6307_ = lean_ctor_get(v_decl_6231_, 1);
            lean_inc(v_n_6307_);
            v_check_6308_ = lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_persistent_6309_ = lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
            );
            v_objs_x3f_6310_ = lean_ctor_get(v_decl_6231_, 2);
            lean_inc(v_objs_x3f_6310_);
            lean_dec_ref_known(v_decl_6231_, 3);
            v___x_6311_ = lean_box((v_check_6308_) as usize);
            v___x_6312_ = lean_box((v_persistent_6309_) as usize);
            v___f_6313_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed
                    as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_6313_, 0, v_n_6307_);
            lean_closure_set(v___f_6313_, 1, v___x_6311_);
            lean_closure_set(v___f_6313_, 2, v___x_6312_);
            lean_closure_set(v___f_6313_, 3, v_objs_x3f_6310_);
            lean_closure_set(v___f_6313_, 4, v_toPure_6305_);
            v___x_6314_ = lean_apply_1(v_f_6230_, v_fvarId_6306_);
            v___x_6315_ = lean_apply_4(
                v_toBind_6304_,
                lean_box(0),
                lean_box(0),
                v___x_6314_,
                v___f_6313_,
            );
            return v___x_6315_;
        }
        _ => {
            let mut v_toApplicative_6316_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6317_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6318_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6316_ = lean_ctor_get(v_inst_6229_, 0);
            lean_inc_ref(v_toApplicative_6316_);
            lean_dec(v_inst_6228_);
            v_toBind_6317_ = lean_ctor_get(v_inst_6229_, 1);
            lean_inc(v_toBind_6317_);
            lean_dec_ref(v_inst_6229_);
            v_toPure_6318_ = lean_ctor_get(v_toApplicative_6316_, 1);
            lean_inc(v_toPure_6318_);
            lean_dec_ref(v_toApplicative_6316_);
            v_fvarId_6319_ = lean_ctor_get(v_decl_6231_, 0);
            lean_inc(v_fvarId_6319_);
            lean_dec_ref_known(v_decl_6231_, 1);
            v___f_6320_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13 as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_6320_, 0, v_toPure_6318_);
            v___x_6321_ = lean_apply_1(v_f_6230_, v_fvarId_6319_);
            v___x_6322_ = lean_apply_4(
                v_toBind_6317_,
                lean_box(0),
                lean_box(0),
                v___x_6321_,
                v___f_6320_,
            );
            return v___x_6322_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(
    mut v_pu_6323_: *mut LeanObject,
    mut v_m_6324_: *mut LeanObject,
    mut v_inst_6325_: *mut LeanObject,
    mut v_inst_6326_: *mut LeanObject,
    mut v_f_6327_: *mut LeanObject,
    mut v_decl_6328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6329_: u8 = 0;
    let mut v_res_6330_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6329_ = (lean_unbox(v_pu_6323_) as u8);
    v_res_6330_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(
        v_pu_boxed_6329_,
        v_m_6324_,
        v_inst_6325_,
        v_inst_6326_,
        v_f_6327_,
        v_decl_6328_,
    );
    return v_res_6330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(
    mut v_inst_6331_: *mut LeanObject,
    mut v_f_6332_: *mut LeanObject,
    mut v_y_6333_: *mut LeanObject,
    mut v_____r_6334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    v___x_6335_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_6331_, v_f_6332_, v_y_6333_);
    return v___x_6335_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(
    mut v_f_6336_: *mut LeanObject,
    mut v_y_6337_: *mut LeanObject,
    mut v_____r_6338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    v___x_6339_ = lean_apply_1(v_f_6336_, v_y_6337_);
    return v___x_6339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(
    mut v_inst_6340_: *mut LeanObject,
    mut v_f_6341_: *mut LeanObject,
    mut v_ty_6342_: *mut LeanObject,
    mut v_____r_6343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    v___x_6344_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_6340_, v_f_6341_, v_ty_6342_);
    return v___x_6344_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(
    mut v_f_6345_: *mut LeanObject,
    mut v_y_6346_: *mut LeanObject,
    mut v_toBind_6347_: *mut LeanObject,
    mut v___f_6348_: *mut LeanObject,
    mut v_____r_6349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    v___x_6350_ = lean_apply_1(v_f_6345_, v_y_6346_);
    v___x_6351_ = lean_apply_4(
        v_toBind_6347_,
        lean_box(0),
        lean_box(0),
        v___x_6350_,
        v___f_6348_,
    );
    return v___x_6351_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(
    mut v_m_6352_: *mut LeanObject,
    mut v_inst_6353_: *mut LeanObject,
    mut v_f_6354_: *mut LeanObject,
    mut v_decl_6355_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_6355_) {
        0 => {
            let mut v_decl_6356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6356_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc_ref(v_decl_6356_);
            lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6357_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6356_,
            );
            return v___x_6357_;
        }
        1 => {
            let mut v_decl_6358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6358_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc_ref(v_decl_6358_);
            lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6359_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6358_,
            );
            return v___x_6359_;
        }
        2 => {
            let mut v_decl_6360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6360_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc_ref(v_decl_6360_);
            lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6361_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6360_,
            );
            return v___x_6361_;
        }
        3 => {
            let mut v_toBind_6362_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6363_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6364_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6365_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_6362_ = lean_ctor_get(v_inst_6353_, 1);
            lean_inc(v_toBind_6362_);
            v_fvarId_6363_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc(v_fvarId_6363_);
            v_y_6364_ = lean_ctor_get(v_decl_6355_, 2);
            lean_inc(v_y_6364_);
            lean_dec_ref_known(v_decl_6355_, 3);
            lean_inc(v_f_6354_);
            v___f_6365_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_6365_, 0, v_inst_6353_);
            lean_closure_set(v___f_6365_, 1, v_f_6354_);
            lean_closure_set(v___f_6365_, 2, v_y_6364_);
            v___x_6366_ = lean_apply_1(v_f_6354_, v_fvarId_6363_);
            v___x_6367_ = lean_apply_4(
                v_toBind_6362_,
                lean_box(0),
                lean_box(0),
                v___x_6366_,
                v___f_6365_,
            );
            return v___x_6367_;
        }
        4 => {
            let mut v_toBind_6368_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6369_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_6368_ = lean_ctor_get(v_inst_6353_, 1);
            lean_inc(v_toBind_6368_);
            lean_dec_ref(v_inst_6353_);
            v_fvarId_6369_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc(v_fvarId_6369_);
            v_y_6370_ = lean_ctor_get(v_decl_6355_, 2);
            lean_inc(v_y_6370_);
            lean_dec_ref_known(v_decl_6355_, 3);
            lean_inc(v_f_6354_);
            v___f_6371_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_6371_, 0, v_f_6354_);
            lean_closure_set(v___f_6371_, 1, v_y_6370_);
            v___x_6372_ = lean_apply_1(v_f_6354_, v_fvarId_6369_);
            v___x_6373_ = lean_apply_4(
                v_toBind_6368_,
                lean_box(0),
                lean_box(0),
                v___x_6372_,
                v___f_6371_,
            );
            return v___x_6373_;
        }
        5 => {
            let mut v_toBind_6374_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6375_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_6376_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_6377_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_6374_ = lean_ctor_get(v_inst_6353_, 1);
            lean_inc_n(v_toBind_6374_, 2);
            v_fvarId_6375_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc(v_fvarId_6375_);
            v_y_6376_ = lean_ctor_get(v_decl_6355_, 3);
            lean_inc(v_y_6376_);
            v_ty_6377_ = lean_ctor_get(v_decl_6355_, 4);
            lean_inc_ref(v_ty_6377_);
            lean_dec_ref_known(v_decl_6355_, 5);
            lean_inc_n(v_f_6354_, 2);
            v___f_6378_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_6378_, 0, v_inst_6353_);
            lean_closure_set(v___f_6378_, 1, v_f_6354_);
            lean_closure_set(v___f_6378_, 2, v_ty_6377_);
            v___f_6379_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18 as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_6379_, 0, v_f_6354_);
            lean_closure_set(v___f_6379_, 1, v_y_6376_);
            lean_closure_set(v___f_6379_, 2, v_toBind_6374_);
            lean_closure_set(v___f_6379_, 3, v___f_6378_);
            v___x_6380_ = lean_apply_1(v_f_6354_, v_fvarId_6375_);
            v___x_6381_ = lean_apply_4(
                v_toBind_6374_,
                lean_box(0),
                lean_box(0),
                v___x_6380_,
                v___f_6379_,
            );
            return v___x_6381_;
        }
        _ => {
            let mut v_fvarId_6382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_6353_);
            v_fvarId_6382_ = lean_ctor_get(v_decl_6355_, 0);
            lean_inc(v_fvarId_6382_);
            lean_dec_ref(v_decl_6355_);
            v___x_6383_ = lean_apply_1(v_f_6354_, v_fvarId_6382_);
            return v___x_6383_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(mut v_pu_6385_: u8) -> *mut LeanObject {
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    v___x_6386_ = lean_box((v_pu_6385_) as usize);
    v___f_6387_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_6387_, 0, v___x_6386_);
    v___f_6388_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0;
    v___x_6389_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6389_, 0, v___f_6387_);
    lean_ctor_set(v___x_6389_, 1, v___f_6388_);
    return v___x_6389_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(
    mut v_pu_6390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6391_: u8 = 0;
    let mut v_res_6392_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6391_ = (lean_unbox(v_pu_6390_) as u8);
    v_res_6392_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_6391_);
    return v_res_6392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(
    mut v_ctorName_6393_: *mut LeanObject,
    mut v_params_6394_: *mut LeanObject,
    mut v_toPure_6395_: *mut LeanObject,
    mut v_____do__lift_6396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    v___x_6397_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6397_, 0, v_ctorName_6393_);
    lean_ctor_set(v___x_6397_, 1, v_params_6394_);
    lean_ctor_set(v___x_6397_, 2, v_____do__lift_6396_);
    v___x_6398_ = lean_apply_2(v_toPure_6395_, lean_box(0), v___x_6397_);
    return v___x_6398_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(
    mut v_ctorName_6399_: *mut LeanObject,
    mut v_toPure_6400_: *mut LeanObject,
    mut v_pu_6401_: u8,
    mut v_inst_6402_: *mut LeanObject,
    mut v_inst_6403_: *mut LeanObject,
    mut v_f_6404_: *mut LeanObject,
    mut v_code_6405_: *mut LeanObject,
    mut v_toBind_6406_: *mut LeanObject,
    mut v_params_6407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    v___f_6408_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6408_, 0, v_ctorName_6399_);
    lean_closure_set(v___f_6408_, 1, v_params_6407_);
    lean_closure_set(v___f_6408_, 2, v_toPure_6400_);
    v___x_6409_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_6401_,
        v_inst_6402_,
        v_inst_6403_,
        v_f_6404_,
        v_code_6405_,
    );
    v___x_6410_ = lean_apply_4(
        v_toBind_6406_,
        lean_box(0),
        lean_box(0),
        v___x_6409_,
        v___f_6408_,
    );
    return v___x_6410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(
    mut v_ctorName_6411_: *mut LeanObject,
    mut v_toPure_6412_: *mut LeanObject,
    mut v_pu_6413_: *mut LeanObject,
    mut v_inst_6414_: *mut LeanObject,
    mut v_inst_6415_: *mut LeanObject,
    mut v_f_6416_: *mut LeanObject,
    mut v_code_6417_: *mut LeanObject,
    mut v_toBind_6418_: *mut LeanObject,
    mut v_params_6419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6420_: u8 = 0;
    let mut v_res_6421_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6420_ = (lean_unbox(v_pu_6413_) as u8);
    v_res_6421_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(
        v_ctorName_6411_,
        v_toPure_6412_,
        v_pu_boxed_6420_,
        v_inst_6414_,
        v_inst_6415_,
        v_f_6416_,
        v_code_6417_,
        v_toBind_6418_,
        v_params_6419_,
    );
    return v_res_6421_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(
    mut v_info_6422_: *mut LeanObject,
    mut v_toPure_6423_: *mut LeanObject,
    mut v_____do__lift_6424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    v___x_6425_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6425_, 0, v_info_6422_);
    lean_ctor_set(v___x_6425_, 1, v_____do__lift_6424_);
    v___x_6426_ = lean_apply_2(v_toPure_6423_, lean_box(0), v___x_6425_);
    return v___x_6426_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(
    mut v_toPure_6427_: *mut LeanObject,
    mut v_____do__lift_6428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    v___x_6429_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_6429_, 0, v_____do__lift_6428_);
    v___x_6430_ = lean_apply_2(v_toPure_6427_, lean_box(0), v___x_6429_);
    return v___x_6430_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(
    mut v_pu_6431_: u8,
    mut v_m_6432_: *mut LeanObject,
    mut v_inst_6433_: *mut LeanObject,
    mut v_inst_6434_: *mut LeanObject,
    mut v_f_6435_: *mut LeanObject,
    mut v_alt_6436_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_alt_6436_) {
        0 => {
            let mut v_toApplicative_6437_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6438_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6439_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ctorName_6440_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_6441_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_6442_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6444_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_6447_: usize = 0;
            let mut v___x_6448_: usize = 0;
            let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6437_ = lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6438_ = lean_ctor_get(v_inst_6434_, 1);
            lean_inc_n(v_toBind_6438_, 2);
            v_toPure_6439_ = lean_ctor_get(v_toApplicative_6437_, 1);
            v_ctorName_6440_ = lean_ctor_get(v_alt_6436_, 0);
            lean_inc(v_ctorName_6440_);
            v_params_6441_ = lean_ctor_get(v_alt_6436_, 1);
            lean_inc_ref(v_params_6441_);
            v_code_6442_ = lean_ctor_get(v_alt_6436_, 2);
            lean_inc_ref(v_code_6442_);
            lean_dec_ref_known(v_alt_6436_, 3);
            v___x_6443_ = lean_box((v_pu_6431_) as usize);
            lean_inc(v_f_6435_);
            lean_inc_ref_n(v_inst_6434_, 2);
            lean_inc(v_inst_6433_);
            lean_inc(v_toPure_6439_);
            v___f_6444_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed as *mut core::ffi::c_void,
                9,
                8,
            );
            lean_closure_set(v___f_6444_, 0, v_ctorName_6440_);
            lean_closure_set(v___f_6444_, 1, v_toPure_6439_);
            lean_closure_set(v___f_6444_, 2, v___x_6443_);
            lean_closure_set(v___f_6444_, 3, v_inst_6433_);
            lean_closure_set(v___f_6444_, 4, v_inst_6434_);
            lean_closure_set(v___f_6444_, 5, v_f_6435_);
            lean_closure_set(v___f_6444_, 6, v_code_6442_);
            lean_closure_set(v___f_6444_, 7, v_toBind_6438_);
            v___x_6445_ = lean_box((v_pu_6431_) as usize);
            v___x_6446_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___x_6446_, 0, lean_box(0));
            lean_closure_set(v___x_6446_, 1, v___x_6445_);
            lean_closure_set(v___x_6446_, 2, v_inst_6433_);
            lean_closure_set(v___x_6446_, 3, v_inst_6434_);
            lean_closure_set(v___x_6446_, 4, v_f_6435_);
            v_sz_6447_ = lean_array_size(v_params_6441_);
            v___x_6448_ = 0usize;
            v___x_6449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_6434_,
                v___x_6446_,
                v_sz_6447_,
                v___x_6448_,
                v_params_6441_,
            );
            v___x_6450_ = lean_apply_4(
                v_toBind_6438_,
                lean_box(0),
                lean_box(0),
                v___x_6449_,
                v___f_6444_,
            );
            return v___x_6450_;
        }
        1 => {
            let mut v_toApplicative_6451_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6453_: *mut LeanObject = core::ptr::null_mut();
            let mut v_info_6454_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_6455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6451_ = lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6452_ = lean_ctor_get(v_inst_6434_, 1);
            lean_inc(v_toBind_6452_);
            v_toPure_6453_ = lean_ctor_get(v_toApplicative_6451_, 1);
            v_info_6454_ = lean_ctor_get(v_alt_6436_, 0);
            lean_inc_ref(v_info_6454_);
            v_code_6455_ = lean_ctor_get(v_alt_6436_, 1);
            lean_inc_ref(v_code_6455_);
            lean_dec_ref_known(v_alt_6436_, 2);
            lean_inc(v_toPure_6453_);
            v___f_6456_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_6456_, 0, v_info_6454_);
            lean_closure_set(v___f_6456_, 1, v_toPure_6453_);
            v___x_6457_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
                v_pu_6431_,
                v_inst_6433_,
                v_inst_6434_,
                v_f_6435_,
                v_code_6455_,
            );
            v___x_6458_ = lean_apply_4(
                v_toBind_6452_,
                lean_box(0),
                lean_box(0),
                v___x_6457_,
                v___f_6456_,
            );
            return v___x_6458_;
        }
        _ => {
            let mut v_toApplicative_6459_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6460_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6461_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_6462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_6459_ = lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6460_ = lean_ctor_get(v_inst_6434_, 1);
            lean_inc(v_toBind_6460_);
            v_toPure_6461_ = lean_ctor_get(v_toApplicative_6459_, 1);
            v_code_6462_ = lean_ctor_get(v_alt_6436_, 0);
            lean_inc_ref(v_code_6462_);
            lean_dec_ref_known(v_alt_6436_, 1);
            lean_inc(v_toPure_6461_);
            v___f_6463_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3 as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_6463_, 0, v_toPure_6461_);
            v___x_6464_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
                v_pu_6431_,
                v_inst_6433_,
                v_inst_6434_,
                v_f_6435_,
                v_code_6462_,
            );
            v___x_6465_ = lean_apply_4(
                v_toBind_6460_,
                lean_box(0),
                lean_box(0),
                v___x_6464_,
                v___f_6463_,
            );
            return v___x_6465_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(
    mut v_pu_6466_: *mut LeanObject,
    mut v_m_6467_: *mut LeanObject,
    mut v_inst_6468_: *mut LeanObject,
    mut v_inst_6469_: *mut LeanObject,
    mut v_f_6470_: *mut LeanObject,
    mut v_alt_6471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6472_: u8 = 0;
    let mut v_res_6473_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6472_ = (lean_unbox(v_pu_6466_) as u8);
    v_res_6473_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(
        v_pu_boxed_6472_,
        v_m_6467_,
        v_inst_6468_,
        v_inst_6469_,
        v_f_6470_,
        v_alt_6471_,
    );
    return v_res_6473_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(
    mut v_inst_6474_: *mut LeanObject,
    mut v_f_6475_: *mut LeanObject,
    mut v_code_6476_: *mut LeanObject,
    mut v_____r_6477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    v___x_6478_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6474_, v_f_6475_, v_code_6476_);
    return v___x_6478_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(
    mut v_m_6479_: *mut LeanObject,
    mut v_inst_6480_: *mut LeanObject,
    mut v_f_6481_: *mut LeanObject,
    mut v_alt_6482_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_alt_6482_) {
        0 => {
            let mut v_toApplicative_6483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_6484_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_6485_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_6486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6487_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6491_: u8 = 0;
            v_toApplicative_6483_ = lean_ctor_get(v_inst_6480_, 0);
            v_toBind_6484_ = lean_ctor_get(v_inst_6480_, 1);
            lean_inc(v_toBind_6484_);
            v_params_6485_ = lean_ctor_get(v_alt_6482_, 1);
            lean_inc_ref(v_params_6485_);
            v_code_6486_ = lean_ctor_get(v_alt_6482_, 2);
            lean_inc_ref(v_code_6486_);
            lean_dec_ref_known(v_alt_6482_, 3);
            lean_inc(v_f_6481_);
            lean_inc_ref(v_inst_6480_);
            v___f_6487_ = lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_6487_, 0, v_inst_6480_);
            lean_closure_set(v___f_6487_, 1, v_f_6481_);
            lean_closure_set(v___f_6487_, 2, v_code_6486_);
            v___x_6488_ = lean_unsigned_to_nat(0);
            v___x_6489_ = lean_array_get_size(v_params_6485_);
            v___x_6490_ = lean_box(0);
            v___x_6491_ = lean_nat_dec_lt(v___x_6488_, v___x_6489_);
            if v___x_6491_ == 0 {
                let mut v_toPure_6492_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_6483_);
                lean_dec_ref(v_params_6485_);
                lean_dec(v_f_6481_);
                lean_dec_ref(v_inst_6480_);
                v_toPure_6492_ = lean_ctor_get(v_toApplicative_6483_, 1);
                lean_inc(v_toPure_6492_);
                lean_dec_ref(v_toApplicative_6483_);
                v___x_6493_ = lean_apply_2(v_toPure_6492_, lean_box(0), v___x_6490_);
                v___x_6494_ = lean_apply_4(
                    v_toBind_6484_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6493_,
                    v___f_6487_,
                );
                return v___x_6494_;
            } else {
                let mut v___f_6495_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6496_: u8 = 0;
                lean_inc_ref(v_inst_6480_);
                v___f_6495_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_6495_, 0, v_inst_6480_);
                lean_closure_set(v___f_6495_, 1, v_f_6481_);
                v___x_6496_ = lean_nat_dec_le(v___x_6489_, v___x_6489_);
                if v___x_6496_ == 0 {
                    if v___x_6491_ == 0 {
                        let mut v_toPure_6497_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
                        lean_inc_ref(v_toApplicative_6483_);
                        lean_dec_ref(v___f_6495_);
                        lean_dec_ref(v_params_6485_);
                        lean_dec_ref(v_inst_6480_);
                        v_toPure_6497_ = lean_ctor_get(v_toApplicative_6483_, 1);
                        lean_inc(v_toPure_6497_);
                        lean_dec_ref(v_toApplicative_6483_);
                        v___x_6498_ = lean_apply_2(v_toPure_6497_, lean_box(0), v___x_6490_);
                        v___x_6499_ = lean_apply_4(
                            v_toBind_6484_,
                            lean_box(0),
                            lean_box(0),
                            v___x_6498_,
                            v___f_6487_,
                        );
                        return v___x_6499_;
                    } else {
                        let mut v___x_6500_: usize = 0;
                        let mut v___x_6501_: usize = 0;
                        let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
                        v___x_6500_ = 0usize;
                        v___x_6501_ = lean_usize_of_nat(v___x_6489_);
                        v___x_6502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_6480_,
                            v___f_6495_,
                            v_params_6485_,
                            v___x_6500_,
                            v___x_6501_,
                            v___x_6490_,
                        );
                        v___x_6503_ = lean_apply_4(
                            v_toBind_6484_,
                            lean_box(0),
                            lean_box(0),
                            v___x_6502_,
                            v___f_6487_,
                        );
                        return v___x_6503_;
                    }
                } else {
                    let mut v___x_6504_: usize = 0;
                    let mut v___x_6505_: usize = 0;
                    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6504_ = 0usize;
                    v___x_6505_ = lean_usize_of_nat(v___x_6489_);
                    v___x_6506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_6480_,
                        v___f_6495_,
                        v_params_6485_,
                        v___x_6504_,
                        v___x_6505_,
                        v___x_6490_,
                    );
                    v___x_6507_ = lean_apply_4(
                        v_toBind_6484_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6506_,
                        v___f_6487_,
                    );
                    return v___x_6507_;
                }
            }
        }
        1 => {
            let mut v_code_6508_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
            v_code_6508_ = lean_ctor_get(v_alt_6482_, 1);
            lean_inc_ref(v_code_6508_);
            lean_dec_ref_known(v_alt_6482_, 2);
            v___x_6509_ =
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6480_, v_f_6481_, v_code_6508_);
            return v___x_6509_;
        }
        _ => {
            let mut v_code_6510_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
            v_code_6510_ = lean_ctor_get(v_alt_6482_, 0);
            lean_inc_ref(v_code_6510_);
            lean_dec_ref_known(v_alt_6482_, 1);
            v___x_6511_ =
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6480_, v_f_6481_, v_code_6510_);
            return v___x_6511_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt(mut v_pu_6513_: u8) -> *mut LeanObject {
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    v___x_6514_ = lean_box((v_pu_6513_) as usize);
    v___f_6515_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_6515_, 0, v___x_6514_);
    v___f_6516_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0;
    v___x_6517_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6517_, 0, v___f_6515_);
    lean_ctor_set(v___x_6517_, 1, v___f_6516_);
    return v___x_6517_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(
    mut v_pu_6518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6519_: u8 = 0;
    let mut v_res_6520_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6519_ = (lean_unbox(v_pu_6518_) as u8);
    v_res_6520_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_6519_);
    return v_res_6520_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(
    mut v_toPure_6523_: *mut LeanObject,
    mut v_____do__lift_6524_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_6524_) == 0 {
        let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
        v___x_6525_ = lean_box(0);
        v___x_6526_ = lean_apply_2(v_toPure_6523_, lean_box(0), v___x_6525_);
        return v___x_6526_;
    } else {
        let mut v_val_6527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6528_: u8 = 0;
        v_val_6527_ = lean_ctor_get(v_____do__lift_6524_, 0);
        v___x_6528_ = (lean_unbox(v_val_6527_) as u8);
        if v___x_6528_ == 0 {
            let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
            v___x_6529_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0;
            v___x_6530_ = lean_apply_2(v_toPure_6523_, lean_box(0), v___x_6529_);
            return v___x_6530_;
        } else {
            let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
            v___x_6531_ = lean_box(0);
            v___x_6532_ = lean_apply_2(v_toPure_6523_, lean_box(0), v___x_6531_);
            return v___x_6532_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(
    mut v_toPure_6533_: *mut LeanObject,
    mut v_____do__lift_6534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6535_: *mut LeanObject = core::ptr::null_mut();
    v_res_6535_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(
            v_toPure_6533_,
            v_____do__lift_6534_,
        );
    lean_dec(v_____do__lift_6534_);
    return v_res_6535_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(
    mut v_toPure_6536_: *mut LeanObject,
    mut v_____do__lift_6537_: u8,
) -> *mut LeanObject {
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    v___x_6538_ = lean_box((v_____do__lift_6537_) as usize);
    v___x_6539_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6539_, 0, v___x_6538_);
    v___x_6540_ = lean_apply_2(v_toPure_6536_, lean_box(0), v___x_6539_);
    return v___x_6540_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(
    mut v_toPure_6541_: *mut LeanObject,
    mut v_____do__lift_6542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_405__boxed_6543_: u8 = 0;
    let mut v_res_6544_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_405__boxed_6543_ = (lean_unbox(v_____do__lift_6542_) as u8);
    v_res_6544_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(
            v_toPure_6541_,
            v_____do__lift_405__boxed_6543_,
        );
    return v_res_6544_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(
    mut v_inst_6545_: *mut LeanObject,
    mut v_f_6546_: *mut LeanObject,
    mut v_fvar_6547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6548_ = lean_ctor_get(v_inst_6545_, 0);
    lean_inc_ref(v_toApplicative_6548_);
    v_toBind_6549_ = lean_ctor_get(v_inst_6545_, 1);
    lean_inc_n(v_toBind_6549_, 2);
    lean_dec_ref(v_inst_6545_);
    v_toPure_6550_ = lean_ctor_get(v_toApplicative_6548_, 1);
    lean_inc_n(v_toPure_6550_, 2);
    lean_dec_ref(v_toApplicative_6548_);
    v___x_6551_ = lean_apply_1(v_f_6546_, v_fvar_6547_);
    v___f_6552_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6552_, 0, v_toPure_6550_);
    v___f_6553_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6553_, 0, v_toPure_6550_);
    v___x_6554_ = lean_apply_4(
        v_toBind_6549_,
        lean_box(0),
        lean_box(0),
        v___x_6551_,
        v___f_6553_,
    );
    v___x_6555_ = lean_apply_4(
        v_toBind_6549_,
        lean_box(0),
        lean_box(0),
        v___x_6554_,
        v___f_6552_,
    );
    return v___x_6555_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(
    mut v_m_6556_: *mut LeanObject,
    mut v_inst_6557_: *mut LeanObject,
    mut v_f_6558_: *mut LeanObject,
    mut v_fvar_6559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    v___x_6560_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(
            v_inst_6557_,
            v_f_6558_,
            v_fvar_6559_,
        );
    return v___x_6560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(
    mut v_toPure_6561_: *mut LeanObject,
    mut v_____do__lift_6562_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_6562_) == 0 {
        let mut v___x_6563_: u8 = 0;
        let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
        v___x_6563_ = 1;
        v___x_6564_ = lean_box((v___x_6563_) as usize);
        v___x_6565_ = lean_apply_2(v_toPure_6561_, lean_box(0), v___x_6564_);
        return v___x_6565_;
    } else {
        let mut v___x_6566_: u8 = 0;
        let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
        v___x_6566_ = 0;
        v___x_6567_ = lean_box((v___x_6566_) as usize);
        v___x_6568_ = lean_apply_2(v_toPure_6561_, lean_box(0), v___x_6567_);
        return v___x_6568_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(
    mut v_toPure_6569_: *mut LeanObject,
    mut v_____do__lift_6570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6571_: *mut LeanObject = core::ptr::null_mut();
    v_res_6571_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_6569_, v_____do__lift_6570_);
    lean_dec(v_____do__lift_6570_);
    return v_res_6571_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg(
    mut v_inst_6572_: *mut LeanObject,
    mut v_inst_6573_: *mut LeanObject,
    mut v_f_6574_: *mut LeanObject,
    mut v_x_6575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forFVarM_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6581_: u8 = 0;
    let mut v___f_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_unused_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6576_ = lean_ctor_get(v_inst_6572_, 0);
                v_toBind_6577_ = lean_ctor_get(v_inst_6572_, 1);
                lean_inc(v_toBind_6577_);
                v_forFVarM_6578_ = lean_ctor_get(v_inst_6573_, 1);
                v_isSharedCheck_6599_ = (!lean_is_exclusive(v_inst_6573_)) as u8;
                if v_isSharedCheck_6599_ == 0 {
                    v_unused_6600_ = lean_ctor_get(v_inst_6573_, 0);
                    lean_dec(v_unused_6600_);
                    v___x_6580_ = v_inst_6573_;
                    v_isShared_6581_ = v_isSharedCheck_6599_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_forFVarM_6578_);
                    lean_dec(v_inst_6573_);
                    v___x_6580_ = lean_box(0);
                    v_isShared_6581_ = v_isSharedCheck_6599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref_n(v_inst_6572_, 5);
                v___f_6582_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6582_, 0, v_inst_6572_);
                v___f_6583_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6583_, 0, v_inst_6572_);
                v___f_6584_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6584_, 0, v_inst_6572_);
                v___f_6585_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6585_, 0, v_inst_6572_);
                v___f_6586_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6586_, 0, v_inst_6572_);
                if v_isShared_6581_ == 0 {
                    lean_ctor_set(v___x_6580_, 1, v___f_6583_);
                    lean_ctor_set(v___x_6580_, 0, v___f_6582_);
                    v___x_6588_ = v___x_6580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___f_6582_);
                    lean_ctor_set(v_reuseFailAlloc_6598_, 1, v___f_6583_);
                    v___x_6588_ = v_reuseFailAlloc_6598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v_inst_6572_, 2);
                v___x_6589_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_6589_, 0, lean_box(0));
                lean_closure_set(v___x_6589_, 1, v_inst_6572_);
                v___x_6590_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_6590_, 0, v___x_6588_);
                lean_ctor_set(v___x_6590_, 1, v___x_6589_);
                lean_ctor_set(v___x_6590_, 2, v___f_6584_);
                lean_ctor_set(v___x_6590_, 3, v___f_6585_);
                lean_ctor_set(v___x_6590_, 4, v___f_6586_);
                v___x_6591_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
                lean_closure_set(v___x_6591_, 0, lean_box(0));
                lean_closure_set(v___x_6591_, 1, v_inst_6572_);
                v___x_6592_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6592_, 0, v___x_6590_);
                lean_ctor_set(v___x_6592_, 1, v___x_6591_);
                v_toPure_6593_ = lean_ctor_get(v_toApplicative_6576_, 1);
                lean_inc(v_toPure_6593_);
                v___x_6594_ = lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___x_6594_, 0, lean_box(0));
                lean_closure_set(v___x_6594_, 1, v_inst_6572_);
                lean_closure_set(v___x_6594_, 2, v_f_6574_);
                v___x_6595_ = lean_apply_4(
                    v_forFVarM_6578_,
                    lean_box(0),
                    v___x_6592_,
                    v___x_6594_,
                    v_x_6575_,
                );
                v___f_6596_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6596_, 0, v_toPure_6593_);
                v___x_6597_ = lean_apply_4(
                    v_toBind_6577_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6595_,
                    v___f_6596_,
                );
                return v___x_6597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM(
    mut v_m_6601_: *mut LeanObject,
    mut v_00_u03b1_6602_: *mut LeanObject,
    mut v_inst_6603_: *mut LeanObject,
    mut v_inst_6604_: *mut LeanObject,
    mut v_f_6605_: *mut LeanObject,
    mut v_x_6606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    v___x_6607_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_6603_, v_inst_6604_, v_f_6605_, v_x_6606_);
    return v___x_6607_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(
    mut v_toPure_6608_: *mut LeanObject,
    mut v_____do__lift_6609_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_6609_) == 0 {
        let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
        v___x_6610_ = lean_box(0);
        v___x_6611_ = lean_apply_2(v_toPure_6608_, lean_box(0), v___x_6610_);
        return v___x_6611_;
    } else {
        let mut v_val_6612_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6613_: u8 = 0;
        v_val_6612_ = lean_ctor_get(v_____do__lift_6609_, 0);
        v___x_6613_ = (lean_unbox(v_val_6612_) as u8);
        if v___x_6613_ == 0 {
            let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
            v___x_6614_ = lean_box(0);
            v___x_6615_ = lean_apply_2(v_toPure_6608_, lean_box(0), v___x_6614_);
            return v___x_6615_;
        } else {
            let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
            v___x_6616_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0;
            v___x_6617_ = lean_apply_2(v_toPure_6608_, lean_box(0), v___x_6616_);
            return v___x_6617_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(
    mut v_toPure_6618_: *mut LeanObject,
    mut v_____do__lift_6619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6620_: *mut LeanObject = core::ptr::null_mut();
    v_res_6620_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(
            v_toPure_6618_,
            v_____do__lift_6619_,
        );
    lean_dec(v_____do__lift_6619_);
    return v_res_6620_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(
    mut v_inst_6621_: *mut LeanObject,
    mut v_f_6622_: *mut LeanObject,
    mut v_fvar_6623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6624_ = lean_ctor_get(v_inst_6621_, 0);
    lean_inc_ref(v_toApplicative_6624_);
    v_toBind_6625_ = lean_ctor_get(v_inst_6621_, 1);
    lean_inc_n(v_toBind_6625_, 2);
    lean_dec_ref(v_inst_6621_);
    v_toPure_6626_ = lean_ctor_get(v_toApplicative_6624_, 1);
    lean_inc_n(v_toPure_6626_, 2);
    lean_dec_ref(v_toApplicative_6624_);
    v___x_6627_ = lean_apply_1(v_f_6622_, v_fvar_6623_);
    v___f_6628_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6628_, 0, v_toPure_6626_);
    v___f_6629_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6629_, 0, v_toPure_6626_);
    v___x_6630_ = lean_apply_4(
        v_toBind_6625_,
        lean_box(0),
        lean_box(0),
        v___x_6627_,
        v___f_6629_,
    );
    v___x_6631_ = lean_apply_4(
        v_toBind_6625_,
        lean_box(0),
        lean_box(0),
        v___x_6630_,
        v___f_6628_,
    );
    return v___x_6631_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(
    mut v_m_6632_: *mut LeanObject,
    mut v_inst_6633_: *mut LeanObject,
    mut v_f_6634_: *mut LeanObject,
    mut v_fvar_6635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    v___x_6636_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(
            v_inst_6633_,
            v_f_6634_,
            v_fvar_6635_,
        );
    return v___x_6636_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(
    mut v_toPure_6637_: *mut LeanObject,
    mut v_____do__lift_6638_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_6638_) == 1 {
        let mut v___x_6639_: u8 = 0;
        let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
        v___x_6639_ = 1;
        v___x_6640_ = lean_box((v___x_6639_) as usize);
        v___x_6641_ = lean_apply_2(v_toPure_6637_, lean_box(0), v___x_6640_);
        return v___x_6641_;
    } else {
        let mut v___x_6642_: u8 = 0;
        let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
        v___x_6642_ = 0;
        v___x_6643_ = lean_box((v___x_6642_) as usize);
        v___x_6644_ = lean_apply_2(v_toPure_6637_, lean_box(0), v___x_6643_);
        return v___x_6644_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(
    mut v_toPure_6645_: *mut LeanObject,
    mut v_____do__lift_6646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6647_: *mut LeanObject = core::ptr::null_mut();
    v_res_6647_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_6645_, v_____do__lift_6646_);
    lean_dec(v_____do__lift_6646_);
    return v_res_6647_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg(
    mut v_inst_6648_: *mut LeanObject,
    mut v_inst_6649_: *mut LeanObject,
    mut v_f_6650_: *mut LeanObject,
    mut v_x_6651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forFVarM_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6657_: u8 = 0;
    let mut v___f_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6675_: u8 = 0;
    let mut v_unused_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6652_ = lean_ctor_get(v_inst_6648_, 0);
                v_toBind_6653_ = lean_ctor_get(v_inst_6648_, 1);
                lean_inc(v_toBind_6653_);
                v_forFVarM_6654_ = lean_ctor_get(v_inst_6649_, 1);
                v_isSharedCheck_6675_ = (!lean_is_exclusive(v_inst_6649_)) as u8;
                if v_isSharedCheck_6675_ == 0 {
                    v_unused_6676_ = lean_ctor_get(v_inst_6649_, 0);
                    lean_dec(v_unused_6676_);
                    v___x_6656_ = v_inst_6649_;
                    v_isShared_6657_ = v_isSharedCheck_6675_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_forFVarM_6654_);
                    lean_dec(v_inst_6649_);
                    v___x_6656_ = lean_box(0);
                    v_isShared_6657_ = v_isSharedCheck_6675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref_n(v_inst_6648_, 5);
                v___f_6658_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6658_, 0, v_inst_6648_);
                v___f_6659_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6659_, 0, v_inst_6648_);
                v___f_6660_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6660_, 0, v_inst_6648_);
                v___f_6661_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6661_, 0, v_inst_6648_);
                v___f_6662_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_6662_, 0, v_inst_6648_);
                if v_isShared_6657_ == 0 {
                    lean_ctor_set(v___x_6656_, 1, v___f_6659_);
                    lean_ctor_set(v___x_6656_, 0, v___f_6658_);
                    v___x_6664_ = v___x_6656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6674_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6674_, 0, v___f_6658_);
                    lean_ctor_set(v_reuseFailAlloc_6674_, 1, v___f_6659_);
                    v___x_6664_ = v_reuseFailAlloc_6674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v_inst_6648_, 2);
                v___x_6665_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_6665_, 0, lean_box(0));
                lean_closure_set(v___x_6665_, 1, v_inst_6648_);
                v___x_6666_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_6666_, 0, v___x_6664_);
                lean_ctor_set(v___x_6666_, 1, v___x_6665_);
                lean_ctor_set(v___x_6666_, 2, v___f_6660_);
                lean_ctor_set(v___x_6666_, 3, v___f_6661_);
                lean_ctor_set(v___x_6666_, 4, v___f_6662_);
                v___x_6667_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
                lean_closure_set(v___x_6667_, 0, lean_box(0));
                lean_closure_set(v___x_6667_, 1, v_inst_6648_);
                v___x_6668_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6668_, 0, v___x_6666_);
                lean_ctor_set(v___x_6668_, 1, v___x_6667_);
                v_toPure_6669_ = lean_ctor_get(v_toApplicative_6652_, 1);
                lean_inc(v_toPure_6669_);
                v___x_6670_ = lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___x_6670_, 0, lean_box(0));
                lean_closure_set(v___x_6670_, 1, v_inst_6648_);
                lean_closure_set(v___x_6670_, 2, v_f_6650_);
                v___x_6671_ = lean_apply_4(
                    v_forFVarM_6654_,
                    lean_box(0),
                    v___x_6668_,
                    v___x_6670_,
                    v_x_6651_,
                );
                v___f_6672_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6672_, 0, v_toPure_6669_);
                v___x_6673_ = lean_apply_4(
                    v_toBind_6653_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6671_,
                    v___f_6672_,
                );
                return v___x_6673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM(
    mut v_m_6677_: *mut LeanObject,
    mut v_00_u03b1_6678_: *mut LeanObject,
    mut v_inst_6679_: *mut LeanObject,
    mut v_inst_6680_: *mut LeanObject,
    mut v_f_6681_: *mut LeanObject,
    mut v_x_6682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    v___x_6683_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_6679_, v_inst_6680_, v_f_6681_, v_x_6682_);
    return v___x_6683_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(
    mut v_f_6684_: *mut LeanObject,
    mut v_x_6685_: *mut LeanObject,
) -> u8 {
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: u8 = 0;
    v___x_6686_ = lean_apply_1(v_f_6684_, v_x_6685_);
    v___x_6687_ = (lean_unbox(v___x_6686_) as u8);
    return v___x_6687_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(
    mut v_f_6688_: *mut LeanObject,
    mut v_x_6689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6690_: u8 = 0;
    let mut v_r_6691_: *mut LeanObject = core::ptr::null_mut();
    v_res_6690_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_6688_, v_x_6689_);
    v_r_6691_ = lean_box((v_res_6690_) as usize);
    return v_r_6691_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg(
    mut v_inst_6711_: *mut LeanObject,
    mut v_f_6712_: *mut LeanObject,
    mut v_x_6713_: *mut LeanObject,
) -> u8 {
    let mut v___f_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: u8 = 0;
    v___f_6714_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6714_, 0, v_f_6712_);
    v___x_6715_ = l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9;
    v___x_6716_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_6715_, v_inst_6711_, v___f_6714_, v_x_6713_);
    v___x_6717_ = (lean_unbox(v___x_6716_) as u8);
    lean_dec(v___x_6716_);
    return v___x_6717_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(
    mut v_inst_6718_: *mut LeanObject,
    mut v_f_6719_: *mut LeanObject,
    mut v_x_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6721_: u8 = 0;
    let mut v_r_6722_: *mut LeanObject = core::ptr::null_mut();
    v_res_6721_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_6718_, v_f_6719_, v_x_6720_);
    v_r_6722_ = lean_box((v_res_6721_) as usize);
    return v_r_6722_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar(
    mut v_00_u03b1_6723_: *mut LeanObject,
    mut v_inst_6724_: *mut LeanObject,
    mut v_f_6725_: *mut LeanObject,
    mut v_x_6726_: *mut LeanObject,
) -> u8 {
    let mut v___x_6727_: u8 = 0;
    v___x_6727_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_6724_, v_f_6725_, v_x_6726_);
    return v___x_6727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___boxed(
    mut v_00_u03b1_6728_: *mut LeanObject,
    mut v_inst_6729_: *mut LeanObject,
    mut v_f_6730_: *mut LeanObject,
    mut v_x_6731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6732_: u8 = 0;
    let mut v_r_6733_: *mut LeanObject = core::ptr::null_mut();
    v_res_6732_ =
        l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_6728_, v_inst_6729_, v_f_6730_, v_x_6731_);
    v_r_6733_ = lean_box((v_res_6732_) as usize);
    return v_r_6733_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___redArg(
    mut v_inst_6734_: *mut LeanObject,
    mut v_f_6735_: *mut LeanObject,
    mut v_x_6736_: *mut LeanObject,
) -> u8 {
    let mut v___f_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: u8 = 0;
    v___f_6737_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6737_, 0, v_f_6735_);
    v___x_6738_ = l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9;
    v___x_6739_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_6738_, v_inst_6734_, v___f_6737_, v_x_6736_);
    v___x_6740_ = (lean_unbox(v___x_6739_) as u8);
    lean_dec(v___x_6739_);
    return v___x_6740_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___redArg___boxed(
    mut v_inst_6741_: *mut LeanObject,
    mut v_f_6742_: *mut LeanObject,
    mut v_x_6743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6744_: u8 = 0;
    let mut v_r_6745_: *mut LeanObject = core::ptr::null_mut();
    v_res_6744_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_6741_, v_f_6742_, v_x_6743_);
    v_r_6745_ = lean_box((v_res_6744_) as usize);
    return v_r_6745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar(
    mut v_00_u03b1_6746_: *mut LeanObject,
    mut v_inst_6747_: *mut LeanObject,
    mut v_f_6748_: *mut LeanObject,
    mut v_x_6749_: *mut LeanObject,
) -> u8 {
    let mut v___x_6750_: u8 = 0;
    v___x_6750_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_6747_, v_f_6748_, v_x_6749_);
    return v___x_6750_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___boxed(
    mut v_00_u03b1_6751_: *mut LeanObject,
    mut v_inst_6752_: *mut LeanObject,
    mut v_f_6753_: *mut LeanObject,
    mut v_x_6754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6755_: u8 = 0;
    let mut v_r_6756_: *mut LeanObject = core::ptr::null_mut();
    v_res_6755_ =
        l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_6751_, v_inst_6752_, v_f_6753_, v_x_6754_);
    v_r_6756_ = lean_box((v_res_6755_) as usize);
    return v_r_6756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_FVarUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_FVarUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
}
