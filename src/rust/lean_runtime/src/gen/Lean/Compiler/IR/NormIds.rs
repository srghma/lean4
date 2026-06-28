// Lean compiler output
// Module: Lean.Compiler.IR.NormIds
// Imports: Lean.Compiler.IR.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Lean::Compiler::IR::Basic::{
    initialize_Lean_Compiler_IR_Basic, l_Lean_IR_Alt_body, l_Lean_IR_Decl_updateBody_x21,
    l_Lean_IR_FnBody_body, l_Lean_IR_FnBody_isTerminal, l_Lean_IR_instBEqVarId_beq,
    runtime_initialize_Lean_Compiler_IR_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_NormalizeIds_withVar___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value: LeanClosureObject<3> =
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
        m_fun: l_StateT_map as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value: LeanClosureObject<3> =
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
        m_fun: l_StateT_pure as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value: LeanClosureObject<3> =
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
        m_fun: l_StateT_bind as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_IR_NormalizeIds_withParams___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_NormalizeIds_withParams___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_IR_NormalizeIds_instMonadLiftMN: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(
    mut v_k_1778_: *mut LeanObject,
    mut v_t_1779_: *mut LeanObject,
) -> u8 {
    let mut v_k_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1779_) == 0 {
                    v_k_1780_ = lean_ctor_get(v_t_1779_, 1);
                    v_l_1781_ = lean_ctor_get(v_t_1779_, 3);
                    v_r_1782_ = lean_ctor_get(v_t_1779_, 4);
                    v___x_1783_ = lean_nat_dec_lt(v_k_1778_, v_k_1780_);
                    if v___x_1783_ == 0 {
                        v___x_1784_ = lean_nat_dec_eq(v_k_1778_, v_k_1780_);
                        if v___x_1784_ == 0 {
                            v_t_1779_ = v_r_1782_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1784_;
                        }
                    } else {
                        v_t_1779_ = v_l_1781_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1787_ = 0;
                    return v___x_1787_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg___boxed(
    mut v_k_1788_: *mut LeanObject,
    mut v_t_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1790_: u8 = 0;
    let mut v_r_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1790_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(
            v_k_1788_, v_t_1789_,
        );
    lean_dec(v_t_1789_);
    lean_dec(v_k_1788_);
    v_r_1791_ = lean_box((v_res_1790_) as usize);
    return v_r_1791_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(
    mut v_k_1792_: *mut LeanObject,
    mut v_v_1793_: *mut LeanObject,
    mut v_t_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: u8 = 0;
    let mut v_impl_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v_size_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_unused_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_unused_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut v_unused_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v_k_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_unused_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v_unused_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1961_: u8 = 0;
    let mut v_size_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_unused_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_unused_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_unused_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v_k_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_unused_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_unused_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1794_) == 0 {
                    v_size_1795_ = lean_ctor_get(v_t_1794_, 0);
                    v_k_1796_ = lean_ctor_get(v_t_1794_, 1);
                    v_v_1797_ = lean_ctor_get(v_t_1794_, 2);
                    v_l_1798_ = lean_ctor_get(v_t_1794_, 3);
                    v_r_1799_ = lean_ctor_get(v_t_1794_, 4);
                    v_isSharedCheck_2080_ = (!lean_is_exclusive(v_t_1794_)) as u8;
                    if v_isSharedCheck_2080_ == 0 {
                        v___x_1801_ = v_t_1794_;
                        v_isShared_1802_ = v_isSharedCheck_2080_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1799_);
                        lean_inc(v_l_1798_);
                        lean_inc(v_v_1797_);
                        lean_inc(v_k_1796_);
                        lean_inc(v_size_1795_);
                        lean_dec(v_t_1794_);
                        v___x_1801_ = lean_box(0);
                        v_isShared_1802_ = v_isSharedCheck_2080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2081_ = lean_unsigned_to_nat(1);
                    v___x_2082_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                    lean_ctor_set(v___x_2082_, 1, v_k_1792_);
                    lean_ctor_set(v___x_2082_, 2, v_v_1793_);
                    lean_ctor_set(v___x_2082_, 3, v_t_1794_);
                    lean_ctor_set(v___x_2082_, 4, v_t_1794_);
                    return v___x_2082_;
                }
            }
            1 => {
                v___x_1803_ = lean_nat_dec_lt(v_k_1792_, v_k_1796_);
                if v___x_1803_ == 0 {
                    v___x_1804_ = lean_nat_dec_eq(v_k_1792_, v_k_1796_);
                    if v___x_1804_ == 0 {
                        lean_dec(v_size_1795_);
                        v_impl_1805_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_1792_, v_v_1793_, v_r_1799_);
                        v___x_1806_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1798_) == 0 {
                            v_size_1807_ = lean_ctor_get(v_l_1798_, 0);
                            v_size_1808_ = lean_ctor_get(v_impl_1805_, 0);
                            lean_inc(v_size_1808_);
                            v_k_1809_ = lean_ctor_get(v_impl_1805_, 1);
                            lean_inc(v_k_1809_);
                            v_v_1810_ = lean_ctor_get(v_impl_1805_, 2);
                            lean_inc(v_v_1810_);
                            v_l_1811_ = lean_ctor_get(v_impl_1805_, 3);
                            lean_inc(v_l_1811_);
                            v_r_1812_ = lean_ctor_get(v_impl_1805_, 4);
                            lean_inc(v_r_1812_);
                            v___x_1813_ = lean_unsigned_to_nat(3);
                            v___x_1814_ = lean_nat_mul(v___x_1813_, v_size_1807_);
                            v___x_1815_ = lean_nat_dec_lt(v___x_1814_, v_size_1808_);
                            lean_dec(v___x_1814_);
                            if v___x_1815_ == 0 {
                                lean_dec(v_r_1812_);
                                lean_dec(v_l_1811_);
                                lean_dec(v_v_1810_);
                                lean_dec(v_k_1809_);
                                v___x_1816_ = lean_nat_add(v___x_1806_, v_size_1807_);
                                v___x_1817_ = lean_nat_add(v___x_1816_, v_size_1808_);
                                lean_dec(v_size_1808_);
                                lean_dec(v___x_1816_);
                                if v_isShared_1802_ == 0 {
                                    lean_ctor_set(v___x_1801_, 4, v_impl_1805_);
                                    lean_ctor_set(v___x_1801_, 0, v___x_1817_);
                                    v___x_1819_ = v___x_1801_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                                    lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_k_1796_);
                                    lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_v_1797_);
                                    lean_ctor_set(v_reuseFailAlloc_1820_, 3, v_l_1798_);
                                    lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_impl_1805_);
                                    v___x_1819_ = v_reuseFailAlloc_1820_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1884_ = (!lean_is_exclusive(v_impl_1805_)) as u8;
                                if v_isSharedCheck_1884_ == 0 {
                                    v_unused_1885_ = lean_ctor_get(v_impl_1805_, 4);
                                    lean_dec(v_unused_1885_);
                                    v_unused_1886_ = lean_ctor_get(v_impl_1805_, 3);
                                    lean_dec(v_unused_1886_);
                                    v_unused_1887_ = lean_ctor_get(v_impl_1805_, 2);
                                    lean_dec(v_unused_1887_);
                                    v_unused_1888_ = lean_ctor_get(v_impl_1805_, 1);
                                    lean_dec(v_unused_1888_);
                                    v_unused_1889_ = lean_ctor_get(v_impl_1805_, 0);
                                    lean_dec(v_unused_1889_);
                                    v___x_1822_ = v_impl_1805_;
                                    v_isShared_1823_ = v_isSharedCheck_1884_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1805_);
                                    v___x_1822_ = lean_box(0);
                                    v_isShared_1823_ = v_isSharedCheck_1884_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1890_ = lean_ctor_get(v_impl_1805_, 3);
                            lean_inc(v_l_1890_);
                            if lean_obj_tag(v_l_1890_) == 0 {
                                v_r_1891_ = lean_ctor_get(v_impl_1805_, 4);
                                v_k_1892_ = lean_ctor_get(v_impl_1805_, 1);
                                v_v_1893_ = lean_ctor_get(v_impl_1805_, 2);
                                v_isSharedCheck_1916_ = (!lean_is_exclusive(v_impl_1805_)) as u8;
                                if v_isSharedCheck_1916_ == 0 {
                                    v_unused_1917_ = lean_ctor_get(v_impl_1805_, 3);
                                    lean_dec(v_unused_1917_);
                                    v_unused_1918_ = lean_ctor_get(v_impl_1805_, 0);
                                    lean_dec(v_unused_1918_);
                                    v___x_1895_ = v_impl_1805_;
                                    v_isShared_1896_ = v_isSharedCheck_1916_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1891_);
                                    lean_inc(v_v_1893_);
                                    lean_inc(v_k_1892_);
                                    lean_dec(v_impl_1805_);
                                    v___x_1895_ = lean_box(0);
                                    v_isShared_1896_ = v_isSharedCheck_1916_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1919_ = lean_ctor_get(v_impl_1805_, 4);
                                lean_inc(v_r_1919_);
                                if lean_obj_tag(v_r_1919_) == 0 {
                                    v_k_1920_ = lean_ctor_get(v_impl_1805_, 1);
                                    v_v_1921_ = lean_ctor_get(v_impl_1805_, 2);
                                    v_isSharedCheck_1932_ =
                                        (!lean_is_exclusive(v_impl_1805_)) as u8;
                                    if v_isSharedCheck_1932_ == 0 {
                                        v_unused_1933_ = lean_ctor_get(v_impl_1805_, 4);
                                        lean_dec(v_unused_1933_);
                                        v_unused_1934_ = lean_ctor_get(v_impl_1805_, 3);
                                        lean_dec(v_unused_1934_);
                                        v_unused_1935_ = lean_ctor_get(v_impl_1805_, 0);
                                        lean_dec(v_unused_1935_);
                                        v___x_1923_ = v_impl_1805_;
                                        v_isShared_1924_ = v_isSharedCheck_1932_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1921_);
                                        lean_inc(v_k_1920_);
                                        lean_dec(v_impl_1805_);
                                        v___x_1923_ = lean_box(0);
                                        v_isShared_1924_ = v_isSharedCheck_1932_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1936_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1802_ == 0 {
                                        lean_ctor_set(v___x_1801_, 4, v_impl_1805_);
                                        lean_ctor_set(v___x_1801_, 3, v_r_1919_);
                                        lean_ctor_set(v___x_1801_, 0, v___x_1936_);
                                        v___x_1938_ = v___x_1801_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
                                        lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1796_);
                                        lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1797_);
                                        lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_r_1919_);
                                        lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_impl_1805_);
                                        v___x_1938_ = v_reuseFailAlloc_1939_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_1797_);
                        lean_dec(v_k_1796_);
                        if v_isShared_1802_ == 0 {
                            lean_ctor_set(v___x_1801_, 2, v_v_1793_);
                            lean_ctor_set(v___x_1801_, 1, v_k_1792_);
                            v___x_1941_ = v___x_1801_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_size_1795_);
                            lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_k_1792_);
                            lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_v_1793_);
                            lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_l_1798_);
                            lean_ctor_set(v_reuseFailAlloc_1942_, 4, v_r_1799_);
                            v___x_1941_ = v_reuseFailAlloc_1942_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_1795_);
                    v_impl_1943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_1792_, v_v_1793_, v_l_1798_);
                    v___x_1944_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_1799_) == 0 {
                        v_size_1945_ = lean_ctor_get(v_r_1799_, 0);
                        v_size_1946_ = lean_ctor_get(v_impl_1943_, 0);
                        lean_inc(v_size_1946_);
                        v_k_1947_ = lean_ctor_get(v_impl_1943_, 1);
                        lean_inc(v_k_1947_);
                        v_v_1948_ = lean_ctor_get(v_impl_1943_, 2);
                        lean_inc(v_v_1948_);
                        v_l_1949_ = lean_ctor_get(v_impl_1943_, 3);
                        lean_inc(v_l_1949_);
                        v_r_1950_ = lean_ctor_get(v_impl_1943_, 4);
                        lean_inc(v_r_1950_);
                        v___x_1951_ = lean_unsigned_to_nat(3);
                        v___x_1952_ = lean_nat_mul(v___x_1951_, v_size_1945_);
                        v___x_1953_ = lean_nat_dec_lt(v___x_1952_, v_size_1946_);
                        lean_dec(v___x_1952_);
                        if v___x_1953_ == 0 {
                            lean_dec(v_r_1950_);
                            lean_dec(v_l_1949_);
                            lean_dec(v_v_1948_);
                            lean_dec(v_k_1947_);
                            v___x_1954_ = lean_nat_add(v___x_1944_, v_size_1946_);
                            lean_dec(v_size_1946_);
                            v___x_1955_ = lean_nat_add(v___x_1954_, v_size_1945_);
                            lean_dec(v___x_1954_);
                            if v_isShared_1802_ == 0 {
                                lean_ctor_set(v___x_1801_, 3, v_impl_1943_);
                                lean_ctor_set(v___x_1801_, 0, v___x_1955_);
                                v___x_1957_ = v___x_1801_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
                                lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_k_1796_);
                                lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_v_1797_);
                                lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_impl_1943_);
                                lean_ctor_set(v_reuseFailAlloc_1958_, 4, v_r_1799_);
                                v___x_1957_ = v_reuseFailAlloc_1958_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_2024_ = (!lean_is_exclusive(v_impl_1943_)) as u8;
                            if v_isSharedCheck_2024_ == 0 {
                                v_unused_2025_ = lean_ctor_get(v_impl_1943_, 4);
                                lean_dec(v_unused_2025_);
                                v_unused_2026_ = lean_ctor_get(v_impl_1943_, 3);
                                lean_dec(v_unused_2026_);
                                v_unused_2027_ = lean_ctor_get(v_impl_1943_, 2);
                                lean_dec(v_unused_2027_);
                                v_unused_2028_ = lean_ctor_get(v_impl_1943_, 1);
                                lean_dec(v_unused_2028_);
                                v_unused_2029_ = lean_ctor_get(v_impl_1943_, 0);
                                lean_dec(v_unused_2029_);
                                v___x_1960_ = v_impl_1943_;
                                v_isShared_1961_ = v_isSharedCheck_2024_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_1943_);
                                v___x_1960_ = lean_box(0);
                                v_isShared_1961_ = v_isSharedCheck_2024_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_2030_ = lean_ctor_get(v_impl_1943_, 3);
                        lean_inc(v_l_2030_);
                        if lean_obj_tag(v_l_2030_) == 0 {
                            v_r_2031_ = lean_ctor_get(v_impl_1943_, 4);
                            v_k_2032_ = lean_ctor_get(v_impl_1943_, 1);
                            v_v_2033_ = lean_ctor_get(v_impl_1943_, 2);
                            v_isSharedCheck_2044_ = (!lean_is_exclusive(v_impl_1943_)) as u8;
                            if v_isSharedCheck_2044_ == 0 {
                                v_unused_2045_ = lean_ctor_get(v_impl_1943_, 3);
                                lean_dec(v_unused_2045_);
                                v_unused_2046_ = lean_ctor_get(v_impl_1943_, 0);
                                lean_dec(v_unused_2046_);
                                v___x_2035_ = v_impl_1943_;
                                v_isShared_2036_ = v_isSharedCheck_2044_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_2031_);
                                lean_inc(v_v_2033_);
                                lean_inc(v_k_2032_);
                                lean_dec(v_impl_1943_);
                                v___x_2035_ = lean_box(0);
                                v_isShared_2036_ = v_isSharedCheck_2044_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_2047_ = lean_ctor_get(v_impl_1943_, 4);
                            lean_inc(v_r_2047_);
                            if lean_obj_tag(v_r_2047_) == 0 {
                                v_k_2048_ = lean_ctor_get(v_impl_1943_, 1);
                                v_v_2049_ = lean_ctor_get(v_impl_1943_, 2);
                                v_isSharedCheck_2072_ = (!lean_is_exclusive(v_impl_1943_)) as u8;
                                if v_isSharedCheck_2072_ == 0 {
                                    v_unused_2073_ = lean_ctor_get(v_impl_1943_, 4);
                                    lean_dec(v_unused_2073_);
                                    v_unused_2074_ = lean_ctor_get(v_impl_1943_, 3);
                                    lean_dec(v_unused_2074_);
                                    v_unused_2075_ = lean_ctor_get(v_impl_1943_, 0);
                                    lean_dec(v_unused_2075_);
                                    v___x_2051_ = v_impl_1943_;
                                    v_isShared_2052_ = v_isSharedCheck_2072_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_2049_);
                                    lean_inc(v_k_2048_);
                                    lean_dec(v_impl_1943_);
                                    v___x_2051_ = lean_box(0);
                                    v_isShared_2052_ = v_isSharedCheck_2072_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_2076_ = lean_unsigned_to_nat(2);
                                if v_isShared_1802_ == 0 {
                                    lean_ctor_set(v___x_1801_, 4, v_r_2047_);
                                    lean_ctor_set(v___x_1801_, 3, v_impl_1943_);
                                    lean_ctor_set(v___x_1801_, 0, v___x_2076_);
                                    v___x_2078_ = v___x_1801_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
                                    lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_1796_);
                                    lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_1797_);
                                    lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_impl_1943_);
                                    lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_r_2047_);
                                    v___x_2078_ = v_reuseFailAlloc_2079_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1819_;
            }
            3 => {
                v_size_1824_ = lean_ctor_get(v_l_1811_, 0);
                v_k_1825_ = lean_ctor_get(v_l_1811_, 1);
                v_v_1826_ = lean_ctor_get(v_l_1811_, 2);
                v_l_1827_ = lean_ctor_get(v_l_1811_, 3);
                v_r_1828_ = lean_ctor_get(v_l_1811_, 4);
                v_size_1829_ = lean_ctor_get(v_r_1812_, 0);
                v___x_1830_ = lean_unsigned_to_nat(2);
                v___x_1831_ = lean_nat_mul(v___x_1830_, v_size_1829_);
                v___x_1832_ = lean_nat_dec_lt(v_size_1824_, v___x_1831_);
                lean_dec(v___x_1831_);
                if v___x_1832_ == 0 {
                    lean_inc(v_r_1828_);
                    lean_inc(v_l_1827_);
                    lean_inc(v_v_1826_);
                    lean_inc(v_k_1825_);
                    v_isSharedCheck_1860_ = (!lean_is_exclusive(v_l_1811_)) as u8;
                    if v_isSharedCheck_1860_ == 0 {
                        v_unused_1861_ = lean_ctor_get(v_l_1811_, 4);
                        lean_dec(v_unused_1861_);
                        v_unused_1862_ = lean_ctor_get(v_l_1811_, 3);
                        lean_dec(v_unused_1862_);
                        v_unused_1863_ = lean_ctor_get(v_l_1811_, 2);
                        lean_dec(v_unused_1863_);
                        v_unused_1864_ = lean_ctor_get(v_l_1811_, 1);
                        lean_dec(v_unused_1864_);
                        v_unused_1865_ = lean_ctor_get(v_l_1811_, 0);
                        lean_dec(v_unused_1865_);
                        v___x_1834_ = v_l_1811_;
                        v_isShared_1835_ = v_isSharedCheck_1860_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_1811_);
                        v___x_1834_ = lean_box(0);
                        v_isShared_1835_ = v_isSharedCheck_1860_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1801_);
                    v___x_1866_ = lean_nat_add(v___x_1806_, v_size_1807_);
                    v___x_1867_ = lean_nat_add(v___x_1866_, v_size_1808_);
                    lean_dec(v_size_1808_);
                    v___x_1868_ = lean_nat_add(v___x_1866_, v_size_1824_);
                    lean_dec(v___x_1866_);
                    lean_inc_ref(v_l_1798_);
                    if v_isShared_1823_ == 0 {
                        lean_ctor_set(v___x_1822_, 4, v_l_1811_);
                        lean_ctor_set(v___x_1822_, 3, v_l_1798_);
                        lean_ctor_set(v___x_1822_, 2, v_v_1797_);
                        lean_ctor_set(v___x_1822_, 1, v_k_1796_);
                        lean_ctor_set(v___x_1822_, 0, v___x_1868_);
                        v___x_1870_ = v___x_1822_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1868_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_k_1796_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1797_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_l_1798_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 4, v_l_1811_);
                        v___x_1870_ = v_reuseFailAlloc_1883_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1836_ = lean_nat_add(v___x_1806_, v_size_1807_);
                v___x_1837_ = lean_nat_add(v___x_1836_, v_size_1808_);
                lean_dec(v_size_1808_);
                if lean_obj_tag(v_l_1827_) == 0 {
                    v_size_1858_ = lean_ctor_get(v_l_1827_, 0);
                    lean_inc(v_size_1858_);
                    v___y_1850_ = v_size_1858_;
                    state = 8;
                    continue;
                } else {
                    v___x_1859_ = lean_unsigned_to_nat(0);
                    v___y_1850_ = v___x_1859_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1842_ = lean_nat_add(v___y_1840_, v___y_1841_);
                lean_dec(v___y_1841_);
                lean_dec(v___y_1840_);
                if v_isShared_1835_ == 0 {
                    lean_ctor_set(v___x_1834_, 4, v_r_1812_);
                    lean_ctor_set(v___x_1834_, 3, v_r_1828_);
                    lean_ctor_set(v___x_1834_, 2, v_v_1810_);
                    lean_ctor_set(v___x_1834_, 1, v_k_1809_);
                    lean_ctor_set(v___x_1834_, 0, v___x_1842_);
                    v___x_1844_ = v___x_1834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1842_);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_k_1809_);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_v_1810_);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_r_1828_);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_r_1812_);
                    v___x_1844_ = v_reuseFailAlloc_1848_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1823_ == 0 {
                    lean_ctor_set(v___x_1822_, 4, v___x_1844_);
                    lean_ctor_set(v___x_1822_, 3, v___y_1839_);
                    lean_ctor_set(v___x_1822_, 2, v_v_1826_);
                    lean_ctor_set(v___x_1822_, 1, v_k_1825_);
                    lean_ctor_set(v___x_1822_, 0, v___x_1837_);
                    v___x_1846_ = v___x_1822_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_k_1825_);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_v_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 3, v___y_1839_);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 4, v___x_1844_);
                    v___x_1846_ = v_reuseFailAlloc_1847_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1846_;
            }
            8 => {
                v___x_1851_ = lean_nat_add(v___x_1836_, v___y_1850_);
                lean_dec(v___y_1850_);
                lean_dec(v___x_1836_);
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v_l_1827_);
                    lean_ctor_set(v___x_1801_, 0, v___x_1851_);
                    v___x_1853_ = v___x_1801_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1798_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_l_1827_);
                    v___x_1853_ = v_reuseFailAlloc_1857_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1854_ = lean_nat_add(v___x_1806_, v_size_1829_);
                if lean_obj_tag(v_r_1828_) == 0 {
                    v_size_1855_ = lean_ctor_get(v_r_1828_, 0);
                    lean_inc(v_size_1855_);
                    v___y_1839_ = v___x_1853_;
                    v___y_1840_ = v___x_1854_;
                    v___y_1841_ = v_size_1855_;
                    state = 5;
                    continue;
                } else {
                    v___x_1856_ = lean_unsigned_to_nat(0);
                    v___y_1839_ = v___x_1853_;
                    v___y_1840_ = v___x_1854_;
                    v___y_1841_ = v___x_1856_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1877_ = (!lean_is_exclusive(v_l_1798_)) as u8;
                if v_isSharedCheck_1877_ == 0 {
                    v_unused_1878_ = lean_ctor_get(v_l_1798_, 4);
                    lean_dec(v_unused_1878_);
                    v_unused_1879_ = lean_ctor_get(v_l_1798_, 3);
                    lean_dec(v_unused_1879_);
                    v_unused_1880_ = lean_ctor_get(v_l_1798_, 2);
                    lean_dec(v_unused_1880_);
                    v_unused_1881_ = lean_ctor_get(v_l_1798_, 1);
                    lean_dec(v_unused_1881_);
                    v_unused_1882_ = lean_ctor_get(v_l_1798_, 0);
                    lean_dec(v_unused_1882_);
                    v___x_1872_ = v_l_1798_;
                    v_isShared_1873_ = v_isSharedCheck_1877_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_1798_);
                    v___x_1872_ = lean_box(0);
                    v_isShared_1873_ = v_isSharedCheck_1877_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1873_ == 0 {
                    lean_ctor_set(v___x_1872_, 4, v_r_1812_);
                    lean_ctor_set(v___x_1872_, 3, v___x_1870_);
                    lean_ctor_set(v___x_1872_, 2, v_v_1810_);
                    lean_ctor_set(v___x_1872_, 1, v_k_1809_);
                    lean_ctor_set(v___x_1872_, 0, v___x_1867_);
                    v___x_1875_ = v___x_1872_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1867_);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1809_);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1810_);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 3, v___x_1870_);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_r_1812_);
                    v___x_1875_ = v_reuseFailAlloc_1876_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1875_;
            }
            13 => {
                v_k_1897_ = lean_ctor_get(v_l_1890_, 1);
                v_v_1898_ = lean_ctor_get(v_l_1890_, 2);
                v_isSharedCheck_1912_ = (!lean_is_exclusive(v_l_1890_)) as u8;
                if v_isSharedCheck_1912_ == 0 {
                    v_unused_1913_ = lean_ctor_get(v_l_1890_, 4);
                    lean_dec(v_unused_1913_);
                    v_unused_1914_ = lean_ctor_get(v_l_1890_, 3);
                    lean_dec(v_unused_1914_);
                    v_unused_1915_ = lean_ctor_get(v_l_1890_, 0);
                    lean_dec(v_unused_1915_);
                    v___x_1900_ = v_l_1890_;
                    v_isShared_1901_ = v_isSharedCheck_1912_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_1898_);
                    lean_inc(v_k_1897_);
                    lean_dec(v_l_1890_);
                    v___x_1900_ = lean_box(0);
                    v_isShared_1901_ = v_isSharedCheck_1912_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1902_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1891_, 2);
                if v_isShared_1901_ == 0 {
                    lean_ctor_set(v___x_1900_, 4, v_r_1891_);
                    lean_ctor_set(v___x_1900_, 3, v_r_1891_);
                    lean_ctor_set(v___x_1900_, 2, v_v_1797_);
                    lean_ctor_set(v___x_1900_, 1, v_k_1796_);
                    lean_ctor_set(v___x_1900_, 0, v___x_1806_);
                    v___x_1904_ = v___x_1900_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1806_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_r_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_r_1891_);
                    v___x_1904_ = v_reuseFailAlloc_1911_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_1891_);
                if v_isShared_1896_ == 0 {
                    lean_ctor_set(v___x_1895_, 3, v_r_1891_);
                    lean_ctor_set(v___x_1895_, 0, v___x_1806_);
                    v___x_1906_ = v___x_1895_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1806_);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_k_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_v_1893_);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_r_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_r_1891_);
                    v___x_1906_ = v_reuseFailAlloc_1910_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v___x_1906_);
                    lean_ctor_set(v___x_1801_, 3, v___x_1904_);
                    lean_ctor_set(v___x_1801_, 2, v_v_1898_);
                    lean_ctor_set(v___x_1801_, 1, v_k_1897_);
                    lean_ctor_set(v___x_1801_, 0, v___x_1902_);
                    v___x_1908_ = v___x_1801_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_k_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_v_1898_);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 3, v___x_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 4, v___x_1906_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1908_;
            }
            18 => {
                v___x_1925_ = lean_unsigned_to_nat(3);
                if v_isShared_1924_ == 0 {
                    lean_ctor_set(v___x_1923_, 4, v_l_1890_);
                    lean_ctor_set(v___x_1923_, 2, v_v_1797_);
                    lean_ctor_set(v___x_1923_, 1, v_k_1796_);
                    lean_ctor_set(v___x_1923_, 0, v___x_1806_);
                    v___x_1927_ = v___x_1923_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1806_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_l_1890_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1890_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v_r_1919_);
                    lean_ctor_set(v___x_1801_, 3, v___x_1927_);
                    lean_ctor_set(v___x_1801_, 2, v_v_1921_);
                    lean_ctor_set(v___x_1801_, 1, v_k_1920_);
                    lean_ctor_set(v___x_1801_, 0, v___x_1925_);
                    v___x_1929_ = v___x_1801_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1925_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1920_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1921_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 3, v___x_1927_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_r_1919_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1929_;
            }
            21 => {
                return v___x_1938_;
            }
            22 => {
                return v___x_1941_;
            }
            23 => {
                return v___x_1957_;
            }
            24 => {
                v_size_1962_ = lean_ctor_get(v_l_1949_, 0);
                v_size_1963_ = lean_ctor_get(v_r_1950_, 0);
                v_k_1964_ = lean_ctor_get(v_r_1950_, 1);
                v_v_1965_ = lean_ctor_get(v_r_1950_, 2);
                v_l_1966_ = lean_ctor_get(v_r_1950_, 3);
                v_r_1967_ = lean_ctor_get(v_r_1950_, 4);
                v___x_1968_ = lean_unsigned_to_nat(2);
                v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1962_);
                v___x_1970_ = lean_nat_dec_lt(v_size_1963_, v___x_1969_);
                lean_dec(v___x_1969_);
                if v___x_1970_ == 0 {
                    lean_inc(v_r_1967_);
                    lean_inc(v_l_1966_);
                    lean_inc(v_v_1965_);
                    lean_inc(v_k_1964_);
                    v_isSharedCheck_1999_ = (!lean_is_exclusive(v_r_1950_)) as u8;
                    if v_isSharedCheck_1999_ == 0 {
                        v_unused_2000_ = lean_ctor_get(v_r_1950_, 4);
                        lean_dec(v_unused_2000_);
                        v_unused_2001_ = lean_ctor_get(v_r_1950_, 3);
                        lean_dec(v_unused_2001_);
                        v_unused_2002_ = lean_ctor_get(v_r_1950_, 2);
                        lean_dec(v_unused_2002_);
                        v_unused_2003_ = lean_ctor_get(v_r_1950_, 1);
                        lean_dec(v_unused_2003_);
                        v_unused_2004_ = lean_ctor_get(v_r_1950_, 0);
                        lean_dec(v_unused_2004_);
                        v___x_1972_ = v_r_1950_;
                        v_isShared_1973_ = v_isSharedCheck_1999_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_1950_);
                        v___x_1972_ = lean_box(0);
                        v_isShared_1973_ = v_isSharedCheck_1999_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1801_);
                    v___x_2005_ = lean_nat_add(v___x_1944_, v_size_1946_);
                    lean_dec(v_size_1946_);
                    v___x_2006_ = lean_nat_add(v___x_2005_, v_size_1945_);
                    lean_dec(v___x_2005_);
                    v___x_2007_ = lean_nat_add(v___x_1944_, v_size_1945_);
                    v___x_2008_ = lean_nat_add(v___x_2007_, v_size_1963_);
                    lean_dec(v___x_2007_);
                    lean_inc_ref(v_r_1799_);
                    if v_isShared_1961_ == 0 {
                        lean_ctor_set(v___x_1960_, 4, v_r_1799_);
                        lean_ctor_set(v___x_1960_, 3, v_r_1950_);
                        lean_ctor_set(v___x_1960_, 2, v_v_1797_);
                        lean_ctor_set(v___x_1960_, 1, v_k_1796_);
                        lean_ctor_set(v___x_1960_, 0, v___x_2008_);
                        v___x_2010_ = v___x_1960_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2008_);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_1796_);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_1797_);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_r_1950_);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_r_1799_);
                        v___x_2010_ = v_reuseFailAlloc_2023_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1974_ = lean_nat_add(v___x_1944_, v_size_1946_);
                lean_dec(v_size_1946_);
                v___x_1975_ = lean_nat_add(v___x_1974_, v_size_1945_);
                lean_dec(v___x_1974_);
                v___x_1987_ = lean_nat_add(v___x_1944_, v_size_1962_);
                if lean_obj_tag(v_l_1966_) == 0 {
                    v_size_1997_ = lean_ctor_get(v_l_1966_, 0);
                    lean_inc(v_size_1997_);
                    v___y_1989_ = v_size_1997_;
                    state = 29;
                    continue;
                } else {
                    v___x_1998_ = lean_unsigned_to_nat(0);
                    v___y_1989_ = v___x_1998_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1980_ = lean_nat_add(v___y_1977_, v___y_1979_);
                lean_dec(v___y_1979_);
                lean_dec(v___y_1977_);
                if v_isShared_1973_ == 0 {
                    lean_ctor_set(v___x_1972_, 4, v_r_1799_);
                    lean_ctor_set(v___x_1972_, 3, v_r_1967_);
                    lean_ctor_set(v___x_1972_, 2, v_v_1797_);
                    lean_ctor_set(v___x_1972_, 1, v_k_1796_);
                    lean_ctor_set(v___x_1972_, 0, v___x_1980_);
                    v___x_1982_ = v___x_1972_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1980_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_r_1967_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_r_1799_);
                    v___x_1982_ = v_reuseFailAlloc_1986_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1961_ == 0 {
                    lean_ctor_set(v___x_1960_, 4, v___x_1982_);
                    lean_ctor_set(v___x_1960_, 3, v___y_1978_);
                    lean_ctor_set(v___x_1960_, 2, v_v_1965_);
                    lean_ctor_set(v___x_1960_, 1, v_k_1964_);
                    lean_ctor_set(v___x_1960_, 0, v___x_1975_);
                    v___x_1984_ = v___x_1960_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1975_);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1965_);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 3, v___y_1978_);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 4, v___x_1982_);
                    v___x_1984_ = v_reuseFailAlloc_1985_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1984_;
            }
            29 => {
                v___x_1990_ = lean_nat_add(v___x_1987_, v___y_1989_);
                lean_dec(v___y_1989_);
                lean_dec(v___x_1987_);
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v_l_1966_);
                    lean_ctor_set(v___x_1801_, 3, v_l_1949_);
                    lean_ctor_set(v___x_1801_, 2, v_v_1948_);
                    lean_ctor_set(v___x_1801_, 1, v_k_1947_);
                    lean_ctor_set(v___x_1801_, 0, v___x_1990_);
                    v___x_1992_ = v___x_1801_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1990_);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1947_);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1948_);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_l_1949_);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_l_1966_);
                    v___x_1992_ = v_reuseFailAlloc_1996_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1993_ = lean_nat_add(v___x_1944_, v_size_1945_);
                if lean_obj_tag(v_r_1967_) == 0 {
                    v_size_1994_ = lean_ctor_get(v_r_1967_, 0);
                    lean_inc(v_size_1994_);
                    v___y_1977_ = v___x_1993_;
                    v___y_1978_ = v___x_1992_;
                    v___y_1979_ = v_size_1994_;
                    state = 26;
                    continue;
                } else {
                    v___x_1995_ = lean_unsigned_to_nat(0);
                    v___y_1977_ = v___x_1993_;
                    v___y_1978_ = v___x_1992_;
                    v___y_1979_ = v___x_1995_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2017_ = (!lean_is_exclusive(v_r_1799_)) as u8;
                if v_isSharedCheck_2017_ == 0 {
                    v_unused_2018_ = lean_ctor_get(v_r_1799_, 4);
                    lean_dec(v_unused_2018_);
                    v_unused_2019_ = lean_ctor_get(v_r_1799_, 3);
                    lean_dec(v_unused_2019_);
                    v_unused_2020_ = lean_ctor_get(v_r_1799_, 2);
                    lean_dec(v_unused_2020_);
                    v_unused_2021_ = lean_ctor_get(v_r_1799_, 1);
                    lean_dec(v_unused_2021_);
                    v_unused_2022_ = lean_ctor_get(v_r_1799_, 0);
                    lean_dec(v_unused_2022_);
                    v___x_2012_ = v_r_1799_;
                    v_isShared_2013_ = v_isSharedCheck_2017_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_1799_);
                    v___x_2012_ = lean_box(0);
                    v_isShared_2013_ = v_isSharedCheck_2017_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2013_ == 0 {
                    lean_ctor_set(v___x_2012_, 4, v___x_2010_);
                    lean_ctor_set(v___x_2012_, 3, v_l_1949_);
                    lean_ctor_set(v___x_2012_, 2, v_v_1948_);
                    lean_ctor_set(v___x_2012_, 1, v_k_1947_);
                    lean_ctor_set(v___x_2012_, 0, v___x_2006_);
                    v___x_2015_ = v___x_2012_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1947_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1948_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_l_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 4, v___x_2010_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2015_;
            }
            34 => {
                v___x_2037_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_2031_);
                if v_isShared_2036_ == 0 {
                    lean_ctor_set(v___x_2035_, 3, v_r_2031_);
                    lean_ctor_set(v___x_2035_, 2, v_v_1797_);
                    lean_ctor_set(v___x_2035_, 1, v_k_1796_);
                    lean_ctor_set(v___x_2035_, 0, v___x_1944_);
                    v___x_2039_ = v___x_2035_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_1944_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_r_2031_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 4, v_r_2031_);
                    v___x_2039_ = v_reuseFailAlloc_2043_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v___x_2039_);
                    lean_ctor_set(v___x_1801_, 3, v_l_2030_);
                    lean_ctor_set(v___x_1801_, 2, v_v_2033_);
                    lean_ctor_set(v___x_1801_, 1, v_k_2032_);
                    lean_ctor_set(v___x_1801_, 0, v___x_2037_);
                    v___x_2041_ = v___x_1801_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2037_);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_k_2032_);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_v_2033_);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_l_2030_);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2041_;
            }
            37 => {
                v_k_2053_ = lean_ctor_get(v_r_2047_, 1);
                v_v_2054_ = lean_ctor_get(v_r_2047_, 2);
                v_isSharedCheck_2068_ = (!lean_is_exclusive(v_r_2047_)) as u8;
                if v_isSharedCheck_2068_ == 0 {
                    v_unused_2069_ = lean_ctor_get(v_r_2047_, 4);
                    lean_dec(v_unused_2069_);
                    v_unused_2070_ = lean_ctor_get(v_r_2047_, 3);
                    lean_dec(v_unused_2070_);
                    v_unused_2071_ = lean_ctor_get(v_r_2047_, 0);
                    lean_dec(v_unused_2071_);
                    v___x_2056_ = v_r_2047_;
                    v_isShared_2057_ = v_isSharedCheck_2068_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_2054_);
                    lean_inc(v_k_2053_);
                    lean_dec(v_r_2047_);
                    v___x_2056_ = lean_box(0);
                    v_isShared_2057_ = v_isSharedCheck_2068_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_2058_ = lean_unsigned_to_nat(3);
                if v_isShared_2057_ == 0 {
                    lean_ctor_set(v___x_2056_, 4, v_l_2030_);
                    lean_ctor_set(v___x_2056_, 3, v_l_2030_);
                    lean_ctor_set(v___x_2056_, 2, v_v_2049_);
                    lean_ctor_set(v___x_2056_, 1, v_k_2048_);
                    lean_ctor_set(v___x_2056_, 0, v___x_1944_);
                    v___x_2060_ = v___x_2056_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_1944_);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2048_);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2049_);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_l_2030_);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 4, v_l_2030_);
                    v___x_2060_ = v_reuseFailAlloc_2067_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_2052_ == 0 {
                    lean_ctor_set(v___x_2051_, 4, v_l_2030_);
                    lean_ctor_set(v___x_2051_, 2, v_v_1797_);
                    lean_ctor_set(v___x_2051_, 1, v_k_1796_);
                    lean_ctor_set(v___x_2051_, 0, v___x_1944_);
                    v___x_2062_ = v___x_2051_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_1944_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_1796_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_1797_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_l_2030_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_l_2030_);
                    v___x_2062_ = v_reuseFailAlloc_2066_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v___x_2062_);
                    lean_ctor_set(v___x_1801_, 3, v___x_2060_);
                    lean_ctor_set(v___x_1801_, 2, v_v_2054_);
                    lean_ctor_set(v___x_1801_, 1, v_k_2053_);
                    lean_ctor_set(v___x_1801_, 0, v___x_2058_);
                    v___x_2064_ = v___x_1801_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2058_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_2053_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_2054_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 3, v___x_2060_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 4, v___x_2062_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2064_;
            }
            42 => {
                return v___x_2078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_UniqueIds_checkId(
    mut v_id_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2085_: u8 = 0;
    v___x_2085_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(
            v_id_2083_, v_a_2084_,
        );
    if v___x_2085_ == 0 {
        let mut v___x_2086_: u8 = 0;
        v___x_2086_ = 1;
        if v___x_2085_ == 0 {
            let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
            v___x_2087_ = lean_box(0);
            v___x_2088_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_id_2083_, v___x_2087_, v_a_2084_);
            v___x_2089_ = lean_box((v___x_2086_) as usize);
            v___x_2090_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2090_, 0, v___x_2089_);
            lean_ctor_set(v___x_2090_, 1, v___x_2088_);
            return v___x_2090_;
        } else {
            let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_id_2083_);
            v___x_2091_ = lean_box((v___x_2086_) as usize);
            v___x_2092_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2092_, 0, v___x_2091_);
            lean_ctor_set(v___x_2092_, 1, v_a_2084_);
            return v___x_2092_;
        }
    } else {
        let mut v___x_2093_: u8 = 0;
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_id_2083_);
        v___x_2093_ = 0;
        v___x_2094_ = lean_box((v___x_2093_) as usize);
        v___x_2095_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2095_, 0, v___x_2094_);
        lean_ctor_set(v___x_2095_, 1, v_a_2084_);
        return v___x_2095_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(
    mut v_00_u03b2_2096_: *mut LeanObject,
    mut v_k_2097_: *mut LeanObject,
    mut v_t_2098_: *mut LeanObject,
) -> u8 {
    let mut v___x_2099_: u8 = 0;
    v___x_2099_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(
            v_k_2097_, v_t_2098_,
        );
    return v___x_2099_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(
    mut v_00_u03b2_2100_: *mut LeanObject,
    mut v_k_2101_: *mut LeanObject,
    mut v_t_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2103_: u8 = 0;
    let mut v_r_2104_: *mut LeanObject = core::ptr::null_mut();
    v_res_2103_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(
        v_00_u03b2_2100_,
        v_k_2101_,
        v_t_2102_,
    );
    lean_dec(v_t_2102_);
    lean_dec(v_k_2101_);
    v_r_2104_ = lean_box((v_res_2103_) as usize);
    return v_r_2104_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(
    mut v_00_u03b2_2105_: *mut LeanObject,
    mut v_k_2106_: *mut LeanObject,
    mut v_v_2107_: *mut LeanObject,
    mut v_t_2108_: *mut LeanObject,
    mut v_hl_2109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    v___x_2110_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(
            v_k_2106_, v_v_2107_, v_t_2108_,
        );
    return v___x_2110_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(
    mut v_as_2111_: *mut LeanObject,
    mut v_i_2112_: usize,
    mut v_stop_2113_: usize,
    mut v___y_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: u8 = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: usize = 0;
    let mut v___x_2131_: usize = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2115_ = lean_usize_dec_eq(v_i_2112_, v_stop_2113_);
                if v___x_2115_ == 0 {
                    v___x_2116_ = lean_array_uget_borrowed(v_as_2111_, v_i_2112_);
                    v_x_2117_ = lean_ctor_get(v___x_2116_, 0);
                    lean_inc(v_x_2117_);
                    v___x_2118_ = l_Lean_IR_UniqueIds_checkId(v_x_2117_, v___y_2114_);
                    v_fst_2119_ = lean_ctor_get(v___x_2118_, 0);
                    v_snd_2120_ = lean_ctor_get(v___x_2118_, 1);
                    v_isSharedCheck_2137_ = (!lean_is_exclusive(v___x_2118_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2122_ = v___x_2118_;
                        v_isShared_2123_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2120_);
                        lean_inc(v_fst_2119_);
                        lean_dec(v___x_2118_);
                        v___x_2122_ = lean_box(0);
                        v_isShared_2123_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2138_ = 0;
                    v___x_2139_ = lean_box((v___x_2138_) as usize);
                    v___x_2140_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2140_, 0, v___x_2139_);
                    lean_ctor_set(v___x_2140_, 1, v___y_2114_);
                    return v___x_2140_;
                }
            }
            1 => {
                v___x_2124_ = 1;
                v___x_2125_ = (lean_unbox(v_fst_2119_) as u8);
                lean_dec(v_fst_2119_);
                if v___x_2125_ == 0 {
                    v___x_2126_ = lean_box((v___x_2124_) as usize);
                    if v_isShared_2123_ == 0 {
                        lean_ctor_set(v___x_2122_, 0, v___x_2126_);
                        v___x_2128_ = v___x_2122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
                        lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_snd_2120_);
                        v___x_2128_ = v_reuseFailAlloc_2129_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_2115_ == 0 {
                        lean_del_object(v___x_2122_);
                        v___x_2130_ = 1usize;
                        v___x_2131_ = lean_usize_add(v_i_2112_, v___x_2130_);
                        v_i_2112_ = v___x_2131_;
                        v___y_2114_ = v_snd_2120_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2133_ = lean_box((v___x_2124_) as usize);
                        if v_isShared_2123_ == 0 {
                            lean_ctor_set(v___x_2122_, 0, v___x_2133_);
                            v___x_2135_ = v___x_2122_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
                            lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_snd_2120_);
                            v___x_2135_ = v_reuseFailAlloc_2136_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2128_;
            }
            3 => {
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(
    mut v_as_2141_: *mut LeanObject,
    mut v_i_2142_: *mut LeanObject,
    mut v_stop_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2145_: usize = 0;
    let mut v_stop_boxed_2146_: usize = 0;
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2145_ = lean_unbox_usize(v_i_2142_);
    lean_dec(v_i_2142_);
    v_stop_boxed_2146_ = lean_unbox_usize(v_stop_2143_);
    lean_dec(v_stop_2143_);
    v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_as_2141_, v_i_boxed_2145_, v_stop_boxed_2146_, v___y_2144_);
    lean_dec_ref(v_as_2141_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_IR_UniqueIds_checkParams(
    mut v_ps_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v_snd_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2155_ = lean_unsigned_to_nat(0);
                v___x_2156_ = lean_array_get_size(v_ps_2148_);
                v___x_2157_ = lean_nat_dec_lt(v___x_2155_, v___x_2156_);
                if v___x_2157_ == 0 {
                    v___y_2151_ = v_a_2149_;
                    state = 1;
                    continue;
                } else {
                    if v___x_2157_ == 0 {
                        v___y_2151_ = v_a_2149_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2158_ = 0usize;
                        v___x_2159_ = lean_usize_of_nat(v___x_2156_);
                        v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_ps_2148_, v___x_2158_, v___x_2159_, v_a_2149_);
                        v_fst_2161_ = lean_ctor_get(v___x_2160_, 0);
                        lean_inc(v_fst_2161_);
                        v___x_2162_ = (lean_unbox(v_fst_2161_) as u8);
                        lean_dec(v_fst_2161_);
                        if v___x_2162_ == 0 {
                            v_snd_2163_ = lean_ctor_get(v___x_2160_, 1);
                            lean_inc(v_snd_2163_);
                            lean_dec_ref(v___x_2160_);
                            v___y_2151_ = v_snd_2163_;
                            state = 1;
                            continue;
                        } else {
                            v_snd_2164_ = lean_ctor_get(v___x_2160_, 1);
                            v_isSharedCheck_2173_ = (!lean_is_exclusive(v___x_2160_)) as u8;
                            if v_isSharedCheck_2173_ == 0 {
                                v_unused_2174_ = lean_ctor_get(v___x_2160_, 0);
                                lean_dec(v_unused_2174_);
                                v___x_2166_ = v___x_2160_;
                                v_isShared_2167_ = v_isSharedCheck_2173_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_snd_2164_);
                                lean_dec(v___x_2160_);
                                v___x_2166_ = lean_box(0);
                                v_isShared_2167_ = v_isSharedCheck_2173_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2152_ = 1;
                v___x_2153_ = lean_box((v___x_2152_) as usize);
                v___x_2154_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2154_, 0, v___x_2153_);
                lean_ctor_set(v___x_2154_, 1, v___y_2151_);
                return v___x_2154_;
            }
            2 => {
                v___x_2168_ = 0;
                v___x_2169_ = lean_box((v___x_2168_) as usize);
                if v_isShared_2167_ == 0 {
                    lean_ctor_set(v___x_2166_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_snd_2164_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_UniqueIds_checkParams___boxed(
    mut v_ps_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2177_: *mut LeanObject = core::ptr::null_mut();
    v_res_2177_ = l_Lean_IR_UniqueIds_checkParams(v_ps_2175_, v_a_2176_);
    lean_dec_ref(v_ps_2175_);
    return v_res_2177_;
}
pub unsafe fn l_Lean_IR_UniqueIds_checkFnBody(
    mut v_x_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v_snd_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: u8 = 0;
    let mut v_snd_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u8 = 0;
    let mut v_snd_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2208_: usize = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v_snd_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut v_unused_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2178_) {
                0 => {
                    v_x_2185_ = lean_ctor_get(v_x_2178_, 0);
                    lean_inc(v_x_2185_);
                    v_b_2186_ = lean_ctor_get(v_x_2178_, 3);
                    lean_inc(v_b_2186_);
                    lean_dec_ref_known(v_x_2178_, 4);
                    v___x_2187_ = l_Lean_IR_UniqueIds_checkId(v_x_2185_, v_a_2179_);
                    v_fst_2188_ = lean_ctor_get(v___x_2187_, 0);
                    lean_inc(v_fst_2188_);
                    v___x_2189_ = (lean_unbox(v_fst_2188_) as u8);
                    lean_dec(v_fst_2188_);
                    if v___x_2189_ == 0 {
                        lean_dec(v_b_2186_);
                        return v___x_2187_;
                    } else {
                        v_snd_2190_ = lean_ctor_get(v___x_2187_, 1);
                        lean_inc(v_snd_2190_);
                        lean_dec_ref(v___x_2187_);
                        v_x_2178_ = v_b_2186_;
                        v_a_2179_ = v_snd_2190_;
                        state = 0;
                        continue;
                    }
                }
                1 => {
                    v_j_2192_ = lean_ctor_get(v_x_2178_, 0);
                    lean_inc(v_j_2192_);
                    v_xs_2193_ = lean_ctor_get(v_x_2178_, 1);
                    lean_inc_ref(v_xs_2193_);
                    v_b_2194_ = lean_ctor_get(v_x_2178_, 3);
                    lean_inc(v_b_2194_);
                    lean_dec_ref_known(v_x_2178_, 4);
                    v___x_2195_ = l_Lean_IR_UniqueIds_checkId(v_j_2192_, v_a_2179_);
                    v_fst_2196_ = lean_ctor_get(v___x_2195_, 0);
                    lean_inc(v_fst_2196_);
                    v___x_2197_ = (lean_unbox(v_fst_2196_) as u8);
                    lean_dec(v_fst_2196_);
                    if v___x_2197_ == 0 {
                        lean_dec(v_b_2194_);
                        lean_dec_ref(v_xs_2193_);
                        return v___x_2195_;
                    } else {
                        v_snd_2198_ = lean_ctor_get(v___x_2195_, 1);
                        lean_inc(v_snd_2198_);
                        lean_dec_ref(v___x_2195_);
                        v___x_2199_ = l_Lean_IR_UniqueIds_checkParams(v_xs_2193_, v_snd_2198_);
                        lean_dec_ref(v_xs_2193_);
                        v_fst_2200_ = lean_ctor_get(v___x_2199_, 0);
                        lean_inc(v_fst_2200_);
                        v___x_2201_ = (lean_unbox(v_fst_2200_) as u8);
                        lean_dec(v_fst_2200_);
                        if v___x_2201_ == 0 {
                            lean_dec(v_b_2194_);
                            return v___x_2199_;
                        } else {
                            v_snd_2202_ = lean_ctor_get(v___x_2199_, 1);
                            lean_inc(v_snd_2202_);
                            lean_dec_ref(v___x_2199_);
                            v_x_2178_ = v_b_2194_;
                            v_a_2179_ = v_snd_2202_;
                            state = 0;
                            continue;
                        }
                    }
                }
                9 => {
                    v_cs_2204_ = lean_ctor_get(v_x_2178_, 3);
                    lean_inc_ref(v_cs_2204_);
                    lean_dec_ref_known(v_x_2178_, 4);
                    v___x_2205_ = lean_unsigned_to_nat(0);
                    v___x_2206_ = lean_array_get_size(v_cs_2204_);
                    v___x_2207_ = lean_nat_dec_lt(v___x_2205_, v___x_2206_);
                    if v___x_2207_ == 0 {
                        lean_dec_ref(v_cs_2204_);
                        v___y_2181_ = v_a_2179_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_2207_ == 0 {
                            lean_dec_ref(v_cs_2204_);
                            v___y_2181_ = v_a_2179_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2208_ = 0usize;
                            v___x_2209_ = lean_usize_of_nat(v___x_2206_);
                            v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_2204_, v___x_2208_, v___x_2209_, v_a_2179_);
                            lean_dec_ref(v_cs_2204_);
                            v_fst_2211_ = lean_ctor_get(v___x_2210_, 0);
                            lean_inc(v_fst_2211_);
                            v___x_2212_ = (lean_unbox(v_fst_2211_) as u8);
                            lean_dec(v_fst_2211_);
                            if v___x_2212_ == 0 {
                                v_snd_2213_ = lean_ctor_get(v___x_2210_, 1);
                                lean_inc(v_snd_2213_);
                                lean_dec_ref(v___x_2210_);
                                v___y_2181_ = v_snd_2213_;
                                state = 1;
                                continue;
                            } else {
                                v_snd_2214_ = lean_ctor_get(v___x_2210_, 1);
                                v_isSharedCheck_2223_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                                if v_isSharedCheck_2223_ == 0 {
                                    v_unused_2224_ = lean_ctor_get(v___x_2210_, 0);
                                    lean_dec(v_unused_2224_);
                                    v___x_2216_ = v___x_2210_;
                                    v_isShared_2217_ = v_isSharedCheck_2223_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_snd_2214_);
                                    lean_dec(v___x_2210_);
                                    v___x_2216_ = lean_box(0);
                                    v_isShared_2217_ = v_isSharedCheck_2223_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {
                    v___x_2225_ = l_Lean_IR_FnBody_isTerminal(v_x_2178_);
                    if v___x_2225_ == 0 {
                        v___x_2226_ = l_Lean_IR_FnBody_body(v_x_2178_);
                        lean_dec(v_x_2178_);
                        v_x_2178_ = v___x_2226_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_x_2178_);
                        v___x_2228_ = lean_box((v___x_2225_) as usize);
                        v___x_2229_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2229_, 0, v___x_2228_);
                        lean_ctor_set(v___x_2229_, 1, v_a_2179_);
                        return v___x_2229_;
                    }
                }
            },
            1 => {
                v___x_2182_ = 1;
                v___x_2183_ = lean_box((v___x_2182_) as usize);
                v___x_2184_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                lean_ctor_set(v___x_2184_, 1, v___y_2181_);
                return v___x_2184_;
            }
            2 => {
                v___x_2218_ = 0;
                v___x_2219_ = lean_box((v___x_2218_) as usize);
                if v_isShared_2217_ == 0 {
                    lean_ctor_set(v___x_2216_, 0, v___x_2219_);
                    v___x_2221_ = v___x_2216_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_snd_2214_);
                    v___x_2221_ = v_reuseFailAlloc_2222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(
    mut v_as_2230_: *mut LeanObject,
    mut v_i_2231_: usize,
    mut v_stop_2232_: usize,
    mut v___y_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: usize = 0;
    let mut v___x_2250_: usize = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2234_ = lean_usize_dec_eq(v_i_2231_, v_stop_2232_);
                if v___x_2234_ == 0 {
                    v___x_2235_ = lean_array_uget_borrowed(v_as_2230_, v_i_2231_);
                    v___x_2236_ = l_Lean_IR_Alt_body(v___x_2235_);
                    v___x_2237_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_2236_, v___y_2233_);
                    v_fst_2238_ = lean_ctor_get(v___x_2237_, 0);
                    v_snd_2239_ = lean_ctor_get(v___x_2237_, 1);
                    v_isSharedCheck_2256_ = (!lean_is_exclusive(v___x_2237_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v___x_2241_ = v___x_2237_;
                        v_isShared_2242_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2239_);
                        lean_inc(v_fst_2238_);
                        lean_dec(v___x_2237_);
                        v___x_2241_ = lean_box(0);
                        v_isShared_2242_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2257_ = 0;
                    v___x_2258_ = lean_box((v___x_2257_) as usize);
                    v___x_2259_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2259_, 0, v___x_2258_);
                    lean_ctor_set(v___x_2259_, 1, v___y_2233_);
                    return v___x_2259_;
                }
            }
            1 => {
                v___x_2243_ = 1;
                v___x_2244_ = (lean_unbox(v_fst_2238_) as u8);
                lean_dec(v_fst_2238_);
                if v___x_2244_ == 0 {
                    v___x_2245_ = lean_box((v___x_2243_) as usize);
                    if v_isShared_2242_ == 0 {
                        lean_ctor_set(v___x_2241_, 0, v___x_2245_);
                        v___x_2247_ = v___x_2241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_snd_2239_);
                        v___x_2247_ = v_reuseFailAlloc_2248_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_2234_ == 0 {
                        lean_del_object(v___x_2241_);
                        v___x_2249_ = 1usize;
                        v___x_2250_ = lean_usize_add(v_i_2231_, v___x_2249_);
                        v_i_2231_ = v___x_2250_;
                        v___y_2233_ = v_snd_2239_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2252_ = lean_box((v___x_2243_) as usize);
                        if v_isShared_2242_ == 0 {
                            lean_ctor_set(v___x_2241_, 0, v___x_2252_);
                            v___x_2254_ = v___x_2241_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
                            lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_snd_2239_);
                            v___x_2254_ = v_reuseFailAlloc_2255_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2247_;
            }
            3 => {
                return v___x_2254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(
    mut v_as_2260_: *mut LeanObject,
    mut v_i_2261_: *mut LeanObject,
    mut v_stop_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2264_: usize = 0;
    let mut v_stop_boxed_2265_: usize = 0;
    let mut v_res_2266_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
    lean_dec(v_i_2261_);
    v_stop_boxed_2265_ = lean_unbox_usize(v_stop_2262_);
    lean_dec(v_stop_2262_);
    v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_2260_, v_i_boxed_2264_, v_stop_boxed_2265_, v___y_2263_);
    lean_dec_ref(v_as_2260_);
    return v_res_2266_;
}
pub unsafe fn l_Lean_IR_UniqueIds_checkDecl(
    mut v_x_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2267_) == 0 {
        let mut v_xs_2269_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: u8 = 0;
        v_xs_2269_ = lean_ctor_get(v_x_2267_, 1);
        lean_inc_ref(v_xs_2269_);
        v_body_2270_ = lean_ctor_get(v_x_2267_, 3);
        lean_inc(v_body_2270_);
        lean_dec_ref_known(v_x_2267_, 5);
        v___x_2271_ = l_Lean_IR_UniqueIds_checkParams(v_xs_2269_, v_a_2268_);
        lean_dec_ref(v_xs_2269_);
        v_fst_2272_ = lean_ctor_get(v___x_2271_, 0);
        lean_inc(v_fst_2272_);
        v___x_2273_ = (lean_unbox(v_fst_2272_) as u8);
        lean_dec(v_fst_2272_);
        if v___x_2273_ == 0 {
            lean_dec(v_body_2270_);
            return v___x_2271_;
        } else {
            let mut v_snd_2274_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
            v_snd_2274_ = lean_ctor_get(v___x_2271_, 1);
            lean_inc(v_snd_2274_);
            lean_dec_ref(v___x_2271_);
            v___x_2275_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_2270_, v_snd_2274_);
            return v___x_2275_;
        }
    } else {
        let mut v_xs_2276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
        v_xs_2276_ = lean_ctor_get(v_x_2267_, 1);
        lean_inc_ref(v_xs_2276_);
        lean_dec_ref_known(v_x_2267_, 4);
        v___x_2277_ = l_Lean_IR_UniqueIds_checkParams(v_xs_2276_, v_a_2268_);
        lean_dec_ref(v_xs_2276_);
        return v___x_2277_;
    }
}
pub unsafe fn l_Lean_IR_Decl_uniqueIds(mut v_d_2278_: *mut LeanObject) -> u8 {
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    v___x_2279_ = lean_box(1);
    v___x_2280_ = l_Lean_IR_UniqueIds_checkDecl(v_d_2278_, v___x_2279_);
    v_fst_2281_ = lean_ctor_get(v___x_2280_, 0);
    lean_inc(v_fst_2281_);
    lean_dec_ref(v___x_2280_);
    v___x_2282_ = (lean_unbox(v_fst_2281_) as u8);
    lean_dec(v_fst_2281_);
    return v___x_2282_;
}
pub unsafe fn l_Lean_IR_Decl_uniqueIds___boxed(mut v_d_2283_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2284_: u8 = 0;
    let mut v_r_2285_: *mut LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_Lean_IR_Decl_uniqueIds(v_d_2283_);
    v_r_2285_ = lean_box((v_res_2284_) as usize);
    return v_r_2285_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(
    mut v_t_2286_: *mut LeanObject,
    mut v_k_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2286_) == 0 {
                    v_k_2288_ = lean_ctor_get(v_t_2286_, 1);
                    v_v_2289_ = lean_ctor_get(v_t_2286_, 2);
                    v_l_2290_ = lean_ctor_get(v_t_2286_, 3);
                    v_r_2291_ = lean_ctor_get(v_t_2286_, 4);
                    v___x_2292_ = lean_nat_dec_lt(v_k_2287_, v_k_2288_);
                    if v___x_2292_ == 0 {
                        v___x_2293_ = lean_nat_dec_eq(v_k_2287_, v_k_2288_);
                        if v___x_2293_ == 0 {
                            v_t_2286_ = v_r_2291_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_2289_);
                            v___x_2295_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2295_, 0, v_v_2289_);
                            return v___x_2295_;
                        }
                    } else {
                        v_t_2286_ = v_l_2290_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2297_ = lean_box(0);
                    return v___x_2297_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(
    mut v_t_2298_: *mut LeanObject,
    mut v_k_2299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2300_: *mut LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_2298_, v_k_2299_);
    lean_dec(v_k_2299_);
    lean_dec(v_t_2298_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normIndex(
    mut v_x_2301_: *mut LeanObject,
    mut v_m_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_2302_, v_x_2301_);
    if lean_obj_tag(v___x_2303_) == 0 {
        lean_inc(v_x_2301_);
        return v_x_2301_;
    } else {
        let mut v_val_2304_: *mut LeanObject = core::ptr::null_mut();
        v_val_2304_ = lean_ctor_get(v___x_2303_, 0);
        lean_inc(v_val_2304_);
        lean_dec_ref_known(v___x_2303_, 1);
        return v_val_2304_;
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_normIndex___boxed(
    mut v_x_2305_: *mut LeanObject,
    mut v_m_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2307_: *mut LeanObject = core::ptr::null_mut();
    v_res_2307_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2305_, v_m_2306_);
    lean_dec(v_m_2306_);
    lean_dec(v_x_2305_);
    return v_res_2307_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(
    mut v_00_u03b4_2308_: *mut LeanObject,
    mut v_t_2309_: *mut LeanObject,
    mut v_k_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_2309_, v_k_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(
    mut v_00_u03b4_2312_: *mut LeanObject,
    mut v_t_2313_: *mut LeanObject,
    mut v_k_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(
            v_00_u03b4_2312_,
            v_t_2313_,
            v_k_2314_,
        );
    lean_dec(v_k_2314_);
    lean_dec(v_t_2313_);
    return v_res_2315_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normVar(
    mut v_x_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2316_, v_a_2317_);
    return v___x_2318_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normVar___boxed(
    mut v_x_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2321_: *mut LeanObject = core::ptr::null_mut();
    v_res_2321_ = l_Lean_IR_NormalizeIds_normVar(v_x_2319_, v_a_2320_);
    lean_dec(v_a_2320_);
    lean_dec(v_x_2319_);
    return v_res_2321_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normJP(
    mut v_x_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2322_, v_a_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normJP___boxed(
    mut v_x_2325_: *mut LeanObject,
    mut v_a_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2327_: *mut LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Lean_IR_NormalizeIds_normJP(v_x_2325_, v_a_2326_);
    lean_dec(v_a_2326_);
    lean_dec(v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normArg(
    mut v_x_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2333_: u8 = 0;
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2328_) == 0 {
                    v_id_2330_ = lean_ctor_get(v_x_2328_, 0);
                    v_isSharedCheck_2338_ = (!lean_is_exclusive(v_x_2328_)) as u8;
                    if v_isSharedCheck_2338_ == 0 {
                        v___x_2332_ = v_x_2328_;
                        v_isShared_2333_ = v_isSharedCheck_2338_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_id_2330_);
                        lean_dec(v_x_2328_);
                        v___x_2332_ = lean_box(0);
                        v_isShared_2333_ = v_isSharedCheck_2338_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_2328_;
                }
            }
            1 => {
                v___x_2334_ = l_Lean_IR_NormalizeIds_normIndex(v_id_2330_, v_a_2329_);
                lean_dec(v_id_2330_);
                if v_isShared_2333_ == 0 {
                    lean_ctor_set(v___x_2332_, 0, v___x_2334_);
                    v___x_2336_ = v___x_2332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_normArg___boxed(
    mut v_x_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_IR_NormalizeIds_normArg(v_x_2339_, v_a_2340_);
    lean_dec(v_a_2340_);
    return v_res_2341_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(
    mut v_m_2342_: *mut LeanObject,
    mut v_sz_2343_: usize,
    mut v_i_2344_: usize,
    mut v_bs_2345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2346_: u8 = 0;
    let mut v_v_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_usize_dec_lt(v_i_2344_, v_sz_2343_);
                if v___x_2346_ == 0 {
                    return v_bs_2345_;
                } else {
                    v_v_2347_ = lean_array_uget(v_bs_2345_, v_i_2344_);
                    v___x_2348_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2349_ = lean_array_uset(v_bs_2345_, v_i_2344_, v___x_2348_);
                    v___x_2350_ = l_Lean_IR_NormalizeIds_normArg(v_v_2347_, v_m_2342_);
                    v___x_2351_ = 1usize;
                    v___x_2352_ = lean_usize_add(v_i_2344_, v___x_2351_);
                    v___x_2353_ = lean_array_uset(v_bs_x27_2349_, v_i_2344_, v___x_2350_);
                    v_i_2344_ = v___x_2352_;
                    v_bs_2345_ = v___x_2353_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(
    mut v_m_2355_: *mut LeanObject,
    mut v_sz_2356_: *mut LeanObject,
    mut v_i_2357_: *mut LeanObject,
    mut v_bs_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2359_: usize = 0;
    let mut v_i_boxed_2360_: usize = 0;
    let mut v_res_2361_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2359_ = lean_unbox_usize(v_sz_2356_);
    lean_dec(v_sz_2356_);
    v_i_boxed_2360_ = lean_unbox_usize(v_i_2357_);
    lean_dec(v_i_2357_);
    v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_2355_, v_sz_boxed_2359_, v_i_boxed_2360_, v_bs_2358_);
    lean_dec(v_m_2355_);
    return v_res_2361_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normArgs(
    mut v_as_2362_: *mut LeanObject,
    mut v_m_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2364_: usize = 0;
    let mut v___x_2365_: usize = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    v_sz_2364_ = lean_array_size(v_as_2362_);
    v___x_2365_ = 0usize;
    v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_2363_, v_sz_2364_, v___x_2365_, v_as_2362_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normArgs___boxed(
    mut v_as_2367_: *mut LeanObject,
    mut v_m_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Lean_IR_NormalizeIds_normArgs(v_as_2367_, v_m_2368_);
    lean_dec(v_m_2368_);
    return v_res_2369_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normExpr(
    mut v_x_2370_: *mut LeanObject,
    mut v_x_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_n_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v_x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_2394_: u8 = 0;
    let mut v_ys_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_i_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_i_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut v_n_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v_c_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2445_: u8 = 0;
    let mut v_c_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2455_: u8 = 0;
    let mut v_x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2466_: u8 = 0;
    let mut v_ty_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2370_) {
                0 => {
                    v_i_2372_ = lean_ctor_get(v_x_2370_, 0);
                    v_ys_2373_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2381_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2375_ = v_x_2370_;
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_ys_2373_);
                        lean_inc(v_i_2372_);
                        lean_dec(v_x_2370_);
                        v___x_2375_ = lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_n_2382_ = lean_ctor_get(v_x_2370_, 0);
                    v_x_2383_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2391_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2391_ == 0 {
                        v___x_2385_ = v_x_2370_;
                        v_isShared_2386_ = v_isSharedCheck_2391_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_x_2383_);
                        lean_inc(v_n_2382_);
                        lean_dec(v_x_2370_);
                        v___x_2385_ = lean_box(0);
                        v_isShared_2386_ = v_isSharedCheck_2391_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_x_2392_ = lean_ctor_get(v_x_2370_, 0);
                    v_i_2393_ = lean_ctor_get(v_x_2370_, 1);
                    v_updtHeader_2394_ = lean_ctor_get_uint8(
                        v_x_2370_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_ys_2395_ = lean_ctor_get(v_x_2370_, 2);
                    v_isSharedCheck_2404_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2404_ == 0 {
                        v___x_2397_ = v_x_2370_;
                        v_isShared_2398_ = v_isSharedCheck_2404_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_ys_2395_);
                        lean_inc(v_i_2393_);
                        lean_inc(v_x_2392_);
                        lean_dec(v_x_2370_);
                        v___x_2397_ = lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2404_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_2405_ = lean_ctor_get(v_x_2370_, 0);
                    v_x_2406_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2414_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v___x_2408_ = v_x_2370_;
                        v_isShared_2409_ = v_isSharedCheck_2414_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_x_2406_);
                        lean_inc(v_i_2405_);
                        lean_dec(v_x_2370_);
                        v___x_2408_ = lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2414_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_i_2415_ = lean_ctor_get(v_x_2370_, 0);
                    v_x_2416_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2424_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2424_ == 0 {
                        v___x_2418_ = v_x_2370_;
                        v_isShared_2419_ = v_isSharedCheck_2424_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_x_2416_);
                        lean_inc(v_i_2415_);
                        lean_dec(v_x_2370_);
                        v___x_2418_ = lean_box(0);
                        v_isShared_2419_ = v_isSharedCheck_2424_;
                        state = 9;
                        continue;
                    }
                }
                5 => {
                    v_n_2425_ = lean_ctor_get(v_x_2370_, 0);
                    v_offset_2426_ = lean_ctor_get(v_x_2370_, 1);
                    v_x_2427_ = lean_ctor_get(v_x_2370_, 2);
                    v_isSharedCheck_2435_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2435_ == 0 {
                        v___x_2429_ = v_x_2370_;
                        v_isShared_2430_ = v_isSharedCheck_2435_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_x_2427_);
                        lean_inc(v_offset_2426_);
                        lean_inc(v_n_2425_);
                        lean_dec(v_x_2370_);
                        v___x_2429_ = lean_box(0);
                        v_isShared_2430_ = v_isSharedCheck_2435_;
                        state = 11;
                        continue;
                    }
                }
                6 => {
                    v_c_2436_ = lean_ctor_get(v_x_2370_, 0);
                    v_ys_2437_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2445_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2445_ == 0 {
                        v___x_2439_ = v_x_2370_;
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_ys_2437_);
                        lean_inc(v_c_2436_);
                        lean_dec(v_x_2370_);
                        v___x_2439_ = lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_c_2446_ = lean_ctor_get(v_x_2370_, 0);
                    v_ys_2447_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2455_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2455_ == 0 {
                        v___x_2449_ = v_x_2370_;
                        v_isShared_2450_ = v_isSharedCheck_2455_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_ys_2447_);
                        lean_inc(v_c_2446_);
                        lean_dec(v_x_2370_);
                        v___x_2449_ = lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2455_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_x_2456_ = lean_ctor_get(v_x_2370_, 0);
                    v_ys_2457_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2466_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2466_ == 0 {
                        v___x_2459_ = v_x_2370_;
                        v_isShared_2460_ = v_isSharedCheck_2466_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_ys_2457_);
                        lean_inc(v_x_2456_);
                        lean_dec(v_x_2370_);
                        v___x_2459_ = lean_box(0);
                        v_isShared_2460_ = v_isSharedCheck_2466_;
                        state = 17;
                        continue;
                    }
                }
                9 => {
                    v_ty_2467_ = lean_ctor_get(v_x_2370_, 0);
                    v_x_2468_ = lean_ctor_get(v_x_2370_, 1);
                    v_isSharedCheck_2476_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2470_ = v_x_2370_;
                        v_isShared_2471_ = v_isSharedCheck_2476_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_x_2468_);
                        lean_inc(v_ty_2467_);
                        lean_dec(v_x_2370_);
                        v___x_2470_ = lean_box(0);
                        v_isShared_2471_ = v_isSharedCheck_2476_;
                        state = 19;
                        continue;
                    }
                }
                10 => {
                    v_x_2477_ = lean_ctor_get(v_x_2370_, 0);
                    v_isSharedCheck_2485_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2485_ == 0 {
                        v___x_2479_ = v_x_2370_;
                        v_isShared_2480_ = v_isSharedCheck_2485_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_x_2477_);
                        lean_dec(v_x_2370_);
                        v___x_2479_ = lean_box(0);
                        v_isShared_2480_ = v_isSharedCheck_2485_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    return v_x_2370_;
                }
                _ => {
                    v_x_2486_ = lean_ctor_get(v_x_2370_, 0);
                    v_isSharedCheck_2494_ = (!lean_is_exclusive(v_x_2370_)) as u8;
                    if v_isSharedCheck_2494_ == 0 {
                        v___x_2488_ = v_x_2370_;
                        v_isShared_2489_ = v_isSharedCheck_2494_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_x_2486_);
                        lean_dec(v_x_2370_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2494_;
                        state = 23;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2377_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_2373_, v_x_2371_);
                if v_isShared_2376_ == 0 {
                    lean_ctor_set(v___x_2375_, 1, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_i_2372_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2377_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2379_;
            }
            3 => {
                v___x_2387_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2383_, v_x_2371_);
                lean_dec(v_x_2383_);
                if v_isShared_2386_ == 0 {
                    lean_ctor_set(v___x_2385_, 1, v___x_2387_);
                    v___x_2389_ = v___x_2385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_n_2382_);
                    lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2387_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2389_;
            }
            5 => {
                v___x_2399_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2392_, v_x_2371_);
                lean_dec(v_x_2392_);
                v___x_2400_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_2395_, v_x_2371_);
                if v_isShared_2398_ == 0 {
                    lean_ctor_set(v___x_2397_, 2, v___x_2400_);
                    lean_ctor_set(v___x_2397_, 0, v___x_2399_);
                    v___x_2402_ = v___x_2397_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2403_ = lean_alloc_ctor(2, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2399_);
                    lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_i_2393_);
                    lean_ctor_set(v_reuseFailAlloc_2403_, 2, v___x_2400_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2403_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_updtHeader_2394_,
                    );
                    v___x_2402_ = v_reuseFailAlloc_2403_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2402_;
            }
            7 => {
                v___x_2410_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2406_, v_x_2371_);
                lean_dec(v_x_2406_);
                if v_isShared_2409_ == 0 {
                    lean_ctor_set(v___x_2408_, 1, v___x_2410_);
                    v___x_2412_ = v___x_2408_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2413_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_i_2405_);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2410_);
                    v___x_2412_ = v_reuseFailAlloc_2413_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2412_;
            }
            9 => {
                v___x_2420_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2416_, v_x_2371_);
                lean_dec(v_x_2416_);
                if v_isShared_2419_ == 0 {
                    lean_ctor_set(v___x_2418_, 1, v___x_2420_);
                    v___x_2422_ = v___x_2418_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_i_2415_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2420_);
                    v___x_2422_ = v_reuseFailAlloc_2423_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2422_;
            }
            11 => {
                v___x_2431_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2427_, v_x_2371_);
                lean_dec(v_x_2427_);
                if v_isShared_2430_ == 0 {
                    lean_ctor_set(v___x_2429_, 2, v___x_2431_);
                    v___x_2433_ = v___x_2429_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = lean_alloc_ctor(5, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_n_2425_);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_offset_2426_);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 2, v___x_2431_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2433_;
            }
            13 => {
                v___x_2441_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_2437_, v_x_2371_);
                if v_isShared_2440_ == 0 {
                    lean_ctor_set(v___x_2439_, 1, v___x_2441_);
                    v___x_2443_ = v___x_2439_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_c_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2441_);
                    v___x_2443_ = v_reuseFailAlloc_2444_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2443_;
            }
            15 => {
                v___x_2451_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_2447_, v_x_2371_);
                if v_isShared_2450_ == 0 {
                    lean_ctor_set(v___x_2449_, 1, v___x_2451_);
                    v___x_2453_ = v___x_2449_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2454_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_c_2446_);
                    lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___x_2451_);
                    v___x_2453_ = v_reuseFailAlloc_2454_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2453_;
            }
            17 => {
                v___x_2461_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2456_, v_x_2371_);
                lean_dec(v_x_2456_);
                v___x_2462_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_2457_, v_x_2371_);
                if v_isShared_2460_ == 0 {
                    lean_ctor_set(v___x_2459_, 1, v___x_2462_);
                    lean_ctor_set(v___x_2459_, 0, v___x_2461_);
                    v___x_2464_ = v___x_2459_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2465_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2461_);
                    lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2462_);
                    v___x_2464_ = v_reuseFailAlloc_2465_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2464_;
            }
            19 => {
                v___x_2472_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2468_, v_x_2371_);
                lean_dec(v_x_2468_);
                if v_isShared_2471_ == 0 {
                    lean_ctor_set(v___x_2470_, 1, v___x_2472_);
                    v___x_2474_ = v___x_2470_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = lean_alloc_ctor(9, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_ty_2467_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2472_);
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2474_;
            }
            21 => {
                v___x_2481_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2477_, v_x_2371_);
                lean_dec(v_x_2477_);
                if v_isShared_2480_ == 0 {
                    lean_ctor_set(v___x_2479_, 0, v___x_2481_);
                    v___x_2483_ = v___x_2479_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = lean_alloc_ctor(10, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
                    v___x_2483_ = v_reuseFailAlloc_2484_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2483_;
            }
            23 => {
                v___x_2490_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2486_, v_x_2371_);
                lean_dec(v_x_2486_);
                if v_isShared_2489_ == 0 {
                    lean_ctor_set(v___x_2488_, 0, v___x_2490_);
                    v___x_2492_ = v___x_2488_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = lean_alloc_ctor(12, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                    v___x_2492_ = v_reuseFailAlloc_2493_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_normExpr___boxed(
    mut v_x_2495_: *mut LeanObject,
    mut v_x_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2497_: *mut LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_IR_NormalizeIds_normExpr(v_x_2495_, v_x_2496_);
    lean_dec(v_x_2496_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(
    mut v_x_2498_: *mut LeanObject,
    mut v_y_2499_: *mut LeanObject,
) -> u8 {
    let mut v___x_2500_: u8 = 0;
    v___x_2500_ = lean_nat_dec_lt(v_x_2498_, v_y_2499_);
    if v___x_2500_ == 0 {
        let mut v___x_2501_: u8 = 0;
        v___x_2501_ = lean_nat_dec_eq(v_x_2498_, v_y_2499_);
        if v___x_2501_ == 0 {
            let mut v___x_2502_: u8 = 0;
            v___x_2502_ = 2;
            return v___x_2502_;
        } else {
            let mut v___x_2503_: u8 = 0;
            v___x_2503_ = 1;
            return v___x_2503_;
        }
    } else {
        let mut v___x_2504_: u8 = 0;
        v___x_2504_ = 0;
        return v___x_2504_;
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(
    mut v_x_2505_: *mut LeanObject,
    mut v_y_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2507_: u8 = 0;
    let mut v_r_2508_: *mut LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_2505_, v_y_2506_);
    lean_dec(v_y_2506_);
    lean_dec(v_x_2505_);
    v_r_2508_ = lean_box((v_res_2507_) as usize);
    return v_r_2508_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar___redArg(
    mut v_x_2510_: *mut LeanObject,
    mut v_k_2511_: *mut LeanObject,
    mut v_m_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___f_2514_ = l_Lean_IR_NormalizeIds_withVar___redArg___closed__0;
    v___x_2515_ = lean_unsigned_to_nat(1);
    v___x_2516_ = lean_nat_add(v_a_2513_, v___x_2515_);
    lean_inc(v_m_2512_);
    lean_inc(v_a_2513_);
    v___x_2517_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2514_, v_x_2510_, v_a_2513_, v_m_2512_);
    v___x_2518_ = lean_apply_3(v_k_2511_, v_a_2513_, v___x_2517_, v___x_2516_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar___redArg___boxed(
    mut v_x_2519_: *mut LeanObject,
    mut v_k_2520_: *mut LeanObject,
    mut v_m_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2523_: *mut LeanObject = core::ptr::null_mut();
    v_res_2523_ =
        l_Lean_IR_NormalizeIds_withVar___redArg(v_x_2519_, v_k_2520_, v_m_2521_, v_a_2522_);
    lean_dec(v_m_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar(
    mut v_00_u03b1_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
    mut v_k_2526_: *mut LeanObject,
    mut v_m_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    v___f_2529_ = l_Lean_IR_NormalizeIds_withVar___redArg___closed__0;
    v___x_2530_ = lean_unsigned_to_nat(1);
    v___x_2531_ = lean_nat_add(v_a_2528_, v___x_2530_);
    lean_inc(v_m_2527_);
    lean_inc(v_a_2528_);
    v___x_2532_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2529_, v_x_2525_, v_a_2528_, v_m_2527_);
    v___x_2533_ = lean_apply_3(v_k_2526_, v_a_2528_, v___x_2532_, v___x_2531_);
    return v___x_2533_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withVar___boxed(
    mut v_00_u03b1_2534_: *mut LeanObject,
    mut v_x_2535_: *mut LeanObject,
    mut v_k_2536_: *mut LeanObject,
    mut v_m_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2539_: *mut LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_IR_NormalizeIds_withVar(
        v_00_u03b1_2534_,
        v_x_2535_,
        v_k_2536_,
        v_m_2537_,
        v_a_2538_,
    );
    lean_dec(v_m_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withJP___redArg(
    mut v_x_2540_: *mut LeanObject,
    mut v_k_2541_: *mut LeanObject,
    mut v_m_2542_: *mut LeanObject,
    mut v_a_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___f_2544_ = l_Lean_IR_NormalizeIds_withVar___redArg___closed__0;
    v___x_2545_ = lean_unsigned_to_nat(1);
    v___x_2546_ = lean_nat_add(v_a_2543_, v___x_2545_);
    lean_inc(v_m_2542_);
    lean_inc(v_a_2543_);
    v___x_2547_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2544_, v_x_2540_, v_a_2543_, v_m_2542_);
    v___x_2548_ = lean_apply_3(v_k_2541_, v_a_2543_, v___x_2547_, v___x_2546_);
    return v___x_2548_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withJP___redArg___boxed(
    mut v_x_2549_: *mut LeanObject,
    mut v_k_2550_: *mut LeanObject,
    mut v_m_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_res_2553_ =
        l_Lean_IR_NormalizeIds_withJP___redArg(v_x_2549_, v_k_2550_, v_m_2551_, v_a_2552_);
    lean_dec(v_m_2551_);
    return v_res_2553_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withJP(
    mut v_00_u03b1_2554_: *mut LeanObject,
    mut v_x_2555_: *mut LeanObject,
    mut v_k_2556_: *mut LeanObject,
    mut v_m_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    v___f_2559_ = l_Lean_IR_NormalizeIds_withVar___redArg___closed__0;
    v___x_2560_ = lean_unsigned_to_nat(1);
    v___x_2561_ = lean_nat_add(v_a_2558_, v___x_2560_);
    lean_inc(v_m_2557_);
    lean_inc(v_a_2558_);
    v___x_2562_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2559_, v_x_2555_, v_a_2558_, v_m_2557_);
    v___x_2563_ = lean_apply_3(v_k_2556_, v_a_2558_, v___x_2562_, v___x_2561_);
    return v___x_2563_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withJP___boxed(
    mut v_00_u03b1_2564_: *mut LeanObject,
    mut v_x_2565_: *mut LeanObject,
    mut v_k_2566_: *mut LeanObject,
    mut v_m_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2569_: *mut LeanObject = core::ptr::null_mut();
    v_res_2569_ =
        l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_2564_, v_x_2565_, v_k_2566_, v_m_2567_, v_a_2568_);
    lean_dec(v_m_2567_);
    return v_res_2569_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(
    mut v_fst_2570_: *mut LeanObject,
    mut v_x_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_2573_: u8 = 0;
    let mut v_ty_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_2572_ = lean_ctor_get(v_x_2571_, 0);
                v_borrow_2573_ = lean_ctor_get_uint8(
                    v_x_2571_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_ty_2574_ = lean_ctor_get(v_x_2571_, 1);
                v_isSharedCheck_2582_ = (!lean_is_exclusive(v_x_2571_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v___x_2576_ = v_x_2571_;
                    v_isShared_2577_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ty_2574_);
                    lean_inc(v_x_2572_);
                    lean_dec(v_x_2571_);
                    v___x_2576_ = lean_box(0);
                    v_isShared_2577_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2578_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2572_, v_fst_2570_);
                lean_dec(v_x_2572_);
                if v_isShared_2577_ == 0 {
                    lean_ctor_set(v___x_2576_, 0, v___x_2578_);
                    v___x_2580_ = v___x_2576_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_ty_2574_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_borrow_2573_,
                    );
                    v___x_2580_ = v_reuseFailAlloc_2581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(
    mut v_fst_2583_: *mut LeanObject,
    mut v_x_2584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2585_: *mut LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_2583_, v_x_2584_);
    lean_dec(v_fst_2583_);
    return v_res_2585_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(
    mut v___f_2586_: *mut LeanObject,
    mut v_m_2587_: *mut LeanObject,
    mut v_p_2588_: *mut LeanObject,
    mut v___y_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v_x_2590_ = lean_ctor_get(v_p_2588_, 0);
    lean_inc(v_x_2590_);
    lean_dec_ref(v_p_2588_);
    v___x_2591_ = lean_unsigned_to_nat(1);
    v___x_2592_ = lean_nat_add(v___y_2589_, v___x_2591_);
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v___f_2586_,
        v_x_2590_,
        v___y_2589_,
        v_m_2587_,
    );
    v___x_2594_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2594_, 0, v___x_2593_);
    lean_ctor_set(v___x_2594_, 1, v___x_2592_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___redArg(
    mut v_ps_2642_: *mut LeanObject,
    mut v_k_2643_: *mut LeanObject,
    mut v_m_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___f_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: usize = 0;
    let mut v___x_793__overap_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: usize = 0;
    let mut v___x_2670_: usize = 0;
    let mut v___x_798__overap_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2646_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__9;
                v___x_2659_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__19;
                v___x_2660_ = lean_unsigned_to_nat(0);
                v___x_2661_ = lean_array_get_size(v_ps_2642_);
                v___x_2662_ = lean_nat_dec_lt(v___x_2660_, v___x_2661_);
                if v___x_2662_ == 0 {
                    lean_inc(v_m_2644_);
                    v_fst_2648_ = v_m_2644_;
                    v_snd_2649_ = v_a_2645_;
                    state = 1;
                    continue;
                } else {
                    v___f_2663_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__20;
                    v___x_2664_ = lean_nat_dec_le(v___x_2661_, v___x_2661_);
                    if v___x_2664_ == 0 {
                        if v___x_2662_ == 0 {
                            lean_inc(v_m_2644_);
                            v_fst_2648_ = v_m_2644_;
                            v_snd_2649_ = v_a_2645_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2665_ = 0usize;
                            v___x_2666_ = lean_usize_of_nat(v___x_2661_);
                            lean_inc(v_m_2644_);
                            lean_inc_ref(v_ps_2642_);
                            v___x_793__overap_2667_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2659_,
                                    v___f_2663_,
                                    v_ps_2642_,
                                    v___x_2665_,
                                    v___x_2666_,
                                    v_m_2644_,
                                );
                            v___x_2668_ = lean_apply_1(v___x_793__overap_2667_, v_a_2645_);
                            v___y_2656_ = v___x_2668_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2669_ = 0usize;
                        v___x_2670_ = lean_usize_of_nat(v___x_2661_);
                        lean_inc(v_m_2644_);
                        lean_inc_ref(v_ps_2642_);
                        v___x_798__overap_2671_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2659_,
                                v___f_2663_,
                                v_ps_2642_,
                                v___x_2669_,
                                v___x_2670_,
                                v_m_2644_,
                            );
                        v___x_2672_ = lean_apply_1(v___x_798__overap_2671_, v_a_2645_);
                        v___y_2656_ = v___x_2672_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_fst_2648_);
                v___f_2650_ = lean_alloc_closure(
                    l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2650_, 0, v_fst_2648_);
                v_sz_2651_ = lean_array_size(v_ps_2642_);
                v___x_2652_ = 0usize;
                v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2646_,
                    v___f_2650_,
                    v_sz_2651_,
                    v___x_2652_,
                    v_ps_2642_,
                );
                v___x_2654_ = lean_apply_3(v_k_2643_, v___x_2653_, v_fst_2648_, v_snd_2649_);
                return v___x_2654_;
            }
            2 => {
                v_fst_2657_ = lean_ctor_get(v___y_2656_, 0);
                lean_inc(v_fst_2657_);
                v_snd_2658_ = lean_ctor_get(v___y_2656_, 1);
                lean_inc(v_snd_2658_);
                lean_dec_ref(v___y_2656_);
                v_fst_2648_ = v_fst_2657_;
                v_snd_2649_ = v_snd_2658_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___redArg___boxed(
    mut v_ps_2673_: *mut LeanObject,
    mut v_k_2674_: *mut LeanObject,
    mut v_m_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
    v_res_2677_ =
        l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_2673_, v_k_2674_, v_m_2675_, v_a_2676_);
    lean_dec(v_m_2675_);
    return v_res_2677_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams(
    mut v_00_u03b1_2678_: *mut LeanObject,
    mut v_ps_2679_: *mut LeanObject,
    mut v_k_2680_: *mut LeanObject,
    mut v_m_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2688_: usize = 0;
    let mut v___x_2689_: usize = 0;
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___f_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_975__overap_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: usize = 0;
    let mut v___x_978__overap_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2683_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__9;
                v___x_2696_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__19;
                v___x_2697_ = lean_unsigned_to_nat(0);
                v___x_2698_ = lean_array_get_size(v_ps_2679_);
                v___x_2699_ = lean_nat_dec_lt(v___x_2697_, v___x_2698_);
                if v___x_2699_ == 0 {
                    lean_inc(v_m_2681_);
                    v_fst_2685_ = v_m_2681_;
                    v_snd_2686_ = v_a_2682_;
                    state = 1;
                    continue;
                } else {
                    v___f_2700_ = l_Lean_IR_NormalizeIds_withParams___redArg___closed__20;
                    v___x_2701_ = lean_nat_dec_le(v___x_2698_, v___x_2698_);
                    if v___x_2701_ == 0 {
                        if v___x_2699_ == 0 {
                            lean_inc(v_m_2681_);
                            v_fst_2685_ = v_m_2681_;
                            v_snd_2686_ = v_a_2682_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2702_ = 0usize;
                            v___x_2703_ = lean_usize_of_nat(v___x_2698_);
                            lean_inc(v_m_2681_);
                            lean_inc_ref(v_ps_2679_);
                            v___x_975__overap_2704_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2696_,
                                    v___f_2700_,
                                    v_ps_2679_,
                                    v___x_2702_,
                                    v___x_2703_,
                                    v_m_2681_,
                                );
                            v___x_2705_ = lean_apply_1(v___x_975__overap_2704_, v_a_2682_);
                            v___y_2693_ = v___x_2705_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2706_ = 0usize;
                        v___x_2707_ = lean_usize_of_nat(v___x_2698_);
                        lean_inc(v_m_2681_);
                        lean_inc_ref(v_ps_2679_);
                        v___x_978__overap_2708_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2696_,
                                v___f_2700_,
                                v_ps_2679_,
                                v___x_2706_,
                                v___x_2707_,
                                v_m_2681_,
                            );
                        v___x_2709_ = lean_apply_1(v___x_978__overap_2708_, v_a_2682_);
                        v___y_2693_ = v___x_2709_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_fst_2685_);
                v___f_2687_ = lean_alloc_closure(
                    l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2687_, 0, v_fst_2685_);
                v_sz_2688_ = lean_array_size(v_ps_2679_);
                v___x_2689_ = 0usize;
                v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2683_,
                    v___f_2687_,
                    v_sz_2688_,
                    v___x_2689_,
                    v_ps_2679_,
                );
                v___x_2691_ = lean_apply_3(v_k_2680_, v___x_2690_, v_fst_2685_, v_snd_2686_);
                return v___x_2691_;
            }
            2 => {
                v_fst_2694_ = lean_ctor_get(v___y_2693_, 0);
                lean_inc(v_fst_2694_);
                v_snd_2695_ = lean_ctor_get(v___y_2693_, 1);
                lean_inc(v_snd_2695_);
                lean_dec_ref(v___y_2693_);
                v_fst_2685_ = v_fst_2694_;
                v_snd_2686_ = v_snd_2695_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_withParams___boxed(
    mut v_00_u03b1_2710_: *mut LeanObject,
    mut v_ps_2711_: *mut LeanObject,
    mut v_k_2712_: *mut LeanObject,
    mut v_m_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2715_: *mut LeanObject = core::ptr::null_mut();
    v_res_2715_ = l_Lean_IR_NormalizeIds_withParams(
        v_00_u03b1_2710_,
        v_ps_2711_,
        v_k_2712_,
        v_m_2713_,
        v_a_2714_,
    );
    lean_dec(v_m_2713_);
    return v_res_2715_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(
    mut v_00_u03b1_2716_: *mut LeanObject,
    mut v_x_2717_: *mut LeanObject,
    mut v_m_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2720_ = lean_apply_1(v_x_2717_, v_m_2718_);
    v___x_2721_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2721_, 0, v___x_2720_);
    lean_ctor_set(v___x_2721_, 1, v___y_2719_);
    return v___x_2721_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(
    mut v_fst_2724_: *mut LeanObject,
    mut v_sz_2725_: usize,
    mut v_i_2726_: usize,
    mut v_bs_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: u8 = 0;
    let mut v_v_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_2731_: u8 = 0;
    let mut v_ty_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: usize = 0;
    let mut v___x_2742_: usize = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2728_ = lean_usize_dec_lt(v_i_2726_, v_sz_2725_);
                if v___x_2728_ == 0 {
                    return v_bs_2727_;
                } else {
                    v_v_2729_ = lean_array_uget(v_bs_2727_, v_i_2726_);
                    v_x_2730_ = lean_ctor_get(v_v_2729_, 0);
                    v_borrow_2731_ = lean_ctor_get_uint8(
                        v_v_2729_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_ty_2732_ = lean_ctor_get(v_v_2729_, 1);
                    v_isSharedCheck_2746_ = (!lean_is_exclusive(v_v_2729_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v___x_2734_ = v_v_2729_;
                        v_isShared_2735_ = v_isSharedCheck_2746_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_ty_2732_);
                        lean_inc(v_x_2730_);
                        lean_dec(v_v_2729_);
                        v___x_2734_ = lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2746_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2736_ = lean_unsigned_to_nat(0);
                v_bs_x27_2737_ = lean_array_uset(v_bs_2727_, v_i_2726_, v___x_2736_);
                v___x_2738_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2730_, v_fst_2724_);
                lean_dec(v_x_2730_);
                if v_isShared_2735_ == 0 {
                    lean_ctor_set(v___x_2734_, 0, v___x_2738_);
                    v___x_2740_ = v___x_2734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_ty_2732_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2745_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_borrow_2731_,
                    );
                    v___x_2740_ = v_reuseFailAlloc_2745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2741_ = 1usize;
                v___x_2742_ = lean_usize_add(v_i_2726_, v___x_2741_);
                v___x_2743_ = lean_array_uset(v_bs_x27_2737_, v_i_2726_, v___x_2740_);
                v_i_2726_ = v___x_2742_;
                v_bs_2727_ = v___x_2743_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(
    mut v_fst_2747_: *mut LeanObject,
    mut v_sz_2748_: *mut LeanObject,
    mut v_i_2749_: *mut LeanObject,
    mut v_bs_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2751_: usize = 0;
    let mut v_i_boxed_2752_: usize = 0;
    let mut v_res_2753_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2751_ = lean_unbox_usize(v_sz_2748_);
    lean_dec(v_sz_2748_);
    v_i_boxed_2752_ = lean_unbox_usize(v_i_2749_);
    lean_dec(v_i_2749_);
    v_res_2753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_2747_, v_sz_boxed_2751_, v_i_boxed_2752_, v_bs_2750_);
    lean_dec(v_fst_2747_);
    return v_res_2753_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(
    mut v_as_2754_: *mut LeanObject,
    mut v_i_2755_: usize,
    mut v_stop_2756_: usize,
    mut v_b_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: usize = 0;
    let mut v___x_2766_: usize = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2759_ = lean_usize_dec_eq(v_i_2755_, v_stop_2756_);
                if v___x_2759_ == 0 {
                    v___x_2760_ = lean_array_uget_borrowed(v_as_2754_, v_i_2755_);
                    v_x_2761_ = lean_ctor_get(v___x_2760_, 0);
                    v___x_2762_ = lean_unsigned_to_nat(1);
                    v___x_2763_ = lean_nat_add(v___y_2758_, v___x_2762_);
                    lean_inc(v_x_2761_);
                    v___x_2764_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_2761_, v___y_2758_, v_b_2757_);
                    v___x_2765_ = 1usize;
                    v___x_2766_ = lean_usize_add(v_i_2755_, v___x_2765_);
                    v_i_2755_ = v___x_2766_;
                    v_b_2757_ = v___x_2764_;
                    v___y_2758_ = v___x_2763_;
                    state = 0;
                    continue;
                } else {
                    v___x_2768_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2768_, 0, v_b_2757_);
                    lean_ctor_set(v___x_2768_, 1, v___y_2758_);
                    return v___x_2768_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(
    mut v_as_2769_: *mut LeanObject,
    mut v_i_2770_: *mut LeanObject,
    mut v_stop_2771_: *mut LeanObject,
    mut v_b_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2774_: usize = 0;
    let mut v_stop_boxed_2775_: usize = 0;
    let mut v_res_2776_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2774_ = lean_unbox_usize(v_i_2770_);
    lean_dec(v_i_2770_);
    v_stop_boxed_2775_ = lean_unbox_usize(v_stop_2771_);
    lean_dec(v_stop_2771_);
    v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_2769_, v_i_boxed_2774_, v_stop_boxed_2775_, v_b_2772_, v___y_2773_);
    lean_dec_ref(v_as_2769_);
    return v_res_2776_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normFnBody(
    mut v_x_2777_: *mut LeanObject,
    mut v_a_2778_: *mut LeanObject,
    mut v_a_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2803_: u8 = 0;
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_j_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v_fst_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2826_: u8 = 0;
    let mut v_sz_2827_: usize = 0;
    let mut v___x_2828_: usize = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v___y_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: usize = 0;
    let mut v___x_2846_: usize = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: usize = 0;
    let mut v___x_2849_: usize = 0;
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_isSharedCheck_2874_: u8 = 0;
    let mut v_x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v_x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2946_: u8 = 0;
    let mut v_persistent_2947_: u8 = 0;
    let mut v_b_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2951_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut v_x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2969_: u8 = 0;
    let mut v_persistent_2970_: u8 = 0;
    let mut v_b_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2988_: u8 = 0;
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_tid_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xType_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3018_: usize = 0;
    let mut v___x_3019_: usize = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3025_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v_x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut v_j_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3048_: u8 = 0;
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2777_) {
                0 => {
                    v_x_2780_ = lean_ctor_get(v_x_2777_, 0);
                    v_ty_2781_ = lean_ctor_get(v_x_2777_, 1);
                    v_e_2782_ = lean_ctor_get(v_x_2777_, 2);
                    v_b_2783_ = lean_ctor_get(v_x_2777_, 3);
                    v_isSharedCheck_2804_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2804_ == 0 {
                        v___x_2785_ = v_x_2777_;
                        v_isShared_2786_ = v_isSharedCheck_2804_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_b_2783_);
                        lean_inc(v_e_2782_);
                        lean_inc(v_ty_2781_);
                        lean_inc(v_x_2780_);
                        lean_dec(v_x_2777_);
                        v___x_2785_ = lean_box(0);
                        v_isShared_2786_ = v_isSharedCheck_2804_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_2805_ = lean_ctor_get(v_x_2777_, 0);
                    v_xs_2806_ = lean_ctor_get(v_x_2777_, 1);
                    v_v_2807_ = lean_ctor_get(v_x_2777_, 2);
                    v_b_2808_ = lean_ctor_get(v_x_2777_, 3);
                    v_isSharedCheck_2851_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2851_ == 0 {
                        v___x_2810_ = v_x_2777_;
                        v_isShared_2811_ = v_isSharedCheck_2851_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_b_2808_);
                        lean_inc(v_v_2807_);
                        lean_inc(v_xs_2806_);
                        lean_inc(v_j_2805_);
                        lean_dec(v_x_2777_);
                        v___x_2810_ = lean_box(0);
                        v_isShared_2811_ = v_isSharedCheck_2851_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_x_2852_ = lean_ctor_get(v_x_2777_, 0);
                    v_i_2853_ = lean_ctor_get(v_x_2777_, 1);
                    v_y_2854_ = lean_ctor_get(v_x_2777_, 2);
                    v_b_2855_ = lean_ctor_get(v_x_2777_, 3);
                    v_isSharedCheck_2874_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2874_ == 0 {
                        v___x_2857_ = v_x_2777_;
                        v_isShared_2858_ = v_isSharedCheck_2874_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_b_2855_);
                        lean_inc(v_y_2854_);
                        lean_inc(v_i_2853_);
                        lean_inc(v_x_2852_);
                        lean_dec(v_x_2777_);
                        v___x_2857_ = lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2874_;
                        state = 11;
                        continue;
                    }
                }
                3 => {
                    v_x_2875_ = lean_ctor_get(v_x_2777_, 0);
                    v_cidx_2876_ = lean_ctor_get(v_x_2777_, 1);
                    v_b_2877_ = lean_ctor_get(v_x_2777_, 2);
                    v_isSharedCheck_2895_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2879_ = v_x_2777_;
                        v_isShared_2880_ = v_isSharedCheck_2895_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_b_2877_);
                        lean_inc(v_cidx_2876_);
                        lean_inc(v_x_2875_);
                        lean_dec(v_x_2777_);
                        v___x_2879_ = lean_box(0);
                        v_isShared_2880_ = v_isSharedCheck_2895_;
                        state = 15;
                        continue;
                    }
                }
                4 => {
                    v_x_2896_ = lean_ctor_get(v_x_2777_, 0);
                    v_i_2897_ = lean_ctor_get(v_x_2777_, 1);
                    v_y_2898_ = lean_ctor_get(v_x_2777_, 2);
                    v_b_2899_ = lean_ctor_get(v_x_2777_, 3);
                    v_isSharedCheck_2918_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2918_ == 0 {
                        v___x_2901_ = v_x_2777_;
                        v_isShared_2902_ = v_isSharedCheck_2918_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_b_2899_);
                        lean_inc(v_y_2898_);
                        lean_inc(v_i_2897_);
                        lean_inc(v_x_2896_);
                        lean_dec(v_x_2777_);
                        v___x_2901_ = lean_box(0);
                        v_isShared_2902_ = v_isSharedCheck_2918_;
                        state = 19;
                        continue;
                    }
                }
                5 => {
                    v_x_2919_ = lean_ctor_get(v_x_2777_, 0);
                    v_i_2920_ = lean_ctor_get(v_x_2777_, 1);
                    v_offset_2921_ = lean_ctor_get(v_x_2777_, 2);
                    v_y_2922_ = lean_ctor_get(v_x_2777_, 3);
                    v_ty_2923_ = lean_ctor_get(v_x_2777_, 4);
                    v_b_2924_ = lean_ctor_get(v_x_2777_, 5);
                    v_isSharedCheck_2943_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2943_ == 0 {
                        v___x_2926_ = v_x_2777_;
                        v_isShared_2927_ = v_isSharedCheck_2943_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_b_2924_);
                        lean_inc(v_ty_2923_);
                        lean_inc(v_y_2922_);
                        lean_inc(v_offset_2921_);
                        lean_inc(v_i_2920_);
                        lean_inc(v_x_2919_);
                        lean_dec(v_x_2777_);
                        v___x_2926_ = lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2943_;
                        state = 23;
                        continue;
                    }
                }
                6 => {
                    v_x_2944_ = lean_ctor_get(v_x_2777_, 0);
                    v_n_2945_ = lean_ctor_get(v_x_2777_, 1);
                    v_c_2946_ = lean_ctor_get_uint8(
                        v_x_2777_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_2947_ = lean_ctor_get_uint8(
                        v_x_2777_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_b_2948_ = lean_ctor_get(v_x_2777_, 2);
                    v_isSharedCheck_2966_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2966_ == 0 {
                        v___x_2950_ = v_x_2777_;
                        v_isShared_2951_ = v_isSharedCheck_2966_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_b_2948_);
                        lean_inc(v_n_2945_);
                        lean_inc(v_x_2944_);
                        lean_dec(v_x_2777_);
                        v___x_2950_ = lean_box(0);
                        v_isShared_2951_ = v_isSharedCheck_2966_;
                        state = 27;
                        continue;
                    }
                }
                7 => {
                    v_x_2967_ = lean_ctor_get(v_x_2777_, 0);
                    v_n_2968_ = lean_ctor_get(v_x_2777_, 1);
                    v_c_2969_ = lean_ctor_get_uint8(
                        v_x_2777_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_2970_ = lean_ctor_get_uint8(
                        v_x_2777_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_b_2971_ = lean_ctor_get(v_x_2777_, 2);
                    v_isSharedCheck_2989_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2973_ = v_x_2777_;
                        v_isShared_2974_ = v_isSharedCheck_2989_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_b_2971_);
                        lean_inc(v_n_2968_);
                        lean_inc(v_x_2967_);
                        lean_dec(v_x_2777_);
                        v___x_2973_ = lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2989_;
                        state = 31;
                        continue;
                    }
                }
                8 => {
                    v_x_2990_ = lean_ctor_get(v_x_2777_, 0);
                    v_b_2991_ = lean_ctor_get(v_x_2777_, 1);
                    v_isSharedCheck_3009_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_3009_ == 0 {
                        v___x_2993_ = v_x_2777_;
                        v_isShared_2994_ = v_isSharedCheck_3009_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_b_2991_);
                        lean_inc(v_x_2990_);
                        lean_dec(v_x_2777_);
                        v___x_2993_ = lean_box(0);
                        v_isShared_2994_ = v_isSharedCheck_3009_;
                        state = 35;
                        continue;
                    }
                }
                9 => {
                    v_tid_3010_ = lean_ctor_get(v_x_2777_, 0);
                    v_x_3011_ = lean_ctor_get(v_x_2777_, 1);
                    v_xType_3012_ = lean_ctor_get(v_x_2777_, 2);
                    v_cs_3013_ = lean_ctor_get(v_x_2777_, 3);
                    v_isSharedCheck_3033_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_3033_ == 0 {
                        v___x_3015_ = v_x_2777_;
                        v_isShared_3016_ = v_isSharedCheck_3033_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_cs_3013_);
                        lean_inc(v_xType_3012_);
                        lean_inc(v_x_3011_);
                        lean_inc(v_tid_3010_);
                        lean_dec(v_x_2777_);
                        v___x_3015_ = lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3033_;
                        state = 39;
                        continue;
                    }
                }
                10 => {
                    v_x_3034_ = lean_ctor_get(v_x_2777_, 0);
                    v_isSharedCheck_3043_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_3043_ == 0 {
                        v___x_3036_ = v_x_2777_;
                        v_isShared_3037_ = v_isSharedCheck_3043_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_x_3034_);
                        lean_dec(v_x_2777_);
                        v___x_3036_ = lean_box(0);
                        v_isShared_3037_ = v_isSharedCheck_3043_;
                        state = 43;
                        continue;
                    }
                }
                11 => {
                    v_j_3044_ = lean_ctor_get(v_x_2777_, 0);
                    v_ys_3045_ = lean_ctor_get(v_x_2777_, 1);
                    v_isSharedCheck_3055_ = (!lean_is_exclusive(v_x_2777_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v___x_3047_ = v_x_2777_;
                        v_isShared_3048_ = v_isSharedCheck_3055_;
                        state = 45;
                        continue;
                    } else {
                        lean_inc(v_ys_3045_);
                        lean_inc(v_j_3044_);
                        lean_dec(v_x_2777_);
                        v___x_3047_ = lean_box(0);
                        v_isShared_3048_ = v_isSharedCheck_3055_;
                        state = 45;
                        continue;
                    }
                }
                _ => {
                    v___x_3056_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3056_, 0, v_x_2777_);
                    lean_ctor_set(v___x_3056_, 1, v_a_2779_);
                    return v___x_3056_;
                }
            },
            1 => {
                v___x_2787_ = lean_unsigned_to_nat(1);
                v___x_2788_ = lean_nat_add(v_a_2779_, v___x_2787_);
                lean_inc(v_a_2778_);
                lean_inc(v_a_2779_);
                v___x_2789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_2780_, v_a_2779_, v_a_2778_);
                v___x_2790_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_b_2783_, v___x_2789_, v___x_2788_);
                lean_dec(v___x_2789_);
                v_fst_2791_ = lean_ctor_get(v___x_2790_, 0);
                v_snd_2792_ = lean_ctor_get(v___x_2790_, 1);
                v_isSharedCheck_2803_ = (!lean_is_exclusive(v___x_2790_)) as u8;
                if v_isSharedCheck_2803_ == 0 {
                    v___x_2794_ = v___x_2790_;
                    v_isShared_2795_ = v_isSharedCheck_2803_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2792_);
                    lean_inc(v_fst_2791_);
                    lean_dec(v___x_2790_);
                    v___x_2794_ = lean_box(0);
                    v_isShared_2795_ = v_isSharedCheck_2803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2796_ = l_Lean_IR_NormalizeIds_normExpr(v_e_2782_, v_a_2778_);
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 3, v_fst_2791_);
                    lean_ctor_set(v___x_2785_, 2, v___x_2796_);
                    lean_ctor_set(v___x_2785_, 0, v_a_2779_);
                    v___x_2798_ = v___x_2785_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2779_);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_ty_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 2, v___x_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_fst_2791_);
                    v___x_2798_ = v_reuseFailAlloc_2802_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 0, v___x_2798_);
                    v___x_2800_ = v___x_2794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_snd_2792_);
                    v___x_2800_ = v_reuseFailAlloc_2801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2800_;
            }
            5 => {
                v___x_2841_ = lean_unsigned_to_nat(0);
                v___x_2842_ = lean_array_get_size(v_xs_2806_);
                v___x_2843_ = lean_nat_dec_lt(v___x_2841_, v___x_2842_);
                if v___x_2843_ == 0 {
                    lean_inc(v_a_2778_);
                    v_fst_2813_ = v_a_2778_;
                    v_snd_2814_ = v_a_2779_;
                    state = 6;
                    continue;
                } else {
                    v___x_2844_ = lean_nat_dec_le(v___x_2842_, v___x_2842_);
                    if v___x_2844_ == 0 {
                        if v___x_2843_ == 0 {
                            lean_inc(v_a_2778_);
                            v_fst_2813_ = v_a_2778_;
                            v_snd_2814_ = v_a_2779_;
                            state = 6;
                            continue;
                        } else {
                            v___x_2845_ = 0usize;
                            v___x_2846_ = lean_usize_of_nat(v___x_2842_);
                            lean_inc(v_a_2778_);
                            v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_2806_, v___x_2845_, v___x_2846_, v_a_2778_, v_a_2779_);
                            v___y_2838_ = v___x_2847_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_2848_ = 0usize;
                        v___x_2849_ = lean_usize_of_nat(v___x_2842_);
                        lean_inc(v_a_2778_);
                        v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_2806_, v___x_2848_, v___x_2849_, v_a_2778_, v_a_2779_);
                        v___y_2838_ = v___x_2850_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2815_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_v_2807_, v_fst_2813_, v_snd_2814_);
                v_fst_2816_ = lean_ctor_get(v___x_2815_, 0);
                lean_inc(v_fst_2816_);
                v_snd_2817_ = lean_ctor_get(v___x_2815_, 1);
                lean_inc_n(v_snd_2817_, 2);
                lean_dec_ref(v___x_2815_);
                v___x_2818_ = lean_unsigned_to_nat(1);
                v___x_2819_ = lean_nat_add(v_snd_2817_, v___x_2818_);
                lean_inc(v_a_2778_);
                v___x_2820_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_2805_, v_snd_2817_, v_a_2778_);
                v___x_2821_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_b_2808_, v___x_2820_, v___x_2819_);
                lean_dec(v___x_2820_);
                v_fst_2822_ = lean_ctor_get(v___x_2821_, 0);
                v_snd_2823_ = lean_ctor_get(v___x_2821_, 1);
                v_isSharedCheck_2836_ = (!lean_is_exclusive(v___x_2821_)) as u8;
                if v_isSharedCheck_2836_ == 0 {
                    v___x_2825_ = v___x_2821_;
                    v_isShared_2826_ = v_isSharedCheck_2836_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_2823_);
                    lean_inc(v_fst_2822_);
                    lean_dec(v___x_2821_);
                    v___x_2825_ = lean_box(0);
                    v_isShared_2826_ = v_isSharedCheck_2836_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_sz_2827_ = lean_array_size(v_xs_2806_);
                v___x_2828_ = 0usize;
                v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_2813_, v_sz_2827_, v___x_2828_, v_xs_2806_);
                lean_dec(v_fst_2813_);
                if v_isShared_2811_ == 0 {
                    lean_ctor_set(v___x_2810_, 3, v_fst_2822_);
                    lean_ctor_set(v___x_2810_, 2, v_fst_2816_);
                    lean_ctor_set(v___x_2810_, 1, v___x_2829_);
                    lean_ctor_set(v___x_2810_, 0, v_snd_2817_);
                    v___x_2831_ = v___x_2810_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_snd_2817_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2829_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_fst_2816_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_fst_2822_);
                    v___x_2831_ = v_reuseFailAlloc_2835_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2826_ == 0 {
                    lean_ctor_set(v___x_2825_, 0, v___x_2831_);
                    v___x_2833_ = v___x_2825_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_snd_2823_);
                    v___x_2833_ = v_reuseFailAlloc_2834_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2833_;
            }
            10 => {
                v_fst_2839_ = lean_ctor_get(v___y_2838_, 0);
                lean_inc(v_fst_2839_);
                v_snd_2840_ = lean_ctor_get(v___y_2838_, 1);
                lean_inc(v_snd_2840_);
                lean_dec_ref(v___y_2838_);
                v_fst_2813_ = v_fst_2839_;
                v_snd_2814_ = v_snd_2840_;
                state = 6;
                continue;
            }
            11 => {
                v___x_2859_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2852_, v_a_2778_);
                lean_dec(v_x_2852_);
                v___x_2860_ = l_Lean_IR_NormalizeIds_normArg(v_y_2854_, v_a_2778_);
                v___x_2861_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2855_, v_a_2778_, v_a_2779_);
                v_fst_2862_ = lean_ctor_get(v___x_2861_, 0);
                v_snd_2863_ = lean_ctor_get(v___x_2861_, 1);
                v_isSharedCheck_2873_ = (!lean_is_exclusive(v___x_2861_)) as u8;
                if v_isSharedCheck_2873_ == 0 {
                    v___x_2865_ = v___x_2861_;
                    v_isShared_2866_ = v_isSharedCheck_2873_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_2863_);
                    lean_inc(v_fst_2862_);
                    lean_dec(v___x_2861_);
                    v___x_2865_ = lean_box(0);
                    v_isShared_2866_ = v_isSharedCheck_2873_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2858_ == 0 {
                    lean_ctor_set(v___x_2857_, 3, v_fst_2862_);
                    lean_ctor_set(v___x_2857_, 2, v___x_2860_);
                    lean_ctor_set(v___x_2857_, 0, v___x_2859_);
                    v___x_2868_ = v___x_2857_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2859_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_i_2853_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 2, v___x_2860_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_fst_2862_);
                    v___x_2868_ = v_reuseFailAlloc_2872_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2866_ == 0 {
                    lean_ctor_set(v___x_2865_, 0, v___x_2868_);
                    v___x_2870_ = v___x_2865_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_snd_2863_);
                    v___x_2870_ = v_reuseFailAlloc_2871_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2870_;
            }
            15 => {
                v___x_2881_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2875_, v_a_2778_);
                lean_dec(v_x_2875_);
                v___x_2882_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2877_, v_a_2778_, v_a_2779_);
                v_fst_2883_ = lean_ctor_get(v___x_2882_, 0);
                v_snd_2884_ = lean_ctor_get(v___x_2882_, 1);
                v_isSharedCheck_2894_ = (!lean_is_exclusive(v___x_2882_)) as u8;
                if v_isSharedCheck_2894_ == 0 {
                    v___x_2886_ = v___x_2882_;
                    v_isShared_2887_ = v_isSharedCheck_2894_;
                    state = 16;
                    continue;
                } else {
                    lean_inc(v_snd_2884_);
                    lean_inc(v_fst_2883_);
                    lean_dec(v___x_2882_);
                    v___x_2886_ = lean_box(0);
                    v_isShared_2887_ = v_isSharedCheck_2894_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2880_ == 0 {
                    lean_ctor_set(v___x_2879_, 2, v_fst_2883_);
                    lean_ctor_set(v___x_2879_, 0, v___x_2881_);
                    v___x_2889_ = v___x_2879_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_cidx_2876_);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_fst_2883_);
                    v___x_2889_ = v_reuseFailAlloc_2893_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2887_ == 0 {
                    lean_ctor_set(v___x_2886_, 0, v___x_2889_);
                    v___x_2891_ = v___x_2886_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
                    lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_snd_2884_);
                    v___x_2891_ = v_reuseFailAlloc_2892_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2891_;
            }
            19 => {
                v___x_2903_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2896_, v_a_2778_);
                lean_dec(v_x_2896_);
                v___x_2904_ = l_Lean_IR_NormalizeIds_normIndex(v_y_2898_, v_a_2778_);
                lean_dec(v_y_2898_);
                v___x_2905_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2899_, v_a_2778_, v_a_2779_);
                v_fst_2906_ = lean_ctor_get(v___x_2905_, 0);
                v_snd_2907_ = lean_ctor_get(v___x_2905_, 1);
                v_isSharedCheck_2917_ = (!lean_is_exclusive(v___x_2905_)) as u8;
                if v_isSharedCheck_2917_ == 0 {
                    v___x_2909_ = v___x_2905_;
                    v_isShared_2910_ = v_isSharedCheck_2917_;
                    state = 20;
                    continue;
                } else {
                    lean_inc(v_snd_2907_);
                    lean_inc(v_fst_2906_);
                    lean_dec(v___x_2905_);
                    v___x_2909_ = lean_box(0);
                    v_isShared_2910_ = v_isSharedCheck_2917_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2902_ == 0 {
                    lean_ctor_set(v___x_2901_, 3, v_fst_2906_);
                    lean_ctor_set(v___x_2901_, 2, v___x_2904_);
                    lean_ctor_set(v___x_2901_, 0, v___x_2903_);
                    v___x_2912_ = v___x_2901_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = lean_alloc_ctor(4, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2903_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_i_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 2, v___x_2904_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 3, v_fst_2906_);
                    v___x_2912_ = v_reuseFailAlloc_2916_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_2910_ == 0 {
                    lean_ctor_set(v___x_2909_, 0, v___x_2912_);
                    v___x_2914_ = v___x_2909_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_snd_2907_);
                    v___x_2914_ = v_reuseFailAlloc_2915_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2914_;
            }
            23 => {
                v___x_2928_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2919_, v_a_2778_);
                lean_dec(v_x_2919_);
                v___x_2929_ = l_Lean_IR_NormalizeIds_normIndex(v_y_2922_, v_a_2778_);
                lean_dec(v_y_2922_);
                v___x_2930_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2924_, v_a_2778_, v_a_2779_);
                v_fst_2931_ = lean_ctor_get(v___x_2930_, 0);
                v_snd_2932_ = lean_ctor_get(v___x_2930_, 1);
                v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2930_)) as u8;
                if v_isSharedCheck_2942_ == 0 {
                    v___x_2934_ = v___x_2930_;
                    v_isShared_2935_ = v_isSharedCheck_2942_;
                    state = 24;
                    continue;
                } else {
                    lean_inc(v_snd_2932_);
                    lean_inc(v_fst_2931_);
                    lean_dec(v___x_2930_);
                    v___x_2934_ = lean_box(0);
                    v_isShared_2935_ = v_isSharedCheck_2942_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_2927_ == 0 {
                    lean_ctor_set(v___x_2926_, 5, v_fst_2931_);
                    lean_ctor_set(v___x_2926_, 3, v___x_2929_);
                    lean_ctor_set(v___x_2926_, 0, v___x_2928_);
                    v___x_2937_ = v___x_2926_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(5, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_i_2920_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_offset_2921_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 3, v___x_2929_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 4, v_ty_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 5, v_fst_2931_);
                    v___x_2937_ = v_reuseFailAlloc_2941_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_2935_ == 0 {
                    lean_ctor_set(v___x_2934_, 0, v___x_2937_);
                    v___x_2939_ = v___x_2934_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_snd_2932_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2939_;
            }
            27 => {
                v___x_2952_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2944_, v_a_2778_);
                lean_dec(v_x_2944_);
                v___x_2953_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2948_, v_a_2778_, v_a_2779_);
                v_fst_2954_ = lean_ctor_get(v___x_2953_, 0);
                v_snd_2955_ = lean_ctor_get(v___x_2953_, 1);
                v_isSharedCheck_2965_ = (!lean_is_exclusive(v___x_2953_)) as u8;
                if v_isSharedCheck_2965_ == 0 {
                    v___x_2957_ = v___x_2953_;
                    v_isShared_2958_ = v_isSharedCheck_2965_;
                    state = 28;
                    continue;
                } else {
                    lean_inc(v_snd_2955_);
                    lean_inc(v_fst_2954_);
                    lean_dec(v___x_2953_);
                    v___x_2957_ = lean_box(0);
                    v_isShared_2958_ = v_isSharedCheck_2965_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2951_ == 0 {
                    lean_ctor_set(v___x_2950_, 2, v_fst_2954_);
                    lean_ctor_set(v___x_2950_, 0, v___x_2952_);
                    v___x_2960_ = v___x_2950_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2964_ = lean_alloc_ctor(6, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2952_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_n_2945_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_fst_2954_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2964_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_2946_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2964_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_2947_,
                    );
                    v___x_2960_ = v_reuseFailAlloc_2964_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_2958_ == 0 {
                    lean_ctor_set(v___x_2957_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2957_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_snd_2955_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2962_;
            }
            31 => {
                v___x_2975_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2967_, v_a_2778_);
                lean_dec(v_x_2967_);
                v___x_2976_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2971_, v_a_2778_, v_a_2779_);
                v_fst_2977_ = lean_ctor_get(v___x_2976_, 0);
                v_snd_2978_ = lean_ctor_get(v___x_2976_, 1);
                v_isSharedCheck_2988_ = (!lean_is_exclusive(v___x_2976_)) as u8;
                if v_isSharedCheck_2988_ == 0 {
                    v___x_2980_ = v___x_2976_;
                    v_isShared_2981_ = v_isSharedCheck_2988_;
                    state = 32;
                    continue;
                } else {
                    lean_inc(v_snd_2978_);
                    lean_inc(v_fst_2977_);
                    lean_dec(v___x_2976_);
                    v___x_2980_ = lean_box(0);
                    v_isShared_2981_ = v_isSharedCheck_2988_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2974_ == 0 {
                    lean_ctor_set(v___x_2973_, 2, v_fst_2977_);
                    lean_ctor_set(v___x_2973_, 0, v___x_2975_);
                    v___x_2983_ = v___x_2973_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = lean_alloc_ctor(7, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2975_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_n_2968_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_fst_2977_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2987_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_2969_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2987_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_2970_,
                    );
                    v___x_2983_ = v_reuseFailAlloc_2987_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_2981_ == 0 {
                    lean_ctor_set(v___x_2980_, 0, v___x_2983_);
                    v___x_2985_ = v___x_2980_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_snd_2978_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2985_;
            }
            35 => {
                v___x_2995_ = l_Lean_IR_NormalizeIds_normIndex(v_x_2990_, v_a_2778_);
                lean_dec(v_x_2990_);
                v___x_2996_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_2991_, v_a_2778_, v_a_2779_);
                v_fst_2997_ = lean_ctor_get(v___x_2996_, 0);
                v_snd_2998_ = lean_ctor_get(v___x_2996_, 1);
                v_isSharedCheck_3008_ = (!lean_is_exclusive(v___x_2996_)) as u8;
                if v_isSharedCheck_3008_ == 0 {
                    v___x_3000_ = v___x_2996_;
                    v_isShared_3001_ = v_isSharedCheck_3008_;
                    state = 36;
                    continue;
                } else {
                    lean_inc(v_snd_2998_);
                    lean_inc(v_fst_2997_);
                    lean_dec(v___x_2996_);
                    v___x_3000_ = lean_box(0);
                    v_isShared_3001_ = v_isSharedCheck_3008_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_2994_ == 0 {
                    lean_ctor_set(v___x_2993_, 1, v_fst_2997_);
                    lean_ctor_set(v___x_2993_, 0, v___x_2995_);
                    v___x_3003_ = v___x_2993_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2995_);
                    lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_fst_2997_);
                    v___x_3003_ = v_reuseFailAlloc_3007_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3001_ == 0 {
                    lean_ctor_set(v___x_3000_, 0, v___x_3003_);
                    v___x_3005_ = v___x_3000_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_snd_2998_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3005_;
            }
            39 => {
                v___x_3017_ = l_Lean_IR_NormalizeIds_normIndex(v_x_3011_, v_a_2778_);
                lean_dec(v_x_3011_);
                v_sz_3018_ = lean_array_size(v_cs_3013_);
                v___x_3019_ = 0usize;
                v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_3018_, v___x_3019_, v_cs_3013_, v_a_2778_, v_a_2779_);
                v_fst_3021_ = lean_ctor_get(v___x_3020_, 0);
                v_snd_3022_ = lean_ctor_get(v___x_3020_, 1);
                v_isSharedCheck_3032_ = (!lean_is_exclusive(v___x_3020_)) as u8;
                if v_isSharedCheck_3032_ == 0 {
                    v___x_3024_ = v___x_3020_;
                    v_isShared_3025_ = v_isSharedCheck_3032_;
                    state = 40;
                    continue;
                } else {
                    lean_inc(v_snd_3022_);
                    lean_inc(v_fst_3021_);
                    lean_dec(v___x_3020_);
                    v___x_3024_ = lean_box(0);
                    v_isShared_3025_ = v_isSharedCheck_3032_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3016_ == 0 {
                    lean_ctor_set(v___x_3015_, 3, v_fst_3021_);
                    lean_ctor_set(v___x_3015_, 1, v___x_3017_);
                    v___x_3027_ = v___x_3015_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = lean_alloc_ctor(9, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_tid_3010_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3017_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_xType_3012_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_fst_3021_);
                    v___x_3027_ = v_reuseFailAlloc_3031_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3025_ == 0 {
                    lean_ctor_set(v___x_3024_, 0, v___x_3027_);
                    v___x_3029_ = v___x_3024_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_snd_3022_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3029_;
            }
            43 => {
                v___x_3038_ = l_Lean_IR_NormalizeIds_normArg(v_x_3034_, v_a_2778_);
                if v_isShared_3037_ == 0 {
                    lean_ctor_set(v___x_3036_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3036_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = lean_alloc_ctor(10, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3038_);
                    v___x_3040_ = v_reuseFailAlloc_3042_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3041_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3041_, 0, v___x_3040_);
                lean_ctor_set(v___x_3041_, 1, v_a_2779_);
                return v___x_3041_;
            }
            45 => {
                v___x_3049_ = l_Lean_IR_NormalizeIds_normIndex(v_j_3044_, v_a_2778_);
                lean_dec(v_j_3044_);
                v___x_3050_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_3045_, v_a_2778_);
                if v_isShared_3048_ == 0 {
                    lean_ctor_set(v___x_3047_, 1, v___x_3050_);
                    lean_ctor_set(v___x_3047_, 0, v___x_3049_);
                    v___x_3052_ = v___x_3047_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = lean_alloc_ctor(11, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3050_);
                    v___x_3052_ = v_reuseFailAlloc_3054_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                v___x_3053_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3053_, 0, v___x_3052_);
                lean_ctor_set(v___x_3053_, 1, v_a_2779_);
                return v___x_3053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(
    mut v_sz_3057_: usize,
    mut v_i_3058_: usize,
    mut v_bs_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3078_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_b_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3062_ = lean_usize_dec_lt(v_i_3058_, v_sz_3057_);
                if v___x_3062_ == 0 {
                    v___x_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3063_, 0, v_bs_3059_);
                    lean_ctor_set(v___x_3063_, 1, v___y_3061_);
                    return v___x_3063_;
                } else {
                    v_v_3064_ = lean_array_uget(v_bs_3059_, v_i_3058_);
                    v___x_3065_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3066_ = lean_array_uset(v_bs_3059_, v_i_3058_, v___x_3065_);
                    if lean_obj_tag(v_v_3064_) == 0 {
                        v_info_3074_ = lean_ctor_get(v_v_3064_, 0);
                        v_b_3075_ = lean_ctor_get(v_v_3064_, 1);
                        v_isSharedCheck_3085_ = (!lean_is_exclusive(v_v_3064_)) as u8;
                        if v_isSharedCheck_3085_ == 0 {
                            v___x_3077_ = v_v_3064_;
                            v_isShared_3078_ = v_isSharedCheck_3085_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_b_3075_);
                            lean_inc(v_info_3074_);
                            lean_dec(v_v_3064_);
                            v___x_3077_ = lean_box(0);
                            v_isShared_3078_ = v_isSharedCheck_3085_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_b_3086_ = lean_ctor_get(v_v_3064_, 0);
                        v_isSharedCheck_3096_ = (!lean_is_exclusive(v_v_3064_)) as u8;
                        if v_isSharedCheck_3096_ == 0 {
                            v___x_3088_ = v_v_3064_;
                            v_isShared_3089_ = v_isSharedCheck_3096_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_b_3086_);
                            lean_dec(v_v_3064_);
                            v___x_3088_ = lean_box(0);
                            v_isShared_3089_ = v_isSharedCheck_3096_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3070_ = 1usize;
                v___x_3071_ = lean_usize_add(v_i_3058_, v___x_3070_);
                v___x_3072_ = lean_array_uset(v_bs_x27_3066_, v_i_3058_, v_fst_3068_);
                v_i_3058_ = v___x_3071_;
                v_bs_3059_ = v___x_3072_;
                v___y_3061_ = v_snd_3069_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3079_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_b_3075_, v___y_3060_, v___y_3061_);
                v_fst_3080_ = lean_ctor_get(v___x_3079_, 0);
                lean_inc(v_fst_3080_);
                v_snd_3081_ = lean_ctor_get(v___x_3079_, 1);
                lean_inc(v_snd_3081_);
                lean_dec_ref(v___x_3079_);
                if v_isShared_3078_ == 0 {
                    lean_ctor_set(v___x_3077_, 1, v_fst_3080_);
                    v___x_3083_ = v___x_3077_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_info_3074_);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_fst_3080_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_3068_ = v___x_3083_;
                v_snd_3069_ = v_snd_3081_;
                state = 1;
                continue;
            }
            4 => {
                v___x_3090_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_b_3086_, v___y_3060_, v___y_3061_);
                v_fst_3091_ = lean_ctor_get(v___x_3090_, 0);
                lean_inc(v_fst_3091_);
                v_snd_3092_ = lean_ctor_get(v___x_3090_, 1);
                lean_inc(v_snd_3092_);
                lean_dec_ref(v___x_3090_);
                if v_isShared_3089_ == 0 {
                    lean_ctor_set(v___x_3088_, 0, v_fst_3091_);
                    v___x_3094_ = v___x_3088_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_fst_3091_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_3068_ = v___x_3094_;
                v_snd_3069_ = v_snd_3092_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(
    mut v_sz_3097_: *mut LeanObject,
    mut v_i_3098_: *mut LeanObject,
    mut v_bs_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3102_: usize = 0;
    let mut v_i_boxed_3103_: usize = 0;
    let mut v_res_3104_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3102_ = lean_unbox_usize(v_sz_3097_);
    lean_dec(v_sz_3097_);
    v_i_boxed_3103_ = lean_unbox_usize(v_i_3098_);
    lean_dec(v_i_3098_);
    v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_3102_, v_i_boxed_3103_, v_bs_3099_, v___y_3100_, v___y_3101_);
    lean_dec(v___y_3100_);
    return v_res_3104_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normFnBody___boxed(
    mut v_x_3105_: *mut LeanObject,
    mut v_a_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_3105_, v_a_3106_, v_a_3107_);
    lean_dec(v_a_3106_);
    return v_res_3108_;
}
pub unsafe fn l_Lean_IR_NormalizeIds_normDecl(
    mut v_d_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
    mut v_a_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_xs_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v___y_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_d_3109_) == 0 {
                    v_xs_3112_ = lean_ctor_get(v_d_3109_, 1);
                    v_body_3113_ = lean_ctor_get(v_d_3109_, 3);
                    v___x_3132_ = lean_unsigned_to_nat(0);
                    v___x_3133_ = lean_array_get_size(v_xs_3112_);
                    v___x_3134_ = lean_nat_dec_lt(v___x_3132_, v___x_3133_);
                    if v___x_3134_ == 0 {
                        lean_inc(v_a_3110_);
                        v_fst_3115_ = v_a_3110_;
                        v_snd_3116_ = v_a_3111_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3135_ = lean_nat_dec_le(v___x_3133_, v___x_3133_);
                        if v___x_3135_ == 0 {
                            if v___x_3134_ == 0 {
                                lean_inc(v_a_3110_);
                                v_fst_3115_ = v_a_3110_;
                                v_snd_3116_ = v_a_3111_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3136_ = 0usize;
                                v___x_3137_ = lean_usize_of_nat(v___x_3133_);
                                lean_inc(v_a_3110_);
                                v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_3112_, v___x_3136_, v___x_3137_, v_a_3110_, v_a_3111_);
                                v___y_3129_ = v___x_3138_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_3139_ = 0usize;
                            v___x_3140_ = lean_usize_of_nat(v___x_3133_);
                            lean_inc(v_a_3110_);
                            v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_3112_, v___x_3139_, v___x_3140_, v_a_3110_, v_a_3111_);
                            v___y_3129_ = v___x_3141_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_3142_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3142_, 0, v_d_3109_);
                    lean_ctor_set(v___x_3142_, 1, v_a_3111_);
                    return v___x_3142_;
                }
            }
            1 => {
                lean_inc(v_body_3113_);
                v___x_3117_ =
                    l_Lean_IR_NormalizeIds_normFnBody(v_body_3113_, v_fst_3115_, v_snd_3116_);
                lean_dec(v_fst_3115_);
                v_fst_3118_ = lean_ctor_get(v___x_3117_, 0);
                v_snd_3119_ = lean_ctor_get(v___x_3117_, 1);
                v_isSharedCheck_3127_ = (!lean_is_exclusive(v___x_3117_)) as u8;
                if v_isSharedCheck_3127_ == 0 {
                    v___x_3121_ = v___x_3117_;
                    v_isShared_3122_ = v_isSharedCheck_3127_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3119_);
                    lean_inc(v_fst_3118_);
                    lean_dec(v___x_3117_);
                    v___x_3121_ = lean_box(0);
                    v_isShared_3122_ = v_isSharedCheck_3127_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3123_ = l_Lean_IR_Decl_updateBody_x21(v_d_3109_, v_fst_3118_);
                if v_isShared_3122_ == 0 {
                    lean_ctor_set(v___x_3121_, 0, v___x_3123_);
                    v___x_3125_ = v___x_3121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
                    lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_snd_3119_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3125_;
            }
            4 => {
                v_fst_3130_ = lean_ctor_get(v___y_3129_, 0);
                lean_inc(v_fst_3130_);
                v_snd_3131_ = lean_ctor_get(v___y_3129_, 1);
                lean_inc(v_snd_3131_);
                lean_dec_ref(v___y_3129_);
                v_fst_3115_ = v_fst_3130_;
                v_snd_3116_ = v_snd_3131_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_NormalizeIds_normDecl___boxed(
    mut v_d_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3146_: *mut LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Lean_IR_NormalizeIds_normDecl(v_d_3143_, v_a_3144_, v_a_3145_);
    lean_dec(v_a_3144_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_IR_Decl_normalizeIds(mut v_d_3147_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3151_: *mut LeanObject = core::ptr::null_mut();
    v___x_3148_ = lean_box(1);
    v___x_3149_ = lean_unsigned_to_nat(1);
    v___x_3150_ = l_Lean_IR_NormalizeIds_normDecl(v_d_3147_, v___x_3148_, v___x_3149_);
    v_fst_3151_ = lean_ctor_get(v___x_3150_, 0);
    lean_inc(v_fst_3151_);
    lean_dec_ref(v___x_3150_);
    return v_fst_3151_;
}
pub unsafe fn l_Lean_IR_MapVars_mapArg(
    mut v_f_3152_: *mut LeanObject,
    mut v_x_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3153_) == 0 {
                    v_id_3154_ = lean_ctor_get(v_x_3153_, 0);
                    v_isSharedCheck_3162_ = (!lean_is_exclusive(v_x_3153_)) as u8;
                    if v_isSharedCheck_3162_ == 0 {
                        v___x_3156_ = v_x_3153_;
                        v_isShared_3157_ = v_isSharedCheck_3162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_id_3154_);
                        lean_dec(v_x_3153_);
                        v___x_3156_ = lean_box(0);
                        v_isShared_3157_ = v_isSharedCheck_3162_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_3152_);
                    return v_x_3153_;
                }
            }
            1 => {
                v___x_3158_ = lean_apply_1(v_f_3152_, v_id_3154_);
                if v_isShared_3157_ == 0 {
                    lean_ctor_set(v___x_3156_, 0, v___x_3158_);
                    v___x_3160_ = v___x_3156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
                    v___x_3160_ = v_reuseFailAlloc_3161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(
    mut v_f_3163_: *mut LeanObject,
    mut v_sz_3164_: usize,
    mut v_i_3165_: usize,
    mut v_bs_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3167_: u8 = 0;
    let mut v_v_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3167_ = lean_usize_dec_lt(v_i_3165_, v_sz_3164_);
                if v___x_3167_ == 0 {
                    lean_dec_ref(v_f_3163_);
                    return v_bs_3166_;
                } else {
                    v_v_3168_ = lean_array_uget(v_bs_3166_, v_i_3165_);
                    v___x_3169_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3170_ = lean_array_uset(v_bs_3166_, v_i_3165_, v___x_3169_);
                    if lean_obj_tag(v_v_3168_) == 0 {
                        v_id_3177_ = lean_ctor_get(v_v_3168_, 0);
                        v_isSharedCheck_3185_ = (!lean_is_exclusive(v_v_3168_)) as u8;
                        if v_isSharedCheck_3185_ == 0 {
                            v___x_3179_ = v_v_3168_;
                            v_isShared_3180_ = v_isSharedCheck_3185_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_3177_);
                            lean_dec(v_v_3168_);
                            v___x_3179_ = lean_box(0);
                            v_isShared_3180_ = v_isSharedCheck_3185_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_3172_ = v_v_3168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3173_ = 1usize;
                v___x_3174_ = lean_usize_add(v_i_3165_, v___x_3173_);
                v___x_3175_ = lean_array_uset(v_bs_x27_3170_, v_i_3165_, v___y_3172_);
                v_i_3165_ = v___x_3174_;
                v_bs_3166_ = v___x_3175_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc_ref(v_f_3163_);
                v___x_3181_ = lean_apply_1(v_f_3163_, v_id_3177_);
                if v_isShared_3180_ == 0 {
                    lean_ctor_set(v___x_3179_, 0, v___x_3181_);
                    v___x_3183_ = v___x_3179_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3172_ = v___x_3183_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(
    mut v_f_3186_: *mut LeanObject,
    mut v_sz_3187_: *mut LeanObject,
    mut v_i_3188_: *mut LeanObject,
    mut v_bs_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3190_: usize = 0;
    let mut v_i_boxed_3191_: usize = 0;
    let mut v_res_3192_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3190_ = lean_unbox_usize(v_sz_3187_);
    lean_dec(v_sz_3187_);
    v_i_boxed_3191_ = lean_unbox_usize(v_i_3188_);
    lean_dec(v_i_3188_);
    v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_3186_, v_sz_boxed_3190_, v_i_boxed_3191_, v_bs_3189_);
    return v_res_3192_;
}
pub unsafe fn l_Lean_IR_MapVars_mapArgs(
    mut v_f_3193_: *mut LeanObject,
    mut v_as_3194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3195_: usize = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3195_ = lean_array_size(v_as_3194_);
    v___x_3196_ = 0usize;
    v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_3193_, v_sz_3195_, v___x_3196_, v_as_3194_);
    return v___x_3197_;
}
pub unsafe fn l_Lean_IR_MapVars_mapExpr(
    mut v_f_3198_: *mut LeanObject,
    mut v_x_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_n_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v_x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_3222_: u8 = 0;
    let mut v_ys_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_i_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v_i_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_n_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_c_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_c_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v_x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut v_ty_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3199_) {
                0 => {
                    v_i_3200_ = lean_ctor_get(v_x_3199_, 0);
                    v_ys_3201_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3209_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3203_ = v_x_3199_;
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_ys_3201_);
                        lean_inc(v_i_3200_);
                        lean_dec(v_x_3199_);
                        v___x_3203_ = lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_n_3210_ = lean_ctor_get(v_x_3199_, 0);
                    v_x_3211_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3219_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v___x_3213_ = v_x_3199_;
                        v_isShared_3214_ = v_isSharedCheck_3219_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_x_3211_);
                        lean_inc(v_n_3210_);
                        lean_dec(v_x_3199_);
                        v___x_3213_ = lean_box(0);
                        v_isShared_3214_ = v_isSharedCheck_3219_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_x_3220_ = lean_ctor_get(v_x_3199_, 0);
                    v_i_3221_ = lean_ctor_get(v_x_3199_, 1);
                    v_updtHeader_3222_ = lean_ctor_get_uint8(
                        v_x_3199_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_ys_3223_ = lean_ctor_get(v_x_3199_, 2);
                    v_isSharedCheck_3232_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3225_ = v_x_3199_;
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_ys_3223_);
                        lean_inc(v_i_3221_);
                        lean_inc(v_x_3220_);
                        lean_dec(v_x_3199_);
                        v___x_3225_ = lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_3233_ = lean_ctor_get(v_x_3199_, 0);
                    v_x_3234_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3242_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3242_ == 0 {
                        v___x_3236_ = v_x_3199_;
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_x_3234_);
                        lean_inc(v_i_3233_);
                        lean_dec(v_x_3199_);
                        v___x_3236_ = lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_i_3243_ = lean_ctor_get(v_x_3199_, 0);
                    v_x_3244_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3252_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3252_ == 0 {
                        v___x_3246_ = v_x_3199_;
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_x_3244_);
                        lean_inc(v_i_3243_);
                        lean_dec(v_x_3199_);
                        v___x_3246_ = lean_box(0);
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 9;
                        continue;
                    }
                }
                5 => {
                    v_n_3253_ = lean_ctor_get(v_x_3199_, 0);
                    v_offset_3254_ = lean_ctor_get(v_x_3199_, 1);
                    v_x_3255_ = lean_ctor_get(v_x_3199_, 2);
                    v_isSharedCheck_3263_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3263_ == 0 {
                        v___x_3257_ = v_x_3199_;
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_x_3255_);
                        lean_inc(v_offset_3254_);
                        lean_inc(v_n_3253_);
                        lean_dec(v_x_3199_);
                        v___x_3257_ = lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 11;
                        continue;
                    }
                }
                6 => {
                    v_c_3264_ = lean_ctor_get(v_x_3199_, 0);
                    v_ys_3265_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3273_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3267_ = v_x_3199_;
                        v_isShared_3268_ = v_isSharedCheck_3273_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_ys_3265_);
                        lean_inc(v_c_3264_);
                        lean_dec(v_x_3199_);
                        v___x_3267_ = lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3273_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_c_3274_ = lean_ctor_get(v_x_3199_, 0);
                    v_ys_3275_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3283_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v___x_3277_ = v_x_3199_;
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_ys_3275_);
                        lean_inc(v_c_3274_);
                        lean_dec(v_x_3199_);
                        v___x_3277_ = lean_box(0);
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_x_3284_ = lean_ctor_get(v_x_3199_, 0);
                    v_ys_3285_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3294_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3287_ = v_x_3199_;
                        v_isShared_3288_ = v_isSharedCheck_3294_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_ys_3285_);
                        lean_inc(v_x_3284_);
                        lean_dec(v_x_3199_);
                        v___x_3287_ = lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3294_;
                        state = 17;
                        continue;
                    }
                }
                9 => {
                    v_ty_3295_ = lean_ctor_get(v_x_3199_, 0);
                    v_x_3296_ = lean_ctor_get(v_x_3199_, 1);
                    v_isSharedCheck_3304_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3304_ == 0 {
                        v___x_3298_ = v_x_3199_;
                        v_isShared_3299_ = v_isSharedCheck_3304_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_x_3296_);
                        lean_inc(v_ty_3295_);
                        lean_dec(v_x_3199_);
                        v___x_3298_ = lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3304_;
                        state = 19;
                        continue;
                    }
                }
                10 => {
                    v_x_3305_ = lean_ctor_get(v_x_3199_, 0);
                    v_isSharedCheck_3313_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v___x_3307_ = v_x_3199_;
                        v_isShared_3308_ = v_isSharedCheck_3313_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_x_3305_);
                        lean_dec(v_x_3199_);
                        v___x_3307_ = lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3313_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    lean_dec_ref(v_f_3198_);
                    return v_x_3199_;
                }
                _ => {
                    v_x_3314_ = lean_ctor_get(v_x_3199_, 0);
                    v_isSharedCheck_3322_ = (!lean_is_exclusive(v_x_3199_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3316_ = v_x_3199_;
                        v_isShared_3317_ = v_isSharedCheck_3322_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_x_3314_);
                        lean_dec(v_x_3199_);
                        v___x_3316_ = lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3322_;
                        state = 23;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3205_ = l_Lean_IR_MapVars_mapArgs(v_f_3198_, v_ys_3201_);
                if v_isShared_3204_ == 0 {
                    lean_ctor_set(v___x_3203_, 1, v___x_3205_);
                    v___x_3207_ = v___x_3203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_i_3200_);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 1, v___x_3205_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3207_;
            }
            3 => {
                v___x_3215_ = lean_apply_1(v_f_3198_, v_x_3211_);
                if v_isShared_3214_ == 0 {
                    lean_ctor_set(v___x_3213_, 1, v___x_3215_);
                    v___x_3217_ = v___x_3213_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_n_3210_);
                    lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3215_);
                    v___x_3217_ = v_reuseFailAlloc_3218_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3217_;
            }
            5 => {
                lean_inc_ref(v_f_3198_);
                v___x_3227_ = lean_apply_1(v_f_3198_, v_x_3220_);
                v___x_3228_ = l_Lean_IR_MapVars_mapArgs(v_f_3198_, v_ys_3223_);
                if v_isShared_3226_ == 0 {
                    lean_ctor_set(v___x_3225_, 2, v___x_3228_);
                    lean_ctor_set(v___x_3225_, 0, v___x_3227_);
                    v___x_3230_ = v___x_3225_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(2, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3227_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_i_3221_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 2, v___x_3228_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3231_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_updtHeader_3222_,
                    );
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3230_;
            }
            7 => {
                v___x_3238_ = lean_apply_1(v_f_3198_, v_x_3234_);
                if v_isShared_3237_ == 0 {
                    lean_ctor_set(v___x_3236_, 1, v___x_3238_);
                    v___x_3240_ = v___x_3236_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_i_3233_);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3238_);
                    v___x_3240_ = v_reuseFailAlloc_3241_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3240_;
            }
            9 => {
                v___x_3248_ = lean_apply_1(v_f_3198_, v_x_3244_);
                if v_isShared_3247_ == 0 {
                    lean_ctor_set(v___x_3246_, 1, v___x_3248_);
                    v___x_3250_ = v___x_3246_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_i_3243_);
                    lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3250_;
            }
            11 => {
                v___x_3259_ = lean_apply_1(v_f_3198_, v_x_3255_);
                if v_isShared_3258_ == 0 {
                    lean_ctor_set(v___x_3257_, 2, v___x_3259_);
                    v___x_3261_ = v___x_3257_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(5, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_n_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_offset_3254_);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 2, v___x_3259_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3261_;
            }
            13 => {
                v___x_3269_ = l_Lean_IR_MapVars_mapArgs(v_f_3198_, v_ys_3265_);
                if v_isShared_3268_ == 0 {
                    lean_ctor_set(v___x_3267_, 1, v___x_3269_);
                    v___x_3271_ = v___x_3267_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_c_3264_);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3269_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3271_;
            }
            15 => {
                v___x_3279_ = l_Lean_IR_MapVars_mapArgs(v_f_3198_, v_ys_3275_);
                if v_isShared_3278_ == 0 {
                    lean_ctor_set(v___x_3277_, 1, v___x_3279_);
                    v___x_3281_ = v___x_3277_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_c_3274_);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 1, v___x_3279_);
                    v___x_3281_ = v_reuseFailAlloc_3282_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3281_;
            }
            17 => {
                lean_inc_ref(v_f_3198_);
                v___x_3289_ = lean_apply_1(v_f_3198_, v_x_3284_);
                v___x_3290_ = l_Lean_IR_MapVars_mapArgs(v_f_3198_, v_ys_3285_);
                if v_isShared_3288_ == 0 {
                    lean_ctor_set(v___x_3287_, 1, v___x_3290_);
                    lean_ctor_set(v___x_3287_, 0, v___x_3289_);
                    v___x_3292_ = v___x_3287_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3289_);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3290_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3292_;
            }
            19 => {
                v___x_3300_ = lean_apply_1(v_f_3198_, v_x_3296_);
                if v_isShared_3299_ == 0 {
                    lean_ctor_set(v___x_3298_, 1, v___x_3300_);
                    v___x_3302_ = v___x_3298_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(9, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_ty_3295_);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3300_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3302_;
            }
            21 => {
                v___x_3309_ = lean_apply_1(v_f_3198_, v_x_3305_);
                if v_isShared_3308_ == 0 {
                    lean_ctor_set(v___x_3307_, 0, v___x_3309_);
                    v___x_3311_ = v___x_3307_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3312_ = lean_alloc_ctor(10, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
                    v___x_3311_ = v_reuseFailAlloc_3312_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3311_;
            }
            23 => {
                v___x_3318_ = lean_apply_1(v_f_3198_, v_x_3314_);
                if v_isShared_3317_ == 0 {
                    lean_ctor_set(v___x_3316_, 0, v___x_3318_);
                    v___x_3320_ = v___x_3316_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = lean_alloc_ctor(12, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
                    v___x_3320_ = v_reuseFailAlloc_3321_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_MapVars_mapFnBody(
    mut v_f_3323_: *mut LeanObject,
    mut v_x_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_j_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v_x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3400_: u8 = 0;
    let mut v_x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3409_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3419_: u8 = 0;
    let mut v_persistent_3420_: u8 = 0;
    let mut v_b_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3430_: u8 = 0;
    let mut v_x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3433_: u8 = 0;
    let mut v_persistent_3434_: u8 = 0;
    let mut v_b_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_tid_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xType_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3464_: usize = 0;
    let mut v___x_3465_: usize = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut v_x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_id_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3486_: u8 = 0;
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v_unused_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3324_) {
                0 => {
                    v_x_3325_ = lean_ctor_get(v_x_3324_, 0);
                    v_ty_3326_ = lean_ctor_get(v_x_3324_, 1);
                    v_e_3327_ = lean_ctor_get(v_x_3324_, 2);
                    v_b_3328_ = lean_ctor_get(v_x_3324_, 3);
                    v_isSharedCheck_3337_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3337_ == 0 {
                        v___x_3330_ = v_x_3324_;
                        v_isShared_3331_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_b_3328_);
                        lean_inc(v_e_3327_);
                        lean_inc(v_ty_3326_);
                        lean_inc(v_x_3325_);
                        lean_dec(v_x_3324_);
                        v___x_3330_ = lean_box(0);
                        v_isShared_3331_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_3338_ = lean_ctor_get(v_x_3324_, 0);
                    v_xs_3339_ = lean_ctor_get(v_x_3324_, 1);
                    v_v_3340_ = lean_ctor_get(v_x_3324_, 2);
                    v_b_3341_ = lean_ctor_get(v_x_3324_, 3);
                    v_isSharedCheck_3350_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3343_ = v_x_3324_;
                        v_isShared_3344_ = v_isSharedCheck_3350_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_b_3341_);
                        lean_inc(v_v_3340_);
                        lean_inc(v_xs_3339_);
                        lean_inc(v_j_3338_);
                        lean_dec(v_x_3324_);
                        v___x_3343_ = lean_box(0);
                        v_isShared_3344_ = v_isSharedCheck_3350_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_x_3351_ = lean_ctor_get(v_x_3324_, 0);
                    v_i_3352_ = lean_ctor_get(v_x_3324_, 1);
                    v_y_3353_ = lean_ctor_get(v_x_3324_, 2);
                    v_b_3354_ = lean_ctor_get(v_x_3324_, 3);
                    v_isSharedCheck_3374_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3356_ = v_x_3324_;
                        v_isShared_3357_ = v_isSharedCheck_3374_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_b_3354_);
                        lean_inc(v_y_3353_);
                        lean_inc(v_i_3352_);
                        lean_inc(v_x_3351_);
                        lean_dec(v_x_3324_);
                        v___x_3356_ = lean_box(0);
                        v_isShared_3357_ = v_isSharedCheck_3374_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_x_3375_ = lean_ctor_get(v_x_3324_, 0);
                    v_cidx_3376_ = lean_ctor_get(v_x_3324_, 1);
                    v_b_3377_ = lean_ctor_get(v_x_3324_, 2);
                    v_isSharedCheck_3386_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3386_ == 0 {
                        v___x_3379_ = v_x_3324_;
                        v_isShared_3380_ = v_isSharedCheck_3386_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_b_3377_);
                        lean_inc(v_cidx_3376_);
                        lean_inc(v_x_3375_);
                        lean_dec(v_x_3324_);
                        v___x_3379_ = lean_box(0);
                        v_isShared_3380_ = v_isSharedCheck_3386_;
                        state = 10;
                        continue;
                    }
                }
                4 => {
                    v_x_3387_ = lean_ctor_get(v_x_3324_, 0);
                    v_i_3388_ = lean_ctor_get(v_x_3324_, 1);
                    v_y_3389_ = lean_ctor_get(v_x_3324_, 2);
                    v_b_3390_ = lean_ctor_get(v_x_3324_, 3);
                    v_isSharedCheck_3400_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3400_ == 0 {
                        v___x_3392_ = v_x_3324_;
                        v_isShared_3393_ = v_isSharedCheck_3400_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_b_3390_);
                        lean_inc(v_y_3389_);
                        lean_inc(v_i_3388_);
                        lean_inc(v_x_3387_);
                        lean_dec(v_x_3324_);
                        v___x_3392_ = lean_box(0);
                        v_isShared_3393_ = v_isSharedCheck_3400_;
                        state = 12;
                        continue;
                    }
                }
                5 => {
                    v_x_3401_ = lean_ctor_get(v_x_3324_, 0);
                    v_i_3402_ = lean_ctor_get(v_x_3324_, 1);
                    v_offset_3403_ = lean_ctor_get(v_x_3324_, 2);
                    v_y_3404_ = lean_ctor_get(v_x_3324_, 3);
                    v_ty_3405_ = lean_ctor_get(v_x_3324_, 4);
                    v_b_3406_ = lean_ctor_get(v_x_3324_, 5);
                    v_isSharedCheck_3416_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3408_ = v_x_3324_;
                        v_isShared_3409_ = v_isSharedCheck_3416_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_b_3406_);
                        lean_inc(v_ty_3405_);
                        lean_inc(v_y_3404_);
                        lean_inc(v_offset_3403_);
                        lean_inc(v_i_3402_);
                        lean_inc(v_x_3401_);
                        lean_dec(v_x_3324_);
                        v___x_3408_ = lean_box(0);
                        v_isShared_3409_ = v_isSharedCheck_3416_;
                        state = 14;
                        continue;
                    }
                }
                6 => {
                    v_x_3417_ = lean_ctor_get(v_x_3324_, 0);
                    v_n_3418_ = lean_ctor_get(v_x_3324_, 1);
                    v_c_3419_ = lean_ctor_get_uint8(
                        v_x_3324_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_3420_ = lean_ctor_get_uint8(
                        v_x_3324_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_b_3421_ = lean_ctor_get(v_x_3324_, 2);
                    v_isSharedCheck_3430_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3430_ == 0 {
                        v___x_3423_ = v_x_3324_;
                        v_isShared_3424_ = v_isSharedCheck_3430_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_b_3421_);
                        lean_inc(v_n_3418_);
                        lean_inc(v_x_3417_);
                        lean_dec(v_x_3324_);
                        v___x_3423_ = lean_box(0);
                        v_isShared_3424_ = v_isSharedCheck_3430_;
                        state = 16;
                        continue;
                    }
                }
                7 => {
                    v_x_3431_ = lean_ctor_get(v_x_3324_, 0);
                    v_n_3432_ = lean_ctor_get(v_x_3324_, 1);
                    v_c_3433_ = lean_ctor_get_uint8(
                        v_x_3324_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_3434_ = lean_ctor_get_uint8(
                        v_x_3324_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_b_3435_ = lean_ctor_get(v_x_3324_, 2);
                    v_isSharedCheck_3444_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3444_ == 0 {
                        v___x_3437_ = v_x_3324_;
                        v_isShared_3438_ = v_isSharedCheck_3444_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_b_3435_);
                        lean_inc(v_n_3432_);
                        lean_inc(v_x_3431_);
                        lean_dec(v_x_3324_);
                        v___x_3437_ = lean_box(0);
                        v_isShared_3438_ = v_isSharedCheck_3444_;
                        state = 18;
                        continue;
                    }
                }
                8 => {
                    v_x_3445_ = lean_ctor_get(v_x_3324_, 0);
                    v_b_3446_ = lean_ctor_get(v_x_3324_, 1);
                    v_isSharedCheck_3455_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3448_ = v_x_3324_;
                        v_isShared_3449_ = v_isSharedCheck_3455_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_b_3446_);
                        lean_inc(v_x_3445_);
                        lean_dec(v_x_3324_);
                        v___x_3448_ = lean_box(0);
                        v_isShared_3449_ = v_isSharedCheck_3455_;
                        state = 20;
                        continue;
                    }
                }
                9 => {
                    v_tid_3456_ = lean_ctor_get(v_x_3324_, 0);
                    v_x_3457_ = lean_ctor_get(v_x_3324_, 1);
                    v_xType_3458_ = lean_ctor_get(v_x_3324_, 2);
                    v_cs_3459_ = lean_ctor_get(v_x_3324_, 3);
                    v_isSharedCheck_3470_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3470_ == 0 {
                        v___x_3461_ = v_x_3324_;
                        v_isShared_3462_ = v_isSharedCheck_3470_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_cs_3459_);
                        lean_inc(v_xType_3458_);
                        lean_inc(v_x_3457_);
                        lean_inc(v_tid_3456_);
                        lean_dec(v_x_3324_);
                        v___x_3461_ = lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3470_;
                        state = 22;
                        continue;
                    }
                }
                10 => {
                    v_x_3471_ = lean_ctor_get(v_x_3324_, 0);
                    lean_inc(v_x_3471_);
                    if lean_obj_tag(v_x_3471_) == 0 {
                        v_isSharedCheck_3487_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                        if v_isSharedCheck_3487_ == 0 {
                            v_unused_3488_ = lean_ctor_get(v_x_3324_, 0);
                            lean_dec(v_unused_3488_);
                            v___x_3473_ = v_x_3324_;
                            v_isShared_3474_ = v_isSharedCheck_3487_;
                            state = 24;
                            continue;
                        } else {
                            lean_dec(v_x_3324_);
                            v___x_3473_ = lean_box(0);
                            v_isShared_3474_ = v_isSharedCheck_3487_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_f_3323_);
                        return v_x_3324_;
                    }
                }
                11 => {
                    v_j_3489_ = lean_ctor_get(v_x_3324_, 0);
                    v_ys_3490_ = lean_ctor_get(v_x_3324_, 1);
                    v_isSharedCheck_3498_ = (!lean_is_exclusive(v_x_3324_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v___x_3492_ = v_x_3324_;
                        v_isShared_3493_ = v_isSharedCheck_3498_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_ys_3490_);
                        lean_inc(v_j_3489_);
                        lean_dec(v_x_3324_);
                        v___x_3492_ = lean_box(0);
                        v_isShared_3493_ = v_isSharedCheck_3498_;
                        state = 28;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_f_3323_);
                    return v_x_3324_;
                }
            },
            1 => {
                lean_inc_ref(v_f_3323_);
                v___x_3332_ = l_Lean_IR_MapVars_mapExpr(v_f_3323_, v_e_3327_);
                v___x_3333_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3328_);
                if v_isShared_3331_ == 0 {
                    lean_ctor_set(v___x_3330_, 3, v___x_3333_);
                    lean_ctor_set(v___x_3330_, 2, v___x_3332_);
                    v___x_3335_ = v___x_3330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_x_3325_);
                    lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_ty_3326_);
                    lean_ctor_set(v_reuseFailAlloc_3336_, 2, v___x_3332_);
                    lean_ctor_set(v_reuseFailAlloc_3336_, 3, v___x_3333_);
                    v___x_3335_ = v_reuseFailAlloc_3336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3335_;
            }
            3 => {
                lean_inc_ref(v_f_3323_);
                v___x_3345_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_v_3340_);
                v___x_3346_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3341_);
                if v_isShared_3344_ == 0 {
                    lean_ctor_set(v___x_3343_, 3, v___x_3346_);
                    lean_ctor_set(v___x_3343_, 2, v___x_3345_);
                    v___x_3348_ = v___x_3343_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_j_3338_);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_xs_3339_);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 2, v___x_3345_);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 3, v___x_3346_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3348_;
            }
            5 => {
                lean_inc_ref(v_f_3323_);
                v___x_3358_ = lean_apply_1(v_f_3323_, v_x_3351_);
                if lean_obj_tag(v_y_3353_) == 0 {
                    v_id_3365_ = lean_ctor_get(v_y_3353_, 0);
                    v_isSharedCheck_3373_ = (!lean_is_exclusive(v_y_3353_)) as u8;
                    if v_isSharedCheck_3373_ == 0 {
                        v___x_3367_ = v_y_3353_;
                        v_isShared_3368_ = v_isSharedCheck_3373_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_id_3365_);
                        lean_dec(v_y_3353_);
                        v___x_3367_ = lean_box(0);
                        v_isShared_3368_ = v_isSharedCheck_3373_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_3360_ = v_y_3353_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3361_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3354_);
                if v_isShared_3357_ == 0 {
                    lean_ctor_set(v___x_3356_, 3, v___x_3361_);
                    lean_ctor_set(v___x_3356_, 2, v___y_3360_);
                    lean_ctor_set(v___x_3356_, 0, v___x_3358_);
                    v___x_3363_ = v___x_3356_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3358_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_i_3352_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 2, v___y_3360_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 3, v___x_3361_);
                    v___x_3363_ = v_reuseFailAlloc_3364_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3363_;
            }
            8 => {
                lean_inc_ref(v_f_3323_);
                v___x_3369_ = lean_apply_1(v_f_3323_, v_id_3365_);
                if v_isShared_3368_ == 0 {
                    lean_ctor_set(v___x_3367_, 0, v___x_3369_);
                    v___x_3371_ = v___x_3367_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3372_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_3360_ = v___x_3371_;
                state = 6;
                continue;
            }
            10 => {
                lean_inc_ref(v_f_3323_);
                v___x_3381_ = lean_apply_1(v_f_3323_, v_x_3375_);
                v___x_3382_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3377_);
                if v_isShared_3380_ == 0 {
                    lean_ctor_set(v___x_3379_, 2, v___x_3382_);
                    lean_ctor_set(v___x_3379_, 0, v___x_3381_);
                    v___x_3384_ = v___x_3379_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3381_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_cidx_3376_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 2, v___x_3382_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3384_;
            }
            12 => {
                lean_inc_ref_n(v_f_3323_, 2);
                v___x_3394_ = lean_apply_1(v_f_3323_, v_x_3387_);
                v___x_3395_ = lean_apply_1(v_f_3323_, v_y_3389_);
                v___x_3396_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3390_);
                if v_isShared_3393_ == 0 {
                    lean_ctor_set(v___x_3392_, 3, v___x_3396_);
                    lean_ctor_set(v___x_3392_, 2, v___x_3395_);
                    lean_ctor_set(v___x_3392_, 0, v___x_3394_);
                    v___x_3398_ = v___x_3392_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3399_ = lean_alloc_ctor(4, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3394_);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_i_3388_);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 2, v___x_3395_);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 3, v___x_3396_);
                    v___x_3398_ = v_reuseFailAlloc_3399_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3398_;
            }
            14 => {
                lean_inc_ref_n(v_f_3323_, 2);
                v___x_3410_ = lean_apply_1(v_f_3323_, v_x_3401_);
                v___x_3411_ = lean_apply_1(v_f_3323_, v_y_3404_);
                v___x_3412_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3406_);
                if v_isShared_3409_ == 0 {
                    lean_ctor_set(v___x_3408_, 5, v___x_3412_);
                    lean_ctor_set(v___x_3408_, 3, v___x_3411_);
                    lean_ctor_set(v___x_3408_, 0, v___x_3410_);
                    v___x_3414_ = v___x_3408_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = lean_alloc_ctor(5, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3410_);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_i_3402_);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_offset_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 3, v___x_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_ty_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 5, v___x_3412_);
                    v___x_3414_ = v_reuseFailAlloc_3415_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3414_;
            }
            16 => {
                lean_inc_ref(v_f_3323_);
                v___x_3425_ = lean_apply_1(v_f_3323_, v_x_3417_);
                v___x_3426_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3421_);
                if v_isShared_3424_ == 0 {
                    lean_ctor_set(v___x_3423_, 2, v___x_3426_);
                    lean_ctor_set(v___x_3423_, 0, v___x_3425_);
                    v___x_3428_ = v___x_3423_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3429_ = lean_alloc_ctor(6, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3425_);
                    lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_n_3418_);
                    lean_ctor_set(v_reuseFailAlloc_3429_, 2, v___x_3426_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3429_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_3419_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3429_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_3420_,
                    );
                    v___x_3428_ = v_reuseFailAlloc_3429_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3428_;
            }
            18 => {
                lean_inc_ref(v_f_3323_);
                v___x_3439_ = lean_apply_1(v_f_3323_, v_x_3431_);
                v___x_3440_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3435_);
                if v_isShared_3438_ == 0 {
                    lean_ctor_set(v___x_3437_, 2, v___x_3440_);
                    lean_ctor_set(v___x_3437_, 0, v___x_3439_);
                    v___x_3442_ = v___x_3437_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = lean_alloc_ctor(7, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3439_);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_n_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 2, v___x_3440_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3443_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_3433_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3443_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_3434_,
                    );
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3442_;
            }
            20 => {
                lean_inc_ref(v_f_3323_);
                v___x_3450_ = lean_apply_1(v_f_3323_, v_x_3445_);
                v___x_3451_ = l_Lean_IR_MapVars_mapFnBody(v_f_3323_, v_b_3446_);
                if v_isShared_3449_ == 0 {
                    lean_ctor_set(v___x_3448_, 1, v___x_3451_);
                    lean_ctor_set(v___x_3448_, 0, v___x_3450_);
                    v___x_3453_ = v___x_3448_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3450_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3453_;
            }
            22 => {
                lean_inc_ref(v_f_3323_);
                v___x_3463_ = lean_apply_1(v_f_3323_, v_x_3457_);
                v_sz_3464_ = lean_array_size(v_cs_3459_);
                v___x_3465_ = 0usize;
                v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_3323_, v_sz_3464_, v___x_3465_, v_cs_3459_);
                if v_isShared_3462_ == 0 {
                    lean_ctor_set(v___x_3461_, 3, v___x_3466_);
                    lean_ctor_set(v___x_3461_, 1, v___x_3463_);
                    v___x_3468_ = v___x_3461_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = lean_alloc_ctor(9, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_tid_3456_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3463_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_xType_3458_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 3, v___x_3466_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3468_;
            }
            24 => {
                v_id_3475_ = lean_ctor_get(v_x_3471_, 0);
                v_isSharedCheck_3486_ = (!lean_is_exclusive(v_x_3471_)) as u8;
                if v_isSharedCheck_3486_ == 0 {
                    v___x_3477_ = v_x_3471_;
                    v_isShared_3478_ = v_isSharedCheck_3486_;
                    state = 25;
                    continue;
                } else {
                    lean_inc(v_id_3475_);
                    lean_dec(v_x_3471_);
                    v___x_3477_ = lean_box(0);
                    v_isShared_3478_ = v_isSharedCheck_3486_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_3479_ = lean_apply_1(v_f_3323_, v_id_3475_);
                if v_isShared_3478_ == 0 {
                    lean_ctor_set(v___x_3477_, 0, v___x_3479_);
                    v___x_3481_ = v___x_3477_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3479_);
                    v___x_3481_ = v_reuseFailAlloc_3485_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_3474_ == 0 {
                    lean_ctor_set(v___x_3473_, 0, v___x_3481_);
                    v___x_3483_ = v___x_3473_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = lean_alloc_ctor(10, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3483_;
            }
            28 => {
                v___x_3494_ = l_Lean_IR_MapVars_mapArgs(v_f_3323_, v_ys_3490_);
                if v_isShared_3493_ == 0 {
                    lean_ctor_set(v___x_3492_, 1, v___x_3494_);
                    v___x_3496_ = v___x_3492_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3497_ = lean_alloc_ctor(11, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_j_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3494_);
                    v___x_3496_ = v_reuseFailAlloc_3497_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(
    mut v_f_3499_: *mut LeanObject,
    mut v_sz_3500_: usize,
    mut v_i_3501_: usize,
    mut v_bs_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3503_: u8 = 0;
    let mut v_v_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: usize = 0;
    let mut v___x_3510_: usize = 0;
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_b_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3503_ = lean_usize_dec_lt(v_i_3501_, v_sz_3500_);
                if v___x_3503_ == 0 {
                    lean_dec_ref(v_f_3499_);
                    return v_bs_3502_;
                } else {
                    v_v_3504_ = lean_array_uget(v_bs_3502_, v_i_3501_);
                    v___x_3505_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3506_ = lean_array_uset(v_bs_3502_, v_i_3501_, v___x_3505_);
                    if lean_obj_tag(v_v_3504_) == 0 {
                        v_info_3513_ = lean_ctor_get(v_v_3504_, 0);
                        v_b_3514_ = lean_ctor_get(v_v_3504_, 1);
                        v_isSharedCheck_3522_ = (!lean_is_exclusive(v_v_3504_)) as u8;
                        if v_isSharedCheck_3522_ == 0 {
                            v___x_3516_ = v_v_3504_;
                            v_isShared_3517_ = v_isSharedCheck_3522_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_b_3514_);
                            lean_inc(v_info_3513_);
                            lean_dec(v_v_3504_);
                            v___x_3516_ = lean_box(0);
                            v_isShared_3517_ = v_isSharedCheck_3522_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_b_3523_ = lean_ctor_get(v_v_3504_, 0);
                        v_isSharedCheck_3531_ = (!lean_is_exclusive(v_v_3504_)) as u8;
                        if v_isSharedCheck_3531_ == 0 {
                            v___x_3525_ = v_v_3504_;
                            v_isShared_3526_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_b_3523_);
                            lean_dec(v_v_3504_);
                            v___x_3525_ = lean_box(0);
                            v_isShared_3526_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3509_ = 1usize;
                v___x_3510_ = lean_usize_add(v_i_3501_, v___x_3509_);
                v___x_3511_ = lean_array_uset(v_bs_x27_3506_, v_i_3501_, v___y_3508_);
                v_i_3501_ = v___x_3510_;
                v_bs_3502_ = v___x_3511_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc_ref(v_f_3499_);
                v___x_3518_ = l_Lean_IR_MapVars_mapFnBody(v_f_3499_, v_b_3514_);
                if v_isShared_3517_ == 0 {
                    lean_ctor_set(v___x_3516_, 1, v___x_3518_);
                    v___x_3520_ = v___x_3516_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_info_3513_);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 1, v___x_3518_);
                    v___x_3520_ = v_reuseFailAlloc_3521_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3508_ = v___x_3520_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc_ref(v_f_3499_);
                v___x_3527_ = l_Lean_IR_MapVars_mapFnBody(v_f_3499_, v_b_3523_);
                if v_isShared_3526_ == 0 {
                    lean_ctor_set(v___x_3525_, 0, v___x_3527_);
                    v___x_3529_ = v___x_3525_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
                    v___x_3529_ = v_reuseFailAlloc_3530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3508_ = v___x_3529_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(
    mut v_f_3532_: *mut LeanObject,
    mut v_sz_3533_: *mut LeanObject,
    mut v_i_3534_: *mut LeanObject,
    mut v_bs_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3536_: usize = 0;
    let mut v_i_boxed_3537_: usize = 0;
    let mut v_res_3538_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3536_ = lean_unbox_usize(v_sz_3533_);
    lean_dec(v_sz_3533_);
    v_i_boxed_3537_ = lean_unbox_usize(v_i_3534_);
    lean_dec(v_i_3534_);
    v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_3532_, v_sz_boxed_3536_, v_i_boxed_3537_, v_bs_3535_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_IR_FnBody_mapVars(
    mut v_f_3539_: *mut LeanObject,
    mut v_b_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v___x_3541_ = l_Lean_IR_MapVars_mapFnBody(v_f_3539_, v_b_3540_);
    return v___x_3541_;
}
pub unsafe fn l_Lean_IR_FnBody_replaceVar___lam__0(
    mut v_x_3542_: *mut LeanObject,
    mut v_y_3543_: *mut LeanObject,
    mut v_z_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3545_: u8 = 0;
    v___x_3545_ = l_Lean_IR_instBEqVarId_beq(v_x_3542_, v_z_3544_);
    if v___x_3545_ == 0 {
        lean_inc(v_z_3544_);
        return v_z_3544_;
    } else {
        lean_inc(v_y_3543_);
        return v_y_3543_;
    }
}
pub unsafe fn l_Lean_IR_FnBody_replaceVar___lam__0___boxed(
    mut v_x_3546_: *mut LeanObject,
    mut v_y_3547_: *mut LeanObject,
    mut v_z_3548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3549_: *mut LeanObject = core::ptr::null_mut();
    v_res_3549_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_3546_, v_y_3547_, v_z_3548_);
    lean_dec(v_z_3548_);
    lean_dec(v_y_3547_);
    lean_dec(v_x_3546_);
    return v_res_3549_;
}
pub unsafe fn l_Lean_IR_FnBody_replaceVar(
    mut v_x_3550_: *mut LeanObject,
    mut v_y_3551_: *mut LeanObject,
    mut v_b_3552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    v___f_3553_ = lean_alloc_closure(
        l_Lean_IR_FnBody_replaceVar___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3553_, 0, v_x_3550_);
    lean_closure_set(v___f_3553_, 1, v_y_3551_);
    v___x_3554_ = l_Lean_IR_MapVars_mapFnBody(v___f_3553_, v_b_3552_);
    return v___x_3554_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_NormIds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_NormIds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_NormIds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_NormIds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_NormIds(builtin);
}
