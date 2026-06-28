// Lean compiler output
// Module: Lake.Config.Script
// Imports: Init.Dynamic Init.System.IO Lake.Util.Exit Lake.Config.Context
use crate::r#gen::Init::Dynamic::{initialize_Init_Dynamic, runtime_initialize_Init_Dynamic};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Lake::Config::Context::{
    initialize_Lake_Config_Context, runtime_initialize_Lake_Config_Context,
};
use crate::r#gen::Lake::Util::Exit::{
    initialize_Lake_Util_Exit, runtime_initialize_Lake_Util_Exit,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_3, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_instTypeNameScriptFn_unsafe__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value) as *mut LeanObject;
pub static l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [83, 99, 114, 105, 112, 116, 70, 110, 0],
    };
static mut l_Lake_instTypeNameScriptFn_unsafe__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value) as *mut LeanObject;
static l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value)
                as *mut LeanObject,
            13012506173997729135 as *mut LeanObject,
        ],
    };
pub static l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value)
                as *mut LeanObject,
            16942896190233842921 as *mut LeanObject,
        ],
    };
static mut l_Lake_instTypeNameScriptFn_unsafe__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instTypeNameScriptFn_unsafe__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instTypeNameScriptFn: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value) as *mut LeanObject;
pub static l_Lake_instInhabitedScript_default___lam__0___closed__0_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_Lake_instInhabitedScript_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedScript_default___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedScript_default___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedScript_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedScript_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedScript_default___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedScript_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedScript_default___closed__1_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_instInhabitedScript_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__1_value) as *mut LeanObject;
pub static l_Lake_instInhabitedScript_default___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedScript_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedScript_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedScript: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedScript_default___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Lake_instInhabitedScript_default___lam__0(
    mut v_x_49_: *mut LeanObject,
    mut v___y_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    v___x_52_ = l_Lake_instInhabitedScript_default___lam__0___closed__1;
    v___x_53_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_53_, 0, v___x_52_);
    return v___x_53_;
}
pub unsafe fn l_Lake_instInhabitedScript_default___lam__0___boxed(
    mut v_x_54_: *mut LeanObject,
    mut v___y_55_: *mut LeanObject,
    mut v___y_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_57_: *mut LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Lake_instInhabitedScript_default___lam__0(v_x_54_, v___y_55_);
    lean_dec(v___y_55_);
    lean_dec(v_x_54_);
    return v_res_57_;
}
pub unsafe fn l_Lake_Script_run(
    mut v_args_66_: *mut LeanObject,
    mut v_self_67_: *mut LeanObject,
    mut v_a_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    v_fn_70_ = lean_ctor_get(v_self_67_, 1);
    lean_inc_ref(v_fn_70_);
    lean_dec_ref(v_self_67_);
    lean_inc(v_a_68_);
    v___x_71_ = lean_apply_3(v_fn_70_, v_args_66_, v_a_68_, lean_box(0));
    return v___x_71_;
}
pub unsafe fn l_Lake_Script_run___boxed(
    mut v_args_72_: *mut LeanObject,
    mut v_self_73_: *mut LeanObject,
    mut v_a_74_: *mut LeanObject,
    mut v_a_75_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_76_: *mut LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Lake_Script_run(v_args_72_, v_self_73_, v_a_74_);
    lean_dec(v_a_74_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Script(builtin);
}
