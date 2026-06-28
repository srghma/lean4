// Lean compiler output
// Module: Init.Data.ToString.Extra
// Imports: Init.Data.String.Defs Init.Data.Int.Repr
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_toList;
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr___boxed, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringUInt8___lam__0___boxed;
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_array_to_list;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_closure_set,
    lean_ctor_get, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_List_toString___redArg___lam__0___closed__0_value: LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_List_toString___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_toString___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_List_toString___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [91, 93, 0],
};
static mut l_List_toString___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_toString___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_toString___redArg___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l_List_toString___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_toString___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_toString___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_List_toString___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_toString___redArg___closed__2_value) as *mut LeanObject;
pub static l_instToStringArray___redArg___lam__0___closed__0_value: LeanStringObject<2> =
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
        m_data: [35, 0],
    };
static mut l_instToStringArray___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringArray___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instToStringByteArray___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringUInt8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringByteArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringByteArray___closed__0_value) as *mut LeanObject;
pub static l_instToStringByteArray___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringByteArray___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_instToStringByteArray___closed__0_value) as *mut LeanObject],
};
static mut l_instToStringByteArray___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringByteArray___closed__1_value) as *mut LeanObject;
pub static mut l_instToStringByteArray: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringByteArray___closed__1_value) as *mut LeanObject;
pub static l_instToStringInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringInt: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt___closed__0_value) as *mut LeanObject;
pub unsafe fn l_List_toString___redArg___lam__0(
    mut v_inst_65_: *mut LeanObject,
    mut v_l_66_: *mut LeanObject,
    mut v_r_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    v___x_68_ = l_List_toString___redArg___lam__0___closed__0;
    v___x_69_ = lean_string_append(v_l_66_, v___x_68_);
    v___x_70_ = lean_apply_1(v_inst_65_, v_r_67_);
    v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
    lean_dec_ref(v___x_70_);
    return v___x_71_;
}
pub unsafe fn l_List_toString___redArg(
    mut v_inst_75_: *mut LeanObject,
    mut v_x_76_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_76_) == 0 {
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_75_);
        v___x_77_ = l_List_toString___redArg___closed__0;
        return v___x_77_;
    } else {
        let mut v_tail_78_: *mut LeanObject = core::ptr::null_mut();
        v_tail_78_ = lean_ctor_get(v_x_76_, 1);
        if lean_obj_tag(v_tail_78_) == 0 {
            let mut v_head_79_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
            v_head_79_ = lean_ctor_get(v_x_76_, 0);
            lean_inc(v_head_79_);
            lean_dec_ref_known(v_x_76_, 2);
            v___x_80_ = l_List_toString___redArg___closed__1;
            v___x_81_ = lean_apply_1(v_inst_75_, v_head_79_);
            v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
            lean_dec_ref(v___x_81_);
            v___x_83_ = l_List_toString___redArg___closed__2;
            v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
            return v___x_84_;
        } else {
            let mut v_head_85_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_86_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_91_: u32 = 0;
            let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_78_);
            v_head_85_ = lean_ctor_get(v_x_76_, 0);
            lean_inc(v_head_85_);
            lean_dec_ref_known(v_x_76_, 2);
            lean_inc_ref(v_inst_75_);
            v___f_86_ = lean_alloc_closure(
                l_List_toString___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_86_, 0, v_inst_75_);
            v___x_87_ = l_List_toString___redArg___closed__1;
            v___x_88_ = lean_apply_1(v_inst_75_, v_head_85_);
            v___x_89_ = lean_string_append(v___x_87_, v___x_88_);
            lean_dec_ref(v___x_88_);
            v___x_90_ = l_List_foldl___redArg(v___f_86_, v___x_89_, v_tail_78_);
            v___x_91_ = 93;
            v___x_92_ = lean_string_push(v___x_90_, v___x_91_);
            return v___x_92_;
        }
    }
}
pub unsafe fn l_List_toString(
    mut v_00_u03b1_93_: *mut LeanObject,
    mut v_inst_94_: *mut LeanObject,
    mut v_x_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    v___x_96_ = l_List_toString___redArg(v_inst_94_, v_x_95_);
    return v___x_96_;
}
pub unsafe fn l_instToStringList___redArg(mut v_inst_97_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    v___x_98_ = lean_alloc_closure(l_List_toString as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_98_, 0, lean_box(0));
    lean_closure_set(v___x_98_, 1, v_inst_97_);
    return v___x_98_;
}
pub unsafe fn l_instToStringList(
    mut v_00_u03b1_99_: *mut LeanObject,
    mut v_inst_100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v___x_101_ = lean_alloc_closure(l_List_toString as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_101_, 0, lean_box(0));
    lean_closure_set(v___x_101_, 1, v_inst_100_);
    return v___x_101_;
}
pub unsafe fn l_instToStringArray___redArg___lam__0(
    mut v_inst_103_: *mut LeanObject,
    mut v_xs_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v___x_105_ = l_instToStringArray___redArg___lam__0___closed__0;
    v___x_106_ = lean_array_to_list(v_xs_104_);
    v___x_107_ = l_List_toString___redArg(v_inst_103_, v___x_106_);
    v___x_108_ = lean_string_append(v___x_105_, v___x_107_);
    lean_dec_ref(v___x_107_);
    return v___x_108_;
}
pub unsafe fn l_instToStringArray___redArg(mut v_inst_109_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_110_: *mut LeanObject = core::ptr::null_mut();
    v___f_110_ = lean_alloc_closure(
        l_instToStringArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_110_, 0, v_inst_109_);
    return v___f_110_;
}
pub unsafe fn l_instToStringArray(
    mut v_00_u03b1_111_: *mut LeanObject,
    mut v_inst_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_113_: *mut LeanObject = core::ptr::null_mut();
    v___f_113_ = lean_alloc_closure(
        l_instToStringArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_113_, 0, v_inst_112_);
    return v___f_113_;
}
pub unsafe fn l_instToStringByteArray___lam__0(
    mut v___f_114_: *mut LeanObject,
    mut v_bs_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    v___x_116_ = l_ByteArray_toList(v_bs_115_);
    v___x_117_ = l_List_toString___redArg(v___f_114_, v___x_116_);
    return v___x_117_;
}
pub unsafe fn l_instToStringByteArray___lam__0___boxed(
    mut v___f_118_: *mut LeanObject,
    mut v_bs_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l_instToStringByteArray___lam__0(v___f_118_, v_bs_119_);
    lean_dec_ref(v_bs_119_);
    return v_res_120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ToString_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ToString_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ToString_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_ToString_Extra(builtin);
}
