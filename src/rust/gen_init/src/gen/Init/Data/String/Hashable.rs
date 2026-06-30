// Lean compiler output
// Module: Init.Data.String.Hashable
// Imports: Init.Data.Hashable Init.Data.String.Defs
use crate::ffi::{lean_uint64_mix_hash, lean_uint64_of_nat};
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
pub static l_String_instHashableRaw___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_instHashableRaw_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_instHashableRaw___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHashableRaw___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_instHashableRaw: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHashableRaw___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_String_instHashableRaw_hash(mut v_x_44_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_45_: u64 = 0;
    let mut v___x_46_: u64 = 0;
    let mut v___x_47_: u64 = 0;
    v___x_45_ = 0u64;
    v___x_46_ = lean_uint64_of_nat(v_x_44_);
    v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
    return v___x_47_;
}
pub unsafe fn l_String_instHashableRaw_hash___boxed(
    mut v_x_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_49_: u64 = 0;
    let mut v_r_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_49_ = l_String_instHashableRaw_hash(v_x_48_);
    leanh::lean_dec(v_x_48_);
    v_r_50_ = leanh::lean_box_uint64(v_res_49_);
    return v_r_50_;
}
pub unsafe fn l_String_instHashablePos_hash___redArg(
    mut v_x_53_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_54_: u64 = 0;
    let mut v___x_55_: u64 = 0;
    let mut v___x_56_: u64 = 0;
    let mut v___x_57_: u64 = 0;
    v___x_54_ = 0u64;
    v___x_55_ = l_String_instHashableRaw_hash(v_x_53_);
    v___x_56_ = lean_uint64_mix_hash(v___x_54_, v___x_55_);
    v___x_57_ = lean_uint64_mix_hash(v___x_56_, v___x_54_);
    return v___x_57_;
}
pub unsafe fn l_String_instHashablePos_hash___redArg___boxed(
    mut v_x_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_59_: u64 = 0;
    let mut v_r_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_59_ = l_String_instHashablePos_hash___redArg(v_x_58_);
    leanh::lean_dec(v_x_58_);
    v_r_60_ = leanh::lean_box_uint64(v_res_59_);
    return v_r_60_;
}
pub unsafe fn l_String_instHashablePos_hash(
    mut v_s_61_: *mut leanh::LeanObject,
    mut v_x_62_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_63_: u64 = 0;
    v___x_63_ = l_String_instHashablePos_hash___redArg(v_x_62_);
    return v___x_63_;
}
pub unsafe fn l_String_instHashablePos_hash___boxed(
    mut v_s_64_: *mut leanh::LeanObject,
    mut v_x_65_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_66_: u64 = 0;
    let mut v_r_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l_String_instHashablePos_hash(v_s_64_, v_x_65_);
    leanh::lean_dec(v_x_65_);
    leanh::lean_dec_ref(v_s_64_);
    v_r_67_ = leanh::lean_box_uint64(v_res_66_);
    return v_r_67_;
}
pub unsafe fn l_String_instHashablePos(
    mut v_s_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = leanh::lean_alloc_closure(
        l_String_instHashablePos_hash___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_69_, 0, v_s_68_);
    return v___x_69_;
}
pub unsafe fn l_String_instHashablePos__1_hash___redArg(
    mut v_x_70_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_71_: u64 = 0;
    let mut v___x_72_: u64 = 0;
    let mut v___x_73_: u64 = 0;
    let mut v___x_74_: u64 = 0;
    v___x_71_ = 0u64;
    v___x_72_ = l_String_instHashableRaw_hash(v_x_70_);
    v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
    v___x_74_ = lean_uint64_mix_hash(v___x_73_, v___x_71_);
    return v___x_74_;
}
pub unsafe fn l_String_instHashablePos__1_hash___redArg___boxed(
    mut v_x_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_76_: u64 = 0;
    let mut v_r_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_String_instHashablePos__1_hash___redArg(v_x_75_);
    leanh::lean_dec(v_x_75_);
    v_r_77_ = leanh::lean_box_uint64(v_res_76_);
    return v_r_77_;
}
pub unsafe fn l_String_instHashablePos__1_hash(
    mut v_s_78_: *mut leanh::LeanObject,
    mut v_x_79_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_80_: u64 = 0;
    v___x_80_ = l_String_instHashablePos__1_hash___redArg(v_x_79_);
    return v___x_80_;
}
pub unsafe fn l_String_instHashablePos__1_hash___boxed(
    mut v_s_81_: *mut leanh::LeanObject,
    mut v_x_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_83_: u64 = 0;
    let mut v_r_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_String_instHashablePos__1_hash(v_s_81_, v_x_82_);
    leanh::lean_dec(v_x_82_);
    leanh::lean_dec_ref(v_s_81_);
    v_r_84_ = leanh::lean_box_uint64(v_res_83_);
    return v_r_84_;
}
pub unsafe fn l_String_instHashablePos__1(
    mut v_s_85_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_86_ = leanh::lean_alloc_closure(
        l_String_instHashablePos__1_hash___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_86_, 0, v_s_85_);
    return v___x_86_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Hashable(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Hashable(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Hashable(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Hashable(builtin);
}