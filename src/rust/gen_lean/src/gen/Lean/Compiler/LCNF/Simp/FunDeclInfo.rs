// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.FunDeclInfo
// Imports: Lean.Compiler.LCNF.Simp.Basic Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_getBinderName, l_Lean_Compiler_LCNF_getFunDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Basic::{
    initialize_Lean_Compiler_LCNF_Simp_Basic,
    l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_Basic,
};
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_to_int;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        105, 109, 112, 46, 70, 117, 110, 68, 101, 99, 108, 73, 110, 102, 111, 46, 111, 110, 99,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        105, 109, 112, 46, 70, 117, 110, 68, 101, 99, 108, 73, 110, 102, 111, 46, 109, 97, 110,
        121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        105, 109, 112, 46, 70, 117, 110, 68, 101, 99, 108, 73, 110, 102, 111, 46, 109, 117, 115,
        116, 73, 110, 108, 105, 110, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default: u8 = 0;
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo: u8 = 0;
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(
    mut v_x_935_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_935_ {
        0 => {
            let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_936_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_936_;
        }
        1 => {
            let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_937_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_937_;
        }
        _ => {
            let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_938_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_938_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___boxed(
    mut v_x_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_940_: u8 = 0;
    let mut v_res_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_940_ = (crate::leanh::lean_unbox(v_x_939_) as u8);
    v_res_941_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(v_x_boxed_940_);
    return v_res_941_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(
    mut v_x_942_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(v_x_942_);
    return v___x_943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(
    mut v_x_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_945_: u8 = 0;
    let mut v_res_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_945_ = (crate::leanh::lean_unbox(v_x_944_) as u8);
    v_res_946_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(v_x_4__boxed_945_);
    return v_res_946_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(
    mut v_k_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_947_);
    return v_k_947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg___boxed(
    mut v_k_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_949_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(v_k_948_);
    crate::leanh::lean_dec(v_k_948_);
    return v_res_949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(
    mut v_motive_950_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_951_: *mut crate::leanh::LeanObject,
    mut v_t_952_: u8,
    mut v_h_953_: *mut crate::leanh::LeanObject,
    mut v_k_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_954_);
    return v_k_954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___boxed(
    mut v_motive_955_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_956_: *mut crate::leanh::LeanObject,
    mut v_t_957_: *mut crate::leanh::LeanObject,
    mut v_h_958_: *mut crate::leanh::LeanObject,
    mut v_k_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_960_: u8 = 0;
    let mut v_res_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_960_ = (crate::leanh::lean_unbox(v_t_957_) as u8);
    v_res_961_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(
        v_motive_955_,
        v_ctorIdx_956_,
        v_t_boxed_960_,
        v_h_958_,
        v_k_959_,
    );
    crate::leanh::lean_dec(v_k_959_);
    crate::leanh::lean_dec(v_ctorIdx_956_);
    return v_res_961_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(
    mut v_once_962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_once_962_);
    return v_once_962_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg___boxed(
    mut v_once_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(v_once_963_);
    crate::leanh::lean_dec(v_once_963_);
    return v_res_964_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(
    mut v_motive_965_: *mut crate::leanh::LeanObject,
    mut v_t_966_: u8,
    mut v_h_967_: *mut crate::leanh::LeanObject,
    mut v_once_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_once_968_);
    return v_once_968_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___boxed(
    mut v_motive_969_: *mut crate::leanh::LeanObject,
    mut v_t_970_: *mut crate::leanh::LeanObject,
    mut v_h_971_: *mut crate::leanh::LeanObject,
    mut v_once_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_973_: u8 = 0;
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_973_ = (crate::leanh::lean_unbox(v_t_970_) as u8);
    v_res_974_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(
        v_motive_969_,
        v_t_boxed_973_,
        v_h_971_,
        v_once_972_,
    );
    crate::leanh::lean_dec(v_once_972_);
    return v_res_974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(
    mut v_many_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_many_975_);
    return v_many_975_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg___boxed(
    mut v_many_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_977_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(v_many_976_);
    crate::leanh::lean_dec(v_many_976_);
    return v_res_977_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(
    mut v_motive_978_: *mut crate::leanh::LeanObject,
    mut v_t_979_: u8,
    mut v_h_980_: *mut crate::leanh::LeanObject,
    mut v_many_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_many_981_);
    return v_many_981_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___boxed(
    mut v_motive_982_: *mut crate::leanh::LeanObject,
    mut v_t_983_: *mut crate::leanh::LeanObject,
    mut v_h_984_: *mut crate::leanh::LeanObject,
    mut v_many_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_986_: u8 = 0;
    let mut v_res_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_986_ = (crate::leanh::lean_unbox(v_t_983_) as u8);
    v_res_987_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(
        v_motive_982_,
        v_t_boxed_986_,
        v_h_984_,
        v_many_985_,
    );
    crate::leanh::lean_dec(v_many_985_);
    return v_res_987_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(
    mut v_mustInline_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mustInline_988_);
    return v_mustInline_988_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg___boxed(
    mut v_mustInline_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(v_mustInline_989_);
    crate::leanh::lean_dec(v_mustInline_989_);
    return v_res_990_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(
    mut v_motive_991_: *mut crate::leanh::LeanObject,
    mut v_t_992_: u8,
    mut v_h_993_: *mut crate::leanh::LeanObject,
    mut v_mustInline_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mustInline_994_);
    return v_mustInline_994_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___boxed(
    mut v_motive_995_: *mut crate::leanh::LeanObject,
    mut v_t_996_: *mut crate::leanh::LeanObject,
    mut v_h_997_: *mut crate::leanh::LeanObject,
    mut v_mustInline_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_999_: u8 = 0;
    let mut v_res_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_999_ = (crate::leanh::lean_unbox(v_t_996_) as u8);
    v_res_1000_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(
        v_motive_995_,
        v_t_boxed_999_,
        v_h_997_,
        v_mustInline_998_,
    );
    crate::leanh::lean_dec(v_mustInline_998_);
    return v_res_1000_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1011_ = lean_nat_to_int(v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1013_ = lean_nat_to_int(v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(
    mut v_x_1014_: u8,
    mut v_prec_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match v_x_1014_ {
                    0 => {
                        v___x_1037_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_1038_ = lean_nat_dec_le(v___x_1037_, v_prec_1015_);
                        if v___x_1038_ == 0 {
                            v___x_1039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
                            v___y_1017_ = v___x_1039_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
                            v___y_1017_ = v___x_1040_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v___x_1041_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_1042_ = lean_nat_dec_le(v___x_1041_, v_prec_1015_);
                        if v___x_1042_ == 0 {
                            v___x_1043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
                            v___y_1024_ = v___x_1043_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
                            v___y_1024_ = v___x_1044_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1045_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_1046_ = lean_nat_dec_le(v___x_1045_, v_prec_1015_);
                        if v___x_1046_ == 0 {
                            v___x_1047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
                            v___y_1031_ = v___x_1047_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
                            v___y_1031_ = v___x_1048_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1018_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1;
                crate::leanh::lean_inc(v___y_1017_);
                v___x_1019_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1019_, 0, v___y_1017_);
                crate::leanh::lean_ctor_set(v___x_1019_, 1, v___x_1018_);
                v___x_1020_ = 0;
                v___x_1021_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1019_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1021_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1020_,
                );
                v___x_1022_ = l_Repr_addAppParen(v___x_1021_, v_prec_1015_);
                return v___x_1022_;
            }
            2 => {
                v___x_1025_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3;
                crate::leanh::lean_inc(v___y_1024_);
                v___x_1026_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1026_, 0, v___y_1024_);
                crate::leanh::lean_ctor_set(v___x_1026_, 1, v___x_1025_);
                v___x_1027_ = 0;
                v___x_1028_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1028_, 0, v___x_1026_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1028_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1027_,
                );
                v___x_1029_ = l_Repr_addAppParen(v___x_1028_, v_prec_1015_);
                return v___x_1029_;
            }
            3 => {
                v___x_1032_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5;
                crate::leanh::lean_inc(v___y_1031_);
                v___x_1033_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1033_, 0, v___y_1031_);
                crate::leanh::lean_ctor_set(v___x_1033_, 1, v___x_1032_);
                v___x_1034_ = 0;
                v___x_1035_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1033_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1034_,
                );
                v___x_1036_ = l_Repr_addAppParen(v___x_1035_, v_prec_1015_);
                return v___x_1036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed(
    mut v_x_1049_: *mut crate::leanh::LeanObject,
    mut v_prec_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_1051_: u8 = 0;
    let mut v_res_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1051_ = (crate::leanh::lean_unbox(v_x_1049_) as u8);
    v_res_1052_ =
        l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v_x_177__boxed_1051_, v_prec_1050_);
    crate::leanh::lean_dec(v_prec_1050_);
    return v_res_1052_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default() -> u8 {
    let mut v___x_1055_: u8 = 0;
    v___x_1055_ = 0;
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo() -> u8 {
    let mut v___x_1056_: u8 = 0;
    v___x_1056_ = 0;
    return v___x_1056_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = crate::leanh::lean_box(0);
    v___x_1058_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1059_ = lean_mk_array(v___x_1058_, v___x_1057_);
    return v___x_1059_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0,
    );
    v___x_1061_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1062_, 0, v___x_1061_);
    crate::leanh::lean_ctor_set(v___x_1062_, 1, v___x_1060_);
    return v___x_1062_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1,
    );
    return v___x_1063_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
    return v___x_1064_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(
    mut v_x_1065_: *mut crate::leanh::LeanObject,
    mut v_x_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1066_) == 0 {
        crate::leanh::lean_inc(v_x_1065_);
        return v_x_1065_;
    } else {
        let mut v_key_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_1067_ = crate::leanh::lean_ctor_get(v_x_1066_, 0);
        v_value_1068_ = crate::leanh::lean_ctor_get(v_x_1066_, 1);
        v_tail_1069_ = crate::leanh::lean_ctor_get(v_x_1066_, 2);
        v___x_1070_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_1065_, v_tail_1069_);
        crate::leanh::lean_inc(v_value_1068_);
        crate::leanh::lean_inc(v_key_1067_);
        v___x_1071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1071_, 0, v_key_1067_);
        crate::leanh::lean_ctor_set(v___x_1071_, 1, v_value_1068_);
        v___x_1072_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
        crate::leanh::lean_ctor_set(v___x_1072_, 1, v___x_1070_);
        return v___x_1072_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(
    mut v_x_1073_: *mut crate::leanh::LeanObject,
    mut v_x_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_1073_, v_x_1074_);
    crate::leanh::lean_dec(v_x_1074_);
    crate::leanh::lean_dec(v_x_1073_);
    return v_res_1075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(
    mut v_as_1076_: *mut crate::leanh::LeanObject,
    mut v_i_1077_: usize,
    mut v_stop_1078_: usize,
    mut v_b_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: usize = 0;
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1080_ = lean_usize_dec_eq(v_i_1077_, v_stop_1078_);
                if v___x_1080_ == 0 {
                    v___x_1081_ = 1usize;
                    v___x_1082_ = lean_usize_sub(v_i_1077_, v___x_1081_);
                    v___x_1083_ = lean_array_uget_borrowed(v_as_1076_, v___x_1082_);
                    v___x_1084_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_b_1079_, v___x_1083_);
                    crate::leanh::lean_dec(v_b_1079_);
                    v_i_1077_ = v___x_1082_;
                    v_b_1079_ = v___x_1084_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2___boxed(
    mut v_as_1086_: *mut crate::leanh::LeanObject,
    mut v_i_1087_: *mut crate::leanh::LeanObject,
    mut v_stop_1088_: *mut crate::leanh::LeanObject,
    mut v_b_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1090_: usize = 0;
    let mut v_stop_boxed_1091_: usize = 0;
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1090_ = crate::leanh::lean_unbox_usize(v_i_1087_);
    crate::leanh::lean_dec(v_i_1087_);
    v_stop_boxed_1091_ = crate::leanh::lean_unbox_usize(v_stop_1088_);
    crate::leanh::lean_dec(v_stop_1088_);
    v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_as_1086_, v_i_boxed_1090_, v_stop_boxed_1091_, v_b_1089_);
    crate::leanh::lean_dec_ref(v_as_1086_);
    return v_res_1092_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(
    mut v_as_x27_1099_: *mut crate::leanh::LeanObject,
    mut v_b_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1099_) == 0 {
                    v___x_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1106_, 0, v_b_1100_);
                    return v___x_1106_;
                } else {
                    v_head_1107_ = crate::leanh::lean_ctor_get(v_as_x27_1099_, 0);
                    v_tail_1108_ = crate::leanh::lean_ctor_get(v_as_x27_1099_, 1);
                    v_fst_1109_ = crate::leanh::lean_ctor_get(v_head_1107_, 0);
                    v_snd_1110_ = crate::leanh::lean_ctor_get(v_head_1107_, 1);
                    crate::leanh::lean_inc(v_fst_1109_);
                    v___x_1111_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fst_1109_,
                        v___y_1101_,
                        v___y_1102_,
                        v___y_1103_,
                        v___y_1104_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1111_) == 0 {
                        v_a_1112_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                        crate::leanh::lean_inc(v_a_1112_);
                        crate::leanh::lean_dec_ref_known(v___x_1111_, 1);
                        v___x_1113_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1;
                        v___x_1114_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1114_, 0, v_b_1100_);
                        crate::leanh::lean_ctor_set(v___x_1114_, 1, v___x_1113_);
                        v___x_1115_ = 1;
                        v___x_1116_ = l_Lean_Name_toString(v_a_1112_, v___x_1115_);
                        v___x_1117_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1117_, 0, v___x_1116_);
                        v___x_1118_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3;
                        v___x_1119_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1119_, 0, v___x_1117_);
                        crate::leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
                        v___x_1120_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1121_ = (crate::leanh::lean_unbox(v_snd_1110_) as u8);
                        v___x_1122_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(
                            v___x_1121_,
                            v___x_1120_,
                        );
                        v___x_1123_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1123_, 0, v___x_1119_);
                        crate::leanh::lean_ctor_set(v___x_1123_, 1, v___x_1122_);
                        v___x_1124_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1124_, 0, v___x_1114_);
                        crate::leanh::lean_ctor_set(v___x_1124_, 1, v___x_1123_);
                        v_as_x27_1099_ = v_tail_1108_;
                        v_b_1100_ = v___x_1124_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_1100_);
                        v_a_1126_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                        v_isSharedCheck_1133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1111_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v___x_1128_ = v___x_1111_;
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1126_);
                            crate::leanh::lean_dec(v___x_1111_);
                            v___x_1128_ = crate::leanh::lean_box(0);
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1129_ == 0 {
                    v___x_1131_ = v___x_1128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
                    v___x_1131_ = v_reuseFailAlloc_1132_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(
    mut v_as_x27_1134_: *mut crate::leanh::LeanObject,
    mut v_b_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1141_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_1134_, v_b_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
    crate::leanh::lean_dec(v___y_1139_);
    crate::leanh::lean_dec_ref(v___y_1138_);
    crate::leanh::lean_dec(v___y_1137_);
    crate::leanh::lean_dec_ref(v___y_1136_);
    crate::leanh::lean_dec(v_as_x27_1134_);
    return v_res_1141_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(
    mut v_s_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_a_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v_buckets_1148_ = crate::leanh::lean_ctor_get(v_s_1142_, 1);
    v_result_1149_ = crate::leanh::lean_box(0);
    v___x_1150_ = crate::leanh::lean_box(0);
    v___x_1151_ = lean_array_get_size(v_buckets_1148_);
    v___x_1152_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1153_ = lean_nat_dec_lt(v___x_1152_, v___x_1151_);
    if v___x_1153_ == 0 {
        let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1154_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_1150_, v_result_1149_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
        return v___x_1154_;
    } else {
        let mut v___x_1155_: usize = 0;
        let mut v___x_1156_: usize = 0;
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1155_ = lean_usize_of_nat(v___x_1151_);
        v___x_1156_ = 0usize;
        v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_buckets_1148_, v___x_1155_, v___x_1156_, v___x_1150_);
        v___x_1158_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_1157_, v_result_1149_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
        crate::leanh::lean_dec(v___x_1157_);
        return v___x_1158_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(
    mut v_s_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(
        v_s_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_,
    );
    crate::leanh::lean_dec(v_a_1163_);
    crate::leanh::lean_dec_ref(v_a_1162_);
    crate::leanh::lean_dec(v_a_1161_);
    crate::leanh::lean_dec_ref(v_a_1160_);
    crate::leanh::lean_dec_ref(v_s_1159_);
    return v_res_1165_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(
    mut v_as_1166_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1167_: *mut crate::leanh::LeanObject,
    mut v_b_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_1167_, v_b_1168_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
    return v___x_1175_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(
    mut v_as_1176_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1177_: *mut crate::leanh::LeanObject,
    mut v_b_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1185_ =
        l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(
            v_as_1176_,
            v_as_x27_1177_,
            v_b_1178_,
            v_a_1179_,
            v___y_1180_,
            v___y_1181_,
            v___y_1182_,
            v___y_1183_,
        );
    crate::leanh::lean_dec(v___y_1183_);
    crate::leanh::lean_dec_ref(v___y_1182_);
    crate::leanh::lean_dec(v___y_1181_);
    crate::leanh::lean_dec_ref(v___y_1180_);
    crate::leanh::lean_dec(v_as_x27_1177_);
    crate::leanh::lean_dec(v_as_1176_);
    return v_res_1185_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_1186_: *mut crate::leanh::LeanObject,
    mut v_x_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u64 = 0;
    let mut v___x_1196_: u64 = 0;
    let mut v___x_1197_: u64 = 0;
    let mut v_fold_1198_: u64 = 0;
    let mut v___x_1199_: u64 = 0;
    let mut v___x_1200_: u64 = 0;
    let mut v___x_1201_: u64 = 0;
    let mut v___x_1202_: usize = 0;
    let mut v___x_1203_: usize = 0;
    let mut v___x_1204_: usize = 0;
    let mut v___x_1205_: usize = 0;
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1187_) == 0 {
                    return v_x_1186_;
                } else {
                    v_key_1188_ = crate::leanh::lean_ctor_get(v_x_1187_, 0);
                    v_value_1189_ = crate::leanh::lean_ctor_get(v_x_1187_, 1);
                    v_tail_1190_ = crate::leanh::lean_ctor_get(v_x_1187_, 2);
                    v_isSharedCheck_1213_ = (!crate::leanh::lean_is_exclusive(v_x_1187_)) as u8;
                    if v_isSharedCheck_1213_ == 0 {
                        v___x_1192_ = v_x_1187_;
                        v_isShared_1193_ = v_isSharedCheck_1213_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1190_);
                        crate::leanh::lean_inc(v_value_1189_);
                        crate::leanh::lean_inc(v_key_1188_);
                        crate::leanh::lean_dec(v_x_1187_);
                        v___x_1192_ = crate::leanh::lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1213_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1194_ = lean_array_get_size(v_x_1186_);
                v___x_1195_ = l_Lean_instHashableFVarId_hash(v_key_1188_);
                v___x_1196_ = 32u64;
                v___x_1197_ = lean_uint64_shift_right(v___x_1195_, v___x_1196_);
                v_fold_1198_ = lean_uint64_xor(v___x_1195_, v___x_1197_);
                v___x_1199_ = 16u64;
                v___x_1200_ = lean_uint64_shift_right(v_fold_1198_, v___x_1199_);
                v___x_1201_ = lean_uint64_xor(v_fold_1198_, v___x_1200_);
                v___x_1202_ = lean_uint64_to_usize(v___x_1201_);
                v___x_1203_ = lean_usize_of_nat(v___x_1194_);
                v___x_1204_ = 1usize;
                v___x_1205_ = lean_usize_sub(v___x_1203_, v___x_1204_);
                v___x_1206_ = lean_usize_land(v___x_1202_, v___x_1205_);
                v___x_1207_ = lean_array_uget_borrowed(v_x_1186_, v___x_1206_);
                crate::leanh::lean_inc(v___x_1207_);
                if v_isShared_1193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1192_, 2, v___x_1207_);
                    v___x_1209_ = v___x_1192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_key_1188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_value_1189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 2, v___x_1207_);
                    v___x_1209_ = v_reuseFailAlloc_1212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1210_ = lean_array_uset(v_x_1186_, v___x_1206_, v___x_1209_);
                v_x_1186_ = v___x_1210_;
                v_x_1187_ = v_tail_1190_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(
    mut v_i_1214_: *mut crate::leanh::LeanObject,
    mut v_source_1215_: *mut crate::leanh::LeanObject,
    mut v_target_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v_es_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1217_ = lean_array_get_size(v_source_1215_);
                v___x_1218_ = lean_nat_dec_lt(v_i_1214_, v___x_1217_);
                if v___x_1218_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1215_);
                    crate::leanh::lean_dec(v_i_1214_);
                    return v_target_1216_;
                } else {
                    v_es_1219_ = lean_array_fget(v_source_1215_, v_i_1214_);
                    v___x_1220_ = crate::leanh::lean_box(0);
                    v_source_1221_ = lean_array_fset(v_source_1215_, v_i_1214_, v___x_1220_);
                    v_target_1222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1216_, v_es_1219_);
                    v___x_1223_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1224_ = lean_nat_add(v_i_1214_, v___x_1223_);
                    crate::leanh::lean_dec(v_i_1214_);
                    v_i_1214_ = v___x_1224_;
                    v_source_1215_ = v_source_1221_;
                    v_target_1216_ = v_target_1222_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(
    mut v_data_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = lean_array_get_size(v_data_1226_);
    v___x_1228_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1229_ = lean_nat_mul(v___x_1227_, v___x_1228_);
    v___x_1230_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1231_ = crate::leanh::lean_box(0);
    v___x_1232_ = lean_mk_array(v_nbuckets_1229_, v___x_1231_);
    v___x_1233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v___x_1230_, v_data_1226_, v___x_1232_);
    return v___x_1233_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_x_1235_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1236_: u8 = 0;
    let mut v_key_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1235_) == 0 {
                    v___x_1236_ = 0;
                    return v___x_1236_;
                } else {
                    v_key_1237_ = crate::leanh::lean_ctor_get(v_x_1235_, 0);
                    v_tail_1238_ = crate::leanh::lean_ctor_get(v_x_1235_, 2);
                    v___x_1239_ = l_Lean_instBEqFVarId_beq(v_key_1237_, v_a_1234_);
                    if v___x_1239_ == 0 {
                        v_x_1235_ = v_tail_1238_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1239_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_x_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1243_: u8 = 0;
    let mut v_r_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_1241_, v_x_1242_);
    crate::leanh::lean_dec(v_x_1242_);
    crate::leanh::lean_dec(v_a_1241_);
    v_r_1244_ = crate::leanh::lean_box((v_res_1243_) as usize);
    return v_r_1244_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_b_1246_: *mut crate::leanh::LeanObject,
    mut v_x_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1247_) == 0 {
                    crate::leanh::lean_dec(v_b_1246_);
                    crate::leanh::lean_dec(v_a_1245_);
                    return v_x_1247_;
                } else {
                    v_key_1248_ = crate::leanh::lean_ctor_get(v_x_1247_, 0);
                    v_value_1249_ = crate::leanh::lean_ctor_get(v_x_1247_, 1);
                    v_tail_1250_ = crate::leanh::lean_ctor_get(v_x_1247_, 2);
                    v_isSharedCheck_1262_ = (!crate::leanh::lean_is_exclusive(v_x_1247_)) as u8;
                    if v_isSharedCheck_1262_ == 0 {
                        v___x_1252_ = v_x_1247_;
                        v_isShared_1253_ = v_isSharedCheck_1262_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1250_);
                        crate::leanh::lean_inc(v_value_1249_);
                        crate::leanh::lean_inc(v_key_1248_);
                        crate::leanh::lean_dec(v_x_1247_);
                        v___x_1252_ = crate::leanh::lean_box(0);
                        v_isShared_1253_ = v_isSharedCheck_1262_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1254_ = l_Lean_instBEqFVarId_beq(v_key_1248_, v_a_1245_);
                if v___x_1254_ == 0 {
                    v___x_1255_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_1245_, v_b_1246_, v_tail_1250_);
                    if v_isShared_1253_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1252_, 2, v___x_1255_);
                        v___x_1257_ = v___x_1252_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1258_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_key_1248_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_value_1249_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1258_, 2, v___x_1255_);
                        v___x_1257_ = v_reuseFailAlloc_1258_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1249_);
                    crate::leanh::lean_dec(v_key_1248_);
                    if v_isShared_1253_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1252_, 1, v_b_1246_);
                        crate::leanh::lean_ctor_set(v___x_1252_, 0, v_a_1245_);
                        v___x_1260_ = v___x_1252_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1261_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1245_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_b_1246_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_tail_1250_);
                        v___x_1260_ = v_reuseFailAlloc_1261_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1257_;
            }
            3 => {
                return v___x_1260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(
    mut v_m_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_b_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: u64 = 0;
    let mut v___x_1273_: u64 = 0;
    let mut v___x_1274_: u64 = 0;
    let mut v_fold_1275_: u64 = 0;
    let mut v___x_1276_: u64 = 0;
    let mut v___x_1277_: u64 = 0;
    let mut v___x_1278_: u64 = 0;
    let mut v___x_1279_: usize = 0;
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: usize = 0;
    let mut v_bkt_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v_val_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1266_ = crate::leanh::lean_ctor_get(v_m_1263_, 0);
                v_buckets_1267_ = crate::leanh::lean_ctor_get(v_m_1263_, 1);
                v_isSharedCheck_1310_ = (!crate::leanh::lean_is_exclusive(v_m_1263_)) as u8;
                if v_isSharedCheck_1310_ == 0 {
                    v___x_1269_ = v_m_1263_;
                    v_isShared_1270_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1267_);
                    crate::leanh::lean_inc(v_size_1266_);
                    crate::leanh::lean_dec(v_m_1263_);
                    v___x_1269_ = crate::leanh::lean_box(0);
                    v_isShared_1270_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1271_ = lean_array_get_size(v_buckets_1267_);
                v___x_1272_ = l_Lean_instHashableFVarId_hash(v_a_1264_);
                v___x_1273_ = 32u64;
                v___x_1274_ = lean_uint64_shift_right(v___x_1272_, v___x_1273_);
                v_fold_1275_ = lean_uint64_xor(v___x_1272_, v___x_1274_);
                v___x_1276_ = 16u64;
                v___x_1277_ = lean_uint64_shift_right(v_fold_1275_, v___x_1276_);
                v___x_1278_ = lean_uint64_xor(v_fold_1275_, v___x_1277_);
                v___x_1279_ = lean_uint64_to_usize(v___x_1278_);
                v___x_1280_ = lean_usize_of_nat(v___x_1271_);
                v___x_1281_ = 1usize;
                v___x_1282_ = lean_usize_sub(v___x_1280_, v___x_1281_);
                v___x_1283_ = lean_usize_land(v___x_1279_, v___x_1282_);
                v_bkt_1284_ = lean_array_uget_borrowed(v_buckets_1267_, v___x_1283_);
                v___x_1285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_1264_, v_bkt_1284_);
                if v___x_1285_ == 0 {
                    v___x_1286_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1287_ = lean_nat_add(v_size_1266_, v___x_1286_);
                    crate::leanh::lean_dec(v_size_1266_);
                    crate::leanh::lean_inc(v_bkt_1284_);
                    v___x_1288_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1288_, 0, v_a_1264_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 1, v_b_1265_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 2, v_bkt_1284_);
                    v_buckets_x27_1289_ =
                        lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1288_);
                    v___x_1290_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1291_ = lean_nat_mul(v_size_x27_1287_, v___x_1290_);
                    v___x_1292_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1293_ = lean_nat_div(v___x_1291_, v___x_1292_);
                    crate::leanh::lean_dec(v___x_1291_);
                    v___x_1294_ = lean_array_get_size(v_buckets_x27_1289_);
                    v___x_1295_ = lean_nat_dec_le(v___x_1293_, v___x_1294_);
                    crate::leanh::lean_dec(v___x_1293_);
                    if v___x_1295_ == 0 {
                        v_val_1296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_buckets_x27_1289_);
                        if v_isShared_1270_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1269_, 1, v_val_1296_);
                            crate::leanh::lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
                            v___x_1298_ = v___x_1269_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1299_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1299_,
                                0,
                                v_size_x27_1287_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_val_1296_);
                            v___x_1298_ = v_reuseFailAlloc_1299_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1270_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1269_, 1, v_buckets_x27_1289_);
                            crate::leanh::lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
                            v___x_1301_ = v___x_1269_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1302_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1302_,
                                0,
                                v_size_x27_1287_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1302_,
                                1,
                                v_buckets_x27_1289_,
                            );
                            v___x_1301_ = v_reuseFailAlloc_1302_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1284_);
                    v___x_1303_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1304_ =
                        lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1303_);
                    v___x_1305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_1264_, v_b_1265_, v_bkt_1284_);
                    v___x_1306_ = lean_array_uset(v_buckets_x27_1304_, v___x_1283_, v___x_1305_);
                    if v_isShared_1270_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1269_, 1, v___x_1306_);
                        v___x_1308_ = v___x_1269_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_size_1266_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
                        v___x_1308_ = v_reuseFailAlloc_1309_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1298_;
            }
            3 => {
                return v___x_1301_;
            }
            4 => {
                return v___x_1308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_x_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1312_) == 0 {
                    v___x_1313_ = crate::leanh::lean_box(0);
                    return v___x_1313_;
                } else {
                    v_key_1314_ = crate::leanh::lean_ctor_get(v_x_1312_, 0);
                    v_value_1315_ = crate::leanh::lean_ctor_get(v_x_1312_, 1);
                    v_tail_1316_ = crate::leanh::lean_ctor_get(v_x_1312_, 2);
                    v___x_1317_ = l_Lean_instBEqFVarId_beq(v_key_1314_, v_a_1311_);
                    if v___x_1317_ == 0 {
                        v_x_1312_ = v_tail_1316_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1315_);
                        v___x_1319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1319_, 0, v_value_1315_);
                        return v___x_1319_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(
    mut v_a_1320_: *mut crate::leanh::LeanObject,
    mut v_x_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_1320_, v_x_1321_);
    crate::leanh::lean_dec(v_x_1321_);
    crate::leanh::lean_dec(v_a_1320_);
    return v_res_1322_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(
    mut v_m_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u64 = 0;
    let mut v___x_1328_: u64 = 0;
    let mut v___x_1329_: u64 = 0;
    let mut v_fold_1330_: u64 = 0;
    let mut v___x_1331_: u64 = 0;
    let mut v___x_1332_: u64 = 0;
    let mut v___x_1333_: u64 = 0;
    let mut v___x_1334_: usize = 0;
    let mut v___x_1335_: usize = 0;
    let mut v___x_1336_: usize = 0;
    let mut v___x_1337_: usize = 0;
    let mut v___x_1338_: usize = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1325_ = crate::leanh::lean_ctor_get(v_m_1323_, 1);
    v___x_1326_ = lean_array_get_size(v_buckets_1325_);
    v___x_1327_ = l_Lean_instHashableFVarId_hash(v_a_1324_);
    v___x_1328_ = 32u64;
    v___x_1329_ = lean_uint64_shift_right(v___x_1327_, v___x_1328_);
    v_fold_1330_ = lean_uint64_xor(v___x_1327_, v___x_1329_);
    v___x_1331_ = 16u64;
    v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
    v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
    v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
    v___x_1335_ = lean_usize_of_nat(v___x_1326_);
    v___x_1336_ = 1usize;
    v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
    v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
    v___x_1339_ = lean_array_uget_borrowed(v_buckets_1325_, v___x_1338_);
    v___x_1340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_1324_, v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(
    mut v_m_1341_: *mut crate::leanh::LeanObject,
    mut v_a_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_1341_, v_a_1342_);
    crate::leanh::lean_dec(v_a_1342_);
    crate::leanh::lean_dec_ref(v_m_1341_);
    return v_res_1343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(
    mut v_s_1344_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_1344_, v_fvarId_1345_);
    if crate::leanh::lean_obj_tag(v___x_1346_) == 0 {
        let mut v___x_1347_: u8 = 0;
        let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1347_ = 0;
        v___x_1348_ = crate::leanh::lean_box((v___x_1347_) as usize);
        v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_1344_, v_fvarId_1345_, v___x_1348_);
        return v___x_1349_;
    } else {
        let mut v_val_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: u8 = 0;
        v_val_1350_ = crate::leanh::lean_ctor_get(v___x_1346_, 0);
        crate::leanh::lean_inc(v_val_1350_);
        crate::leanh::lean_dec_ref_known(v___x_1346_, 1);
        v___x_1351_ = (crate::leanh::lean_unbox(v_val_1350_) as u8);
        crate::leanh::lean_dec(v_val_1350_);
        if v___x_1351_ == 0 {
            let mut v___x_1352_: u8 = 0;
            let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1352_ = 1;
            v___x_1353_ = crate::leanh::lean_box((v___x_1352_) as usize);
            v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_1344_, v_fvarId_1345_, v___x_1353_);
            return v___x_1354_;
        } else {
            crate::leanh::lean_dec(v_fvarId_1345_);
            return v_s_1344_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(
    mut v_00_u03b2_1355_: *mut crate::leanh::LeanObject,
    mut v_m_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_1356_, v_a_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(
    mut v_00_u03b2_1359_: *mut crate::leanh::LeanObject,
    mut v_m_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_1359_, v_m_1360_, v_a_1361_);
    crate::leanh::lean_dec(v_a_1361_);
    crate::leanh::lean_dec_ref(v_m_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(
    mut v_00_u03b2_1363_: *mut crate::leanh::LeanObject,
    mut v_m_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_b_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_1364_, v_a_1365_, v_b_1366_);
    return v___x_1367_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(
    mut v_00_u03b2_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_x_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_1369_, v_x_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_x_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_1372_, v_a_1373_, v_x_1374_);
    crate::leanh::lean_dec(v_x_1374_);
    crate::leanh::lean_dec(v_a_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(
    mut v_00_u03b2_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1379_: u8 = 0;
    v___x_1379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_1377_, v_x_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(
    mut v_00_u03b2_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1383_: u8 = 0;
    let mut v_r_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_1380_, v_a_1381_, v_x_1382_);
    crate::leanh::lean_dec(v_x_1382_);
    crate::leanh::lean_dec(v_a_1381_);
    v_r_1384_ = crate::leanh::lean_box((v_res_1383_) as usize);
    return v_r_1384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(
    mut v_00_u03b2_1385_: *mut crate::leanh::LeanObject,
    mut v_data_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_data_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(
    mut v_00_u03b2_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_b_1390_: *mut crate::leanh::LeanObject,
    mut v_x_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_1389_, v_b_1390_, v_x_1391_);
    return v___x_1392_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1393_: *mut crate::leanh::LeanObject,
    mut v_i_1394_: *mut crate::leanh::LeanObject,
    mut v_source_1395_: *mut crate::leanh::LeanObject,
    mut v_target_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v_i_1394_, v_source_1395_, v_target_1396_);
    return v___x_1397_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1398_: *mut crate::leanh::LeanObject,
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1399_, v_x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(
    mut v_s_1402_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_1402_, v_fvarId_1403_);
                if crate::leanh::lean_obj_tag(v___x_1408_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                    crate::leanh::lean_inc(v_val_1409_);
                    crate::leanh::lean_dec_ref_known(v___x_1408_, 1);
                    v___x_1410_ = (crate::leanh::lean_unbox(v_val_1409_) as u8);
                    crate::leanh::lean_dec(v_val_1409_);
                    if v___x_1410_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fvarId_1403_);
                        return v_s_1402_;
                    }
                }
            }
            1 => {
                v___x_1405_ = 1;
                v___x_1406_ = crate::leanh::lean_box((v___x_1405_) as usize);
                v___x_1407_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_1402_, v_fvarId_1403_, v___x_1406_);
                return v___x_1407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(
    mut v_s_1411_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = 2;
    v___x_1414_ = crate::leanh::lean_box((v___x_1413_) as usize);
    v___x_1415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_1411_, v_fvarId_1412_, v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(
    mut v_a_1416_: *mut crate::leanh::LeanObject,
    mut v_x_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1417_) == 0 {
                    return v_x_1417_;
                } else {
                    v_key_1418_ = crate::leanh::lean_ctor_get(v_x_1417_, 0);
                    v_value_1419_ = crate::leanh::lean_ctor_get(v_x_1417_, 1);
                    v_tail_1420_ = crate::leanh::lean_ctor_get(v_x_1417_, 2);
                    v_isSharedCheck_1429_ = (!crate::leanh::lean_is_exclusive(v_x_1417_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v___x_1422_ = v_x_1417_;
                        v_isShared_1423_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1420_);
                        crate::leanh::lean_inc(v_value_1419_);
                        crate::leanh::lean_inc(v_key_1418_);
                        crate::leanh::lean_dec(v_x_1417_);
                        v___x_1422_ = crate::leanh::lean_box(0);
                        v_isShared_1423_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1424_ = l_Lean_instBEqFVarId_beq(v_key_1418_, v_a_1416_);
                if v___x_1424_ == 0 {
                    v___x_1425_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_1416_, v_tail_1420_);
                    if v_isShared_1423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1422_, 2, v___x_1425_);
                        v___x_1427_ = v___x_1422_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1428_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_key_1418_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_value_1419_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 2, v___x_1425_);
                        v___x_1427_ = v_reuseFailAlloc_1428_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1422_);
                    crate::leanh::lean_dec(v_value_1419_);
                    crate::leanh::lean_dec(v_key_1418_);
                    return v_tail_1420_;
                }
            }
            2 => {
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_x_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_1430_, v_x_1431_);
    crate::leanh::lean_dec(v_a_1430_);
    return v_res_1432_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(
    mut v_m_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u64 = 0;
    let mut v___x_1439_: u64 = 0;
    let mut v___x_1440_: u64 = 0;
    let mut v_fold_1441_: u64 = 0;
    let mut v___x_1442_: u64 = 0;
    let mut v___x_1443_: u64 = 0;
    let mut v___x_1444_: u64 = 0;
    let mut v___x_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: usize = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v_bkt_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_unused_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1435_ = crate::leanh::lean_ctor_get(v_m_1433_, 0);
                v_buckets_1436_ = crate::leanh::lean_ctor_get(v_m_1433_, 1);
                v___x_1437_ = lean_array_get_size(v_buckets_1436_);
                v___x_1438_ = l_Lean_instHashableFVarId_hash(v_a_1434_);
                v___x_1439_ = 32u64;
                v___x_1440_ = lean_uint64_shift_right(v___x_1438_, v___x_1439_);
                v_fold_1441_ = lean_uint64_xor(v___x_1438_, v___x_1440_);
                v___x_1442_ = 16u64;
                v___x_1443_ = lean_uint64_shift_right(v_fold_1441_, v___x_1442_);
                v___x_1444_ = lean_uint64_xor(v_fold_1441_, v___x_1443_);
                v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
                v___x_1446_ = lean_usize_of_nat(v___x_1437_);
                v___x_1447_ = 1usize;
                v___x_1448_ = lean_usize_sub(v___x_1446_, v___x_1447_);
                v___x_1449_ = lean_usize_land(v___x_1445_, v___x_1448_);
                v_bkt_1450_ = lean_array_uget_borrowed(v_buckets_1436_, v___x_1449_);
                v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_1434_, v_bkt_1450_);
                if v___x_1451_ == 0 {
                    return v_m_1433_;
                } else {
                    crate::leanh::lean_inc(v_bkt_1450_);
                    crate::leanh::lean_inc_ref(v_buckets_1436_);
                    crate::leanh::lean_inc(v_size_1435_);
                    v_isSharedCheck_1464_ = (!crate::leanh::lean_is_exclusive(v_m_1433_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v_unused_1465_ = crate::leanh::lean_ctor_get(v_m_1433_, 1);
                        crate::leanh::lean_dec(v_unused_1465_);
                        v_unused_1466_ = crate::leanh::lean_ctor_get(v_m_1433_, 0);
                        crate::leanh::lean_dec(v_unused_1466_);
                        v___x_1453_ = v_m_1433_;
                        v_isShared_1454_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1433_);
                        v___x_1453_ = crate::leanh::lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1455_ = crate::leanh::lean_box(0);
                v_buckets_x27_1456_ = lean_array_uset(v_buckets_1436_, v___x_1449_, v___x_1455_);
                v___x_1457_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1458_ = lean_nat_sub(v_size_1435_, v___x_1457_);
                crate::leanh::lean_dec(v_size_1435_);
                v___x_1459_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_1434_, v_bkt_1450_);
                v___x_1460_ = lean_array_uset(v_buckets_x27_1456_, v___x_1449_, v___x_1459_);
                if v_isShared_1454_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1453_, 1, v___x_1460_);
                    crate::leanh::lean_ctor_set(v___x_1453_, 0, v___x_1458_);
                    v___x_1462_ = v___x_1453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1460_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(
    mut v_m_1467_: *mut crate::leanh::LeanObject,
    mut v_a_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1469_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_1467_, v_a_1468_);
    crate::leanh::lean_dec(v_a_1468_);
    return v_res_1469_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(
    mut v_s_1470_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1471_: *mut crate::leanh::LeanObject,
    mut v_saved_x3f_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_saved_x3f_1472_) == 0 {
        let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_1470_, v_fvarId_1471_);
        crate::leanh::lean_dec(v_fvarId_1471_);
        return v___x_1473_;
    } else {
        let mut v_val_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1474_ = crate::leanh::lean_ctor_get(v_saved_x3f_1472_, 0);
        crate::leanh::lean_inc(v_val_1474_);
        crate::leanh::lean_dec_ref_known(v_saved_x3f_1472_, 1);
        v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_1470_, v_fvarId_1471_, v_val_1474_);
        return v___x_1475_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(
    mut v_00_u03b2_1476_: *mut crate::leanh::LeanObject,
    mut v_m_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_1477_, v_a_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(
    mut v_00_u03b2_1480_: *mut crate::leanh::LeanObject,
    mut v_m_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_1480_, v_m_1481_, v_a_1482_);
    crate::leanh::lean_dec(v_a_1482_);
    return v_res_1483_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(
    mut v_00_u03b2_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_x_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_1485_, v_x_1486_);
    return v___x_1487_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(
    mut v_00_u03b2_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_x_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(v_00_u03b2_1488_, v_a_1489_, v_x_1490_);
    crate::leanh::lean_dec(v_a_1489_);
    return v_res_1491_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(
    mut v_arg_1492_: *mut crate::leanh::LeanObject,
    mut v_a_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v_val_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_arg_1492_) == 1 {
                    v_fvarId_1496_ = crate::leanh::lean_ctor_get(v_arg_1492_, 0);
                    crate::leanh::lean_inc(v_fvarId_1496_);
                    crate::leanh::lean_dec_ref_known(v_arg_1492_, 1);
                    v___x_1497_ = 0;
                    v___x_1498_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                        v___x_1497_,
                        v_fvarId_1496_,
                        v_a_1494_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1498_) == 0 {
                        v_a_1499_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1516_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1516_ == 0 {
                            v___x_1501_ = v___x_1498_;
                            v_isShared_1502_ = v_isSharedCheck_1516_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1499_);
                            crate::leanh::lean_dec(v___x_1498_);
                            v___x_1501_ = crate::leanh::lean_box(0);
                            v_isShared_1502_ = v_isSharedCheck_1516_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1524_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1524_ == 0 {
                            v___x_1519_ = v___x_1498_;
                            v_isShared_1520_ = v_isSharedCheck_1524_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1517_);
                            crate::leanh::lean_dec(v___x_1498_);
                            v___x_1519_ = crate::leanh::lean_box(0);
                            v_isShared_1520_ = v_isSharedCheck_1524_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_arg_1492_);
                    v___x_1525_ = crate::leanh::lean_box(0);
                    v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                    return v___x_1526_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1499_) == 1 {
                    v_val_1503_ = crate::leanh::lean_ctor_get(v_a_1499_, 0);
                    crate::leanh::lean_inc(v_val_1503_);
                    crate::leanh::lean_dec_ref_known(v_a_1499_, 1);
                    v___x_1504_ = lean_st_ref_take(v_a_1493_);
                    v_fvarId_1505_ = crate::leanh::lean_ctor_get(v_val_1503_, 0);
                    crate::leanh::lean_inc(v_fvarId_1505_);
                    crate::leanh::lean_dec(v_val_1503_);
                    v___x_1506_ =
                        l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_1504_, v_fvarId_1505_);
                    v___x_1507_ = lean_st_ref_set(v_a_1493_, v___x_1506_);
                    v___x_1508_ = crate::leanh::lean_box(0);
                    if v_isShared_1502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1508_);
                        v___x_1510_ = v___x_1501_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
                        v___x_1510_ = v_reuseFailAlloc_1511_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1499_);
                    v___x_1512_ = crate::leanh::lean_box(0);
                    if v_isShared_1502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1512_);
                        v___x_1514_ = v___x_1501_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
                        v___x_1514_ = v_reuseFailAlloc_1515_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1510_;
            }
            3 => {
                return v___x_1514_;
            }
            4 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(
    mut v_arg_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_1527_, v_a_1528_, v_a_1529_);
    crate::leanh::lean_dec(v_a_1529_);
    crate::leanh::lean_dec(v_a_1528_);
    return v_res_1531_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(
    mut v_arg_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_1532_, v_a_1533_, v_a_1535_);
    return v___x_1539_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(
    mut v_arg_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
    crate::leanh::lean_dec(v_a_1545_);
    crate::leanh::lean_dec_ref(v_a_1544_);
    crate::leanh::lean_dec(v_a_1543_);
    crate::leanh::lean_dec_ref(v_a_1542_);
    crate::leanh::lean_dec(v_a_1541_);
    return v_res_1547_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(
    mut v_as_1548_: *mut crate::leanh::LeanObject,
    mut v_i_1549_: usize,
    mut v_stop_1550_: usize,
    mut v_b_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: usize = 0;
    let mut v___x_1560_: usize = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1555_ = lean_usize_dec_eq(v_i_1549_, v_stop_1550_);
                if v___x_1555_ == 0 {
                    v___x_1556_ = lean_array_uget_borrowed(v_as_1548_, v_i_1549_);
                    crate::leanh::lean_inc(v___x_1556_);
                    v___x_1557_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_1556_, v___y_1552_, v___y_1553_);
                    if crate::leanh::lean_obj_tag(v___x_1557_) == 0 {
                        v_a_1558_ = crate::leanh::lean_ctor_get(v___x_1557_, 0);
                        crate::leanh::lean_inc(v_a_1558_);
                        crate::leanh::lean_dec_ref_known(v___x_1557_, 1);
                        v___x_1559_ = 1usize;
                        v___x_1560_ = lean_usize_add(v_i_1549_, v___x_1559_);
                        v_i_1549_ = v___x_1560_;
                        v_b_1551_ = v_a_1558_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1557_;
                    }
                } else {
                    v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1562_, 0, v_b_1551_);
                    return v___x_1562_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(
    mut v_as_1563_: *mut crate::leanh::LeanObject,
    mut v_i_1564_: *mut crate::leanh::LeanObject,
    mut v_stop_1565_: *mut crate::leanh::LeanObject,
    mut v_b_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1570_: usize = 0;
    let mut v_stop_boxed_1571_: usize = 0;
    let mut v_res_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1570_ = crate::leanh::lean_unbox_usize(v_i_1564_);
    crate::leanh::lean_dec(v_i_1564_);
    v_stop_boxed_1571_ = crate::leanh::lean_unbox_usize(v_stop_1565_);
    crate::leanh::lean_dec(v_stop_1565_);
    v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_1563_, v_i_boxed_1570_, v_stop_boxed_1571_, v_b_1566_, v___y_1567_, v___y_1568_);
    crate::leanh::lean_dec(v___y_1568_);
    crate::leanh::lean_dec(v___y_1567_);
    crate::leanh::lean_dec_ref(v_as_1563_);
    return v_res_1572_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(
    mut v_e_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: usize = 0;
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v_val_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: usize = 0;
    let mut v___x_1628_: usize = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v_a_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1573_) {
                0 => {
                    v_isSharedCheck_1587_ = (!crate::leanh::lean_is_exclusive(v_e_1573_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v_unused_1588_ = crate::leanh::lean_ctor_get(v_e_1573_, 0);
                        crate::leanh::lean_dec(v_unused_1588_);
                        v___x_1581_ = v_e_1573_;
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_e_1573_);
                        v___x_1581_ = crate::leanh::lean_box(0);
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_args_1589_ = crate::leanh::lean_ctor_get(v_e_1573_, 2);
                    crate::leanh::lean_inc_ref(v_args_1589_);
                    crate::leanh::lean_dec_ref_known(v_e_1573_, 3);
                    v___x_1590_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1591_ = lean_array_get_size(v_args_1589_);
                    v___x_1592_ = crate::leanh::lean_box(0);
                    v___x_1593_ = lean_nat_dec_lt(v___x_1590_, v___x_1591_);
                    if v___x_1593_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_1589_);
                        v___x_1594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1594_, 0, v___x_1592_);
                        return v___x_1594_;
                    } else {
                        v___x_1595_ = lean_nat_dec_le(v___x_1591_, v___x_1591_);
                        if v___x_1595_ == 0 {
                            if v___x_1593_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_1589_);
                                v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1596_, 0, v___x_1592_);
                                return v___x_1596_;
                            } else {
                                v___x_1597_ = 0usize;
                                v___x_1598_ = lean_usize_of_nat(v___x_1591_);
                                v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1589_, v___x_1597_, v___x_1598_, v___x_1592_, v_a_1574_, v_a_1576_);
                                crate::leanh::lean_dec_ref(v_args_1589_);
                                return v___x_1599_;
                            }
                        } else {
                            v___x_1600_ = 0usize;
                            v___x_1601_ = lean_usize_of_nat(v___x_1591_);
                            v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1589_, v___x_1600_, v___x_1601_, v___x_1592_, v_a_1574_, v_a_1576_);
                            crate::leanh::lean_dec_ref(v_args_1589_);
                            return v___x_1602_;
                        }
                    }
                }
                4 => {
                    v_fvarId_1603_ = crate::leanh::lean_ctor_get(v_e_1573_, 0);
                    crate::leanh::lean_inc(v_fvarId_1603_);
                    v_args_1604_ = crate::leanh::lean_ctor_get(v_e_1573_, 1);
                    crate::leanh::lean_inc_ref(v_args_1604_);
                    crate::leanh::lean_dec_ref_known(v_e_1573_, 2);
                    v___x_1605_ = 0;
                    v___x_1606_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                        v___x_1605_,
                        v_fvarId_1603_,
                        v_a_1576_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1606_) == 0 {
                        v_a_1607_ = crate::leanh::lean_ctor_get(v___x_1606_, 0);
                        v_isSharedCheck_1637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1606_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1609_ = v___x_1606_;
                            v_isShared_1610_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1607_);
                            crate::leanh::lean_dec(v___x_1606_);
                            v___x_1609_ = crate::leanh::lean_box(0);
                            v_isShared_1610_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_1604_);
                        v_a_1638_ = crate::leanh::lean_ctor_get(v___x_1606_, 0);
                        v_isSharedCheck_1645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1606_)) as u8;
                        if v_isSharedCheck_1645_ == 0 {
                            v___x_1640_ = v___x_1606_;
                            v_isShared_1641_ = v_isSharedCheck_1645_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1638_);
                            crate::leanh::lean_dec(v___x_1606_);
                            v___x_1640_ = crate::leanh::lean_box(0);
                            v_isShared_1641_ = v_isSharedCheck_1645_;
                            state = 7;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_e_1573_);
                    v___x_1646_ = crate::leanh::lean_box(0);
                    v___x_1647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1647_, 0, v___x_1646_);
                    return v___x_1647_;
                }
            },
            1 => {
                v___x_1583_ = crate::leanh::lean_box(0);
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1583_);
                    v___x_1585_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
                    v___x_1585_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1585_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1607_) == 1 {
                    v_val_1611_ = crate::leanh::lean_ctor_get(v_a_1607_, 0);
                    crate::leanh::lean_inc(v_val_1611_);
                    crate::leanh::lean_dec_ref_known(v_a_1607_, 1);
                    v___x_1612_ = lean_st_ref_take(v_a_1574_);
                    v_fvarId_1613_ = crate::leanh::lean_ctor_get(v_val_1611_, 0);
                    crate::leanh::lean_inc(v_fvarId_1613_);
                    crate::leanh::lean_dec(v_val_1611_);
                    v___x_1614_ =
                        l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_1612_, v_fvarId_1613_);
                    v___x_1615_ = lean_st_ref_set(v_a_1574_, v___x_1614_);
                    v___x_1616_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1617_ = lean_array_get_size(v_args_1604_);
                    v___x_1618_ = crate::leanh::lean_box(0);
                    v___x_1619_ = lean_nat_dec_lt(v___x_1616_, v___x_1617_);
                    if v___x_1619_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_1604_);
                        if v_isShared_1610_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1618_);
                            v___x_1621_ = v___x_1609_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1622_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1618_);
                            v___x_1621_ = v_reuseFailAlloc_1622_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1623_ = lean_nat_dec_le(v___x_1617_, v___x_1617_);
                        if v___x_1623_ == 0 {
                            if v___x_1619_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_1604_);
                                if v_isShared_1610_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1618_);
                                    v___x_1625_ = v___x_1609_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1626_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1626_,
                                        0,
                                        v___x_1618_,
                                    );
                                    v___x_1625_ = v_reuseFailAlloc_1626_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1609_);
                                v___x_1627_ = 0usize;
                                v___x_1628_ = lean_usize_of_nat(v___x_1617_);
                                v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1604_, v___x_1627_, v___x_1628_, v___x_1618_, v_a_1574_, v_a_1576_);
                                crate::leanh::lean_dec_ref(v_args_1604_);
                                return v___x_1629_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1609_);
                            v___x_1630_ = 0usize;
                            v___x_1631_ = lean_usize_of_nat(v___x_1617_);
                            v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1604_, v___x_1630_, v___x_1631_, v___x_1618_, v_a_1574_, v_a_1576_);
                            crate::leanh::lean_dec_ref(v_args_1604_);
                            return v___x_1632_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1607_);
                    crate::leanh::lean_dec_ref(v_args_1604_);
                    v___x_1633_ = crate::leanh::lean_box(0);
                    if v_isShared_1610_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1633_);
                        v___x_1635_ = v___x_1609_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
                        v___x_1635_ = v_reuseFailAlloc_1636_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1621_;
            }
            5 => {
                return v___x_1625_;
            }
            6 => {
                return v___x_1635_;
            }
            7 => {
                if v_isShared_1641_ == 0 {
                    v___x_1643_ = v___x_1640_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
                    v___x_1643_ = v_reuseFailAlloc_1644_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(
    mut v_e_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
    crate::leanh::lean_dec(v_a_1653_);
    crate::leanh::lean_dec_ref(v_a_1652_);
    crate::leanh::lean_dec(v_a_1651_);
    crate::leanh::lean_dec_ref(v_a_1650_);
    crate::leanh::lean_dec(v_a_1649_);
    return v_res_1655_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(
    mut v_as_1656_: *mut crate::leanh::LeanObject,
    mut v_i_1657_: usize,
    mut v_stop_1658_: usize,
    mut v_b_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_1656_, v_i_1657_, v_stop_1658_, v_b_1659_, v___y_1660_, v___y_1662_);
    return v___x_1666_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(
    mut v_as_1667_: *mut crate::leanh::LeanObject,
    mut v_i_1668_: *mut crate::leanh::LeanObject,
    mut v_stop_1669_: *mut crate::leanh::LeanObject,
    mut v_b_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1677_: usize = 0;
    let mut v_stop_boxed_1678_: usize = 0;
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1677_ = crate::leanh::lean_unbox_usize(v_i_1668_);
    crate::leanh::lean_dec(v_i_1668_);
    v_stop_boxed_1678_ = crate::leanh::lean_unbox_usize(v_stop_1669_);
    crate::leanh::lean_dec(v_stop_1669_);
    v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_1667_, v_i_boxed_1677_, v_stop_boxed_1678_, v_b_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
    crate::leanh::lean_dec(v___y_1675_);
    crate::leanh::lean_dec_ref(v___y_1674_);
    crate::leanh::lean_dec(v___y_1673_);
    crate::leanh::lean_dec_ref(v___y_1672_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v_as_1667_);
    return v_res_1679_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(
    mut v_mustInline_1680_: u8,
    mut v_code_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: usize = 0;
    let mut v___x_1737_: usize = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: usize = 0;
    let mut v___x_1740_: usize = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_a_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_cases_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v_alts_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: usize = 0;
    let mut v___x_1768_: usize = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut v_unused_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1681_) {
                0 => {
                    v_decl_1688_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                    crate::leanh::lean_inc_ref(v_decl_1688_);
                    v_k_1689_ = crate::leanh::lean_ctor_get(v_code_1681_, 1);
                    crate::leanh::lean_inc_ref(v_k_1689_);
                    crate::leanh::lean_dec_ref_known(v_code_1681_, 2);
                    v_value_1690_ = crate::leanh::lean_ctor_get(v_decl_1688_, 3);
                    crate::leanh::lean_inc(v_value_1690_);
                    crate::leanh::lean_dec_ref(v_decl_1688_);
                    v___x_1691_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_1690_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
                    if crate::leanh::lean_obj_tag(v___x_1691_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1691_, 1);
                        v_code_1681_ = v_k_1689_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1689_);
                        return v___x_1691_;
                    }
                }
                1 => {
                    v_decl_1693_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                    crate::leanh::lean_inc_ref(v_decl_1693_);
                    v_k_1694_ = crate::leanh::lean_ctor_get(v_code_1681_, 1);
                    crate::leanh::lean_inc_ref(v_k_1694_);
                    crate::leanh::lean_dec_ref_known(v_code_1681_, 2);
                    if v_mustInline_1680_ == 0 {
                        v___y_1696_ = v_a_1682_;
                        v___y_1697_ = v_a_1683_;
                        v___y_1698_ = v_a_1684_;
                        v___y_1699_ = v_a_1685_;
                        v___y_1700_ = v_a_1686_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1704_ = lean_st_ref_take(v_a_1682_);
                        v_fvarId_1705_ = crate::leanh::lean_ctor_get(v_decl_1693_, 0);
                        crate::leanh::lean_inc(v_fvarId_1705_);
                        v___x_1706_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(
                            v___x_1704_,
                            v_fvarId_1705_,
                        );
                        v___x_1707_ = lean_st_ref_set(v_a_1682_, v___x_1706_);
                        v___y_1696_ = v_a_1682_;
                        v___y_1697_ = v_a_1683_;
                        v___y_1698_ = v_a_1684_;
                        v___y_1699_ = v_a_1685_;
                        v___y_1700_ = v_a_1686_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_decl_1708_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                    crate::leanh::lean_inc_ref(v_decl_1708_);
                    v_k_1709_ = crate::leanh::lean_ctor_get(v_code_1681_, 1);
                    crate::leanh::lean_inc_ref(v_k_1709_);
                    crate::leanh::lean_dec_ref_known(v_code_1681_, 2);
                    v_value_1710_ = crate::leanh::lean_ctor_get(v_decl_1708_, 4);
                    crate::leanh::lean_inc_ref(v_value_1710_);
                    crate::leanh::lean_dec_ref(v_decl_1708_);
                    v___x_1711_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1680_, v_value_1710_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
                    if crate::leanh::lean_obj_tag(v___x_1711_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1711_, 1);
                        v_code_1681_ = v_k_1709_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1709_);
                        return v___x_1711_;
                    }
                }
                3 => {
                    v_fvarId_1713_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                    crate::leanh::lean_inc(v_fvarId_1713_);
                    v_args_1714_ = crate::leanh::lean_ctor_get(v_code_1681_, 1);
                    crate::leanh::lean_inc_ref(v_args_1714_);
                    crate::leanh::lean_dec_ref_known(v_code_1681_, 2);
                    v___x_1715_ = 0;
                    v___x_1716_ = l_Lean_Compiler_LCNF_getFunDecl(
                        v___x_1715_,
                        v_fvarId_1713_,
                        v_a_1683_,
                        v_a_1684_,
                        v_a_1685_,
                        v_a_1686_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1716_) == 0 {
                        v_a_1717_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                        v_isSharedCheck_1742_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1716_)) as u8;
                        if v_isSharedCheck_1742_ == 0 {
                            v___x_1719_ = v___x_1716_;
                            v_isShared_1720_ = v_isSharedCheck_1742_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1717_);
                            crate::leanh::lean_dec(v___x_1716_);
                            v___x_1719_ = crate::leanh::lean_box(0);
                            v_isShared_1720_ = v_isSharedCheck_1742_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_1714_);
                        v_a_1743_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                        v_isSharedCheck_1750_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1716_)) as u8;
                        if v_isSharedCheck_1750_ == 0 {
                            v___x_1745_ = v___x_1716_;
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1743_);
                            crate::leanh::lean_dec(v___x_1716_);
                            v___x_1745_ = crate::leanh::lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 5;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_1751_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                    v_isSharedCheck_1773_ = (!crate::leanh::lean_is_exclusive(v_code_1681_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1753_ = v_code_1681_;
                        v_isShared_1754_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_1751_);
                        crate::leanh::lean_dec(v_code_1681_);
                        v___x_1753_ = crate::leanh::lean_box(0);
                        v_isShared_1754_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_isSharedCheck_1781_ = (!crate::leanh::lean_is_exclusive(v_code_1681_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v_unused_1782_ = crate::leanh::lean_ctor_get(v_code_1681_, 0);
                        crate::leanh::lean_dec(v_unused_1782_);
                        v___x_1775_ = v_code_1681_;
                        v_isShared_1776_ = v_isSharedCheck_1781_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1681_);
                        v___x_1775_ = crate::leanh::lean_box(0);
                        v_isShared_1776_ = v_isSharedCheck_1781_;
                        state = 10;
                        continue;
                    }
                }
            },
            1 => {
                v_value_1701_ = crate::leanh::lean_ctor_get(v_decl_1693_, 4);
                crate::leanh::lean_inc_ref(v_value_1701_);
                crate::leanh::lean_dec_ref(v_decl_1693_);
                v___x_1702_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1680_, v_value_1701_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
                if crate::leanh::lean_obj_tag(v___x_1702_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1702_, 1);
                    v_code_1681_ = v_k_1694_;
                    v_a_1682_ = v___y_1696_;
                    v_a_1683_ = v___y_1697_;
                    v_a_1684_ = v___y_1698_;
                    v_a_1685_ = v___y_1699_;
                    v_a_1686_ = v___y_1700_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_k_1694_);
                    return v___x_1702_;
                }
            }
            2 => {
                v___x_1721_ = lean_st_ref_take(v_a_1682_);
                v_fvarId_1722_ = crate::leanh::lean_ctor_get(v_a_1717_, 0);
                crate::leanh::lean_inc(v_fvarId_1722_);
                crate::leanh::lean_dec(v_a_1717_);
                v___x_1723_ =
                    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_1721_, v_fvarId_1722_);
                v___x_1724_ = lean_st_ref_set(v_a_1682_, v___x_1723_);
                v___x_1725_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1726_ = lean_array_get_size(v_args_1714_);
                v___x_1727_ = crate::leanh::lean_box(0);
                v___x_1728_ = lean_nat_dec_lt(v___x_1725_, v___x_1726_);
                if v___x_1728_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_1714_);
                    if v_isShared_1720_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1727_);
                        v___x_1730_ = v___x_1719_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1727_);
                        v___x_1730_ = v_reuseFailAlloc_1731_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1732_ = lean_nat_dec_le(v___x_1726_, v___x_1726_);
                    if v___x_1732_ == 0 {
                        if v___x_1728_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_1714_);
                            if v_isShared_1720_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1727_);
                                v___x_1734_ = v___x_1719_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1735_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1727_);
                                v___x_1734_ = v_reuseFailAlloc_1735_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1719_);
                            v___x_1736_ = 0usize;
                            v___x_1737_ = lean_usize_of_nat(v___x_1726_);
                            v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1714_, v___x_1736_, v___x_1737_, v___x_1727_, v_a_1682_, v_a_1684_);
                            crate::leanh::lean_dec_ref(v_args_1714_);
                            return v___x_1738_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1719_);
                        v___x_1739_ = 0usize;
                        v___x_1740_ = lean_usize_of_nat(v___x_1726_);
                        v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1714_, v___x_1739_, v___x_1740_, v___x_1727_, v_a_1682_, v_a_1684_);
                        crate::leanh::lean_dec_ref(v_args_1714_);
                        return v___x_1741_;
                    }
                }
            }
            3 => {
                return v___x_1730_;
            }
            4 => {
                return v___x_1734_;
            }
            5 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1748_;
            }
            7 => {
                v_alts_1755_ = crate::leanh::lean_ctor_get(v_cases_1751_, 3);
                crate::leanh::lean_inc_ref(v_alts_1755_);
                crate::leanh::lean_dec_ref(v_cases_1751_);
                v___x_1756_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1757_ = lean_array_get_size(v_alts_1755_);
                v___x_1758_ = crate::leanh::lean_box(0);
                v___x_1759_ = lean_nat_dec_lt(v___x_1756_, v___x_1757_);
                if v___x_1759_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_1755_);
                    if v_isShared_1754_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1753_, 0);
                        crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1758_);
                        v___x_1761_ = v___x_1753_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1758_);
                        v___x_1761_ = v_reuseFailAlloc_1762_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_1763_ = lean_nat_dec_le(v___x_1757_, v___x_1757_);
                    if v___x_1763_ == 0 {
                        if v___x_1759_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_1755_);
                            if v_isShared_1754_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1753_, 0);
                                crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1758_);
                                v___x_1765_ = v___x_1753_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1766_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1758_);
                                v___x_1765_ = v_reuseFailAlloc_1766_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1753_);
                            v___x_1767_ = 0usize;
                            v___x_1768_ = lean_usize_of_nat(v___x_1757_);
                            v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_1680_, v_alts_1755_, v___x_1767_, v___x_1768_, v___x_1758_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
                            crate::leanh::lean_dec_ref(v_alts_1755_);
                            return v___x_1769_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1753_);
                        v___x_1770_ = 0usize;
                        v___x_1771_ = lean_usize_of_nat(v___x_1757_);
                        v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_1680_, v_alts_1755_, v___x_1770_, v___x_1771_, v___x_1758_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
                        crate::leanh::lean_dec_ref(v_alts_1755_);
                        return v___x_1772_;
                    }
                }
            }
            8 => {
                return v___x_1761_;
            }
            9 => {
                return v___x_1765_;
            }
            10 => {
                v___x_1777_ = crate::leanh::lean_box(0);
                if v_isShared_1776_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1775_, 0);
                    crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1777_);
                    v___x_1779_ = v___x_1775_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
                    v___x_1779_ = v_reuseFailAlloc_1780_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(
    mut v_mustInline_1783_: u8,
    mut v_as_1784_: *mut crate::leanh::LeanObject,
    mut v_i_1785_: usize,
    mut v_stop_1786_: usize,
    mut v_b_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: usize = 0;
    let mut v___x_1799_: usize = 0;
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1801_ = lean_usize_dec_eq(v_i_1785_, v_stop_1786_);
                if v___x_1801_ == 0 {
                    v___x_1802_ = lean_array_uget_borrowed(v_as_1784_, v_i_1785_);
                    match crate::leanh::lean_obj_tag(v___x_1802_) {
                        0 => {
                            v_code_1803_ = crate::leanh::lean_ctor_get(v___x_1802_, 2);
                            crate::leanh::lean_inc_ref(v_code_1803_);
                            v___y_1795_ = v_code_1803_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1804_ = crate::leanh::lean_ctor_get(v___x_1802_, 1);
                            crate::leanh::lean_inc_ref(v_code_1804_);
                            v___y_1795_ = v_code_1804_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1805_ = crate::leanh::lean_ctor_get(v___x_1802_, 0);
                            crate::leanh::lean_inc_ref(v_code_1805_);
                            v___y_1795_ = v_code_1805_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1806_, 0, v_b_1787_);
                    return v___x_1806_;
                }
            }
            1 => {
                v___x_1796_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1783_, v___y_1795_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
                if crate::leanh::lean_obj_tag(v___x_1796_) == 0 {
                    v_a_1797_ = crate::leanh::lean_ctor_get(v___x_1796_, 0);
                    crate::leanh::lean_inc(v_a_1797_);
                    crate::leanh::lean_dec_ref_known(v___x_1796_, 1);
                    v___x_1798_ = 1usize;
                    v___x_1799_ = lean_usize_add(v_i_1785_, v___x_1798_);
                    v_i_1785_ = v___x_1799_;
                    v_b_1787_ = v_a_1797_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1796_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(
    mut v_mustInline_1807_: *mut crate::leanh::LeanObject,
    mut v_as_1808_: *mut crate::leanh::LeanObject,
    mut v_i_1809_: *mut crate::leanh::LeanObject,
    mut v_stop_1810_: *mut crate::leanh::LeanObject,
    mut v_b_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_1818_: u8 = 0;
    let mut v_i_boxed_1819_: usize = 0;
    let mut v_stop_boxed_1820_: usize = 0;
    let mut v_res_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_1818_ = (crate::leanh::lean_unbox(v_mustInline_1807_) as u8);
    v_i_boxed_1819_ = crate::leanh::lean_unbox_usize(v_i_1809_);
    crate::leanh::lean_dec(v_i_1809_);
    v_stop_boxed_1820_ = crate::leanh::lean_unbox_usize(v_stop_1810_);
    crate::leanh::lean_dec(v_stop_1810_);
    v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_1818_, v_as_1808_, v_i_boxed_1819_, v_stop_boxed_1820_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    crate::leanh::lean_dec(v___y_1814_);
    crate::leanh::lean_dec_ref(v___y_1813_);
    crate::leanh::lean_dec(v___y_1812_);
    crate::leanh::lean_dec_ref(v_as_1808_);
    return v_res_1821_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(
    mut v_mustInline_1822_: *mut crate::leanh::LeanObject,
    mut v_code_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_1830_: u8 = 0;
    let mut v_res_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_1830_ = (crate::leanh::lean_unbox(v_mustInline_1822_) as u8);
    v_res_1831_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_1830_, v_code_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
    crate::leanh::lean_dec(v_a_1828_);
    crate::leanh::lean_dec_ref(v_a_1827_);
    crate::leanh::lean_dec(v_a_1826_);
    crate::leanh::lean_dec_ref(v_a_1825_);
    crate::leanh::lean_dec(v_a_1824_);
    return v_res_1831_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(
    mut v_s_1832_: *mut crate::leanh::LeanObject,
    mut v_code_1833_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1834_: u8,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut v_unused_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = lean_st_mk_ref(v_s_1832_);
                v___x_1841_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1834_, v_code_1833_, v___x_1840_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
                if crate::leanh::lean_obj_tag(v___x_1841_) == 0 {
                    v_isSharedCheck_1849_ = (!crate::leanh::lean_is_exclusive(v___x_1841_)) as u8;
                    if v_isSharedCheck_1849_ == 0 {
                        v_unused_1850_ = crate::leanh::lean_ctor_get(v___x_1841_, 0);
                        crate::leanh::lean_dec(v_unused_1850_);
                        v___x_1843_ = v___x_1841_;
                        v_isShared_1844_ = v_isSharedCheck_1849_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1841_);
                        v___x_1843_ = crate::leanh::lean_box(0);
                        v_isShared_1844_ = v_isSharedCheck_1849_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1840_);
                    v_a_1851_ = crate::leanh::lean_ctor_get(v___x_1841_, 0);
                    v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___x_1841_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1853_ = v___x_1841_;
                        v_isShared_1854_ = v_isSharedCheck_1858_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1851_);
                        crate::leanh::lean_dec(v___x_1841_);
                        v___x_1853_ = crate::leanh::lean_box(0);
                        v_isShared_1854_ = v_isSharedCheck_1858_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1845_ = lean_st_ref_get(v___x_1840_);
                crate::leanh::lean_dec(v___x_1840_);
                if v_isShared_1844_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1845_);
                    v___x_1847_ = v___x_1843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1847_;
            }
            3 => {
                if v_isShared_1854_ == 0 {
                    v___x_1856_ = v___x_1853_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(
    mut v_s_1859_: *mut crate::leanh::LeanObject,
    mut v_code_1860_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_1867_: u8 = 0;
    let mut v_res_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_1867_ = (crate::leanh::lean_unbox(v_mustInline_1861_) as u8);
    v_res_1868_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(
        v_s_1859_,
        v_code_1860_,
        v_mustInline_boxed_1867_,
        v_a_1862_,
        v_a_1863_,
        v_a_1864_,
        v_a_1865_,
    );
    crate::leanh::lean_dec(v_a_1865_);
    crate::leanh::lean_dec_ref(v_a_1864_);
    crate::leanh::lean_dec(v_a_1863_);
    crate::leanh::lean_dec_ref(v_a_1862_);
    return v_res_1868_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default();
    l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo();
    l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default,
    );
    l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
}
