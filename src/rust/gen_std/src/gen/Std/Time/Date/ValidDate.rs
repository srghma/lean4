// Lean compiler output
// Module: Std.Time.Date.ValidDate
// Imports: Std.Time.Date.Unit.Month Std.Time.Date.Unit.Month Init.Data.Bool
use crate::r#gen::Init::Core::l_instDecidableEqProd___redArg;
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Std::Time::Date::Unit::Day::l_Std_Time_Day_instDecidableEqOrdinal___boxed;
use crate::r#gen::Std::Time::Date::Unit::Month::{
    initialize_Std_Time_Date_Unit_Month, l_Std_Time_Month_Ordinal_cumulativeDays,
    l_Std_Time_Month_Ordinal_days, l_Std_Time_Month_instDecidableEqOrdinal___boxed,
    runtime_initialize_Std_Time_Date_Unit_Month,
};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::ffi::lean_int_emod;
static mut l_Std_Time_instInhabitedValidDate___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedValidDate___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedValidDate___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instOrdValidDate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdValidDate___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdValidDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdValidDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_ValidDate_ofOrdinal___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ValidDate_ofOrdinal___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ValidDate_ofOrdinal___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_182_ = lean_nat_to_int(v___x_181_);
    return v___x_182_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_183_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_184_ = lean_nat_to_int(v___x_183_);
    return v___x_184_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__1_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__1,
    );
    v___x_186_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_187_ = lean_int_add(v___x_186_, v___x_185_);
    return v___x_187_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_189_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__2_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__2,
    );
    v___x_190_ = lean_int_sub(v___x_189_, v___x_188_);
    return v___x_190_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_191_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_192_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__3_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__3,
    );
    v_range_193_ = lean_int_add(v___x_192_, v___x_191_);
    return v_range_193_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_194_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_195_ = lean_int_sub(v___x_194_, v___x_194_);
    return v___x_195_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v_range_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_196_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__4,
    );
    v___x_197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__5,
    );
    v___x_198_ = lean_int_emod(v___x_197_, v_range_196_);
    return v___x_198_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v_range_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_199_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__4,
    );
    v___x_200_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__6_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__6,
    );
    v___x_201_ = lean_int_add(v___x_200_, v_range_199_);
    return v___x_201_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v_range_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__4_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__4,
    );
    v___x_203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__7_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__7,
    );
    v___x_204_ = lean_int_emod(v___x_203_, v_range_202_);
    return v___x_204_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__8_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__8,
    );
    v___x_207_ = lean_int_add(v___x_206_, v___x_205_);
    return v___x_207_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_209_ = lean_nat_to_int(v___x_208_);
    return v___x_209_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__10_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__10,
    );
    v___x_211_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_212_ = lean_int_add(v___x_211_, v___x_210_);
    return v___x_212_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_213_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__11_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__11,
    );
    v___x_215_ = lean_int_sub(v___x_214_, v___x_213_);
    return v___x_215_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_217_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__12_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__12,
    );
    v_range_218_ = lean_int_add(v___x_217_, v___x_216_);
    return v_range_218_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v_range_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_219_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__13,
    );
    v___x_220_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__5,
    );
    v___x_221_ = lean_int_emod(v___x_220_, v_range_219_);
    return v___x_221_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v_range_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_222_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__13,
    );
    v___x_223_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__14_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__14,
    );
    v___x_224_ = lean_int_add(v___x_223_, v_range_222_);
    return v___x_224_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v_range_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_225_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__13_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__13,
    );
    v___x_226_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__15_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__15,
    );
    v___x_227_ = lean_int_emod(v___x_226_, v_range_225_);
    return v___x_227_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_229_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__16_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__16,
    );
    v___x_230_ = lean_int_add(v___x_229_, v___x_228_);
    return v___x_230_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedValidDate___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__17_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__17,
    );
    v___x_232_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__9_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__9,
    );
    v___x_233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_233_, 0, v___x_232_);
    crate::leanh::lean_ctor_set(v___x_233_, 1, v___x_231_);
    return v___x_233_;
}
pub unsafe fn l_Std_Time_instInhabitedValidDate(mut v_l_234_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__18_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__18,
    );
    return v___x_235_;
}
pub unsafe fn l_Std_Time_instInhabitedValidDate___boxed(
    mut v_l_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_boxed_237_: u8 = 0;
    let mut v_res_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_boxed_237_ = (crate::leanh::lean_unbox(v_l_236_) as u8);
    v_res_238_ = l_Std_Time_instInhabitedValidDate(v_l_boxed_237_);
    return v_res_238_;
}
pub unsafe fn l_Std_Time_instDecidableEqValidDate___redArg(
    mut v_a_239_: *mut crate::leanh::LeanObject,
    mut v_b_240_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: u8 = 0;
    v___x_241_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_Month_instDecidableEqOrdinal___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_242_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_Day_instDecidableEqOrdinal___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_243_ = l_instDecidableEqProd___redArg(v___x_241_, v___x_242_, v_a_239_, v_b_240_);
    return v___x_243_;
}
pub unsafe fn l_Std_Time_instDecidableEqValidDate___redArg___boxed(
    mut v_a_244_: *mut crate::leanh::LeanObject,
    mut v_b_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_246_: u8 = 0;
    let mut v_r_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_244_, v_b_245_);
    v_r_247_ = crate::leanh::lean_box((v_res_246_) as usize);
    return v_r_247_;
}
pub unsafe fn l_Std_Time_instDecidableEqValidDate(
    mut v_leap_248_: u8,
    mut v_a_249_: *mut crate::leanh::LeanObject,
    mut v_b_250_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_251_: u8 = 0;
    v___x_251_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_249_, v_b_250_);
    return v___x_251_;
}
pub unsafe fn l_Std_Time_instDecidableEqValidDate___boxed(
    mut v_leap_252_: *mut crate::leanh::LeanObject,
    mut v_a_253_: *mut crate::leanh::LeanObject,
    mut v_b_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_255_: u8 = 0;
    let mut v_res_256_: u8 = 0;
    let mut v_r_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_255_ = (crate::leanh::lean_unbox(v_leap_252_) as u8);
    v_res_256_ = l_Std_Time_instDecidableEqValidDate(v_leap_boxed_255_, v_a_253_, v_b_254_);
    v_r_257_ = crate::leanh::lean_box((v_res_256_) as usize);
    return v_r_257_;
}
pub unsafe fn l_Std_Time_instOrdValidDate___lam__0(
    mut v_a_258_: *mut crate::leanh::LeanObject,
    mut v_b_259_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: u8 = 0;
    v_fst_260_ = crate::leanh::lean_ctor_get(v_a_258_, 0);
    v_snd_261_ = crate::leanh::lean_ctor_get(v_a_258_, 1);
    v_fst_262_ = crate::leanh::lean_ctor_get(v_b_259_, 0);
    v_snd_263_ = crate::leanh::lean_ctor_get(v_b_259_, 1);
    v___x_264_ = lean_int_dec_lt(v_fst_260_, v_fst_262_);
    if v___x_264_ == 0 {
        let mut v___x_265_: u8 = 0;
        v___x_265_ = lean_int_dec_eq(v_fst_260_, v_fst_262_);
        if v___x_265_ == 0 {
            let mut v___x_266_: u8 = 0;
            v___x_266_ = 2;
            return v___x_266_;
        } else {
            let mut v___x_267_: u8 = 0;
            v___x_267_ = lean_int_dec_lt(v_snd_261_, v_snd_263_);
            if v___x_267_ == 0 {
                let mut v___x_268_: u8 = 0;
                v___x_268_ = lean_int_dec_eq(v_snd_261_, v_snd_263_);
                if v___x_268_ == 0 {
                    let mut v___x_269_: u8 = 0;
                    v___x_269_ = 2;
                    return v___x_269_;
                } else {
                    let mut v___x_270_: u8 = 0;
                    v___x_270_ = 1;
                    return v___x_270_;
                }
            } else {
                let mut v___x_271_: u8 = 0;
                v___x_271_ = 0;
                return v___x_271_;
            }
        }
    } else {
        let mut v___x_272_: u8 = 0;
        v___x_272_ = 0;
        return v___x_272_;
    }
}
pub unsafe fn l_Std_Time_instOrdValidDate___lam__0___boxed(
    mut v_a_273_: *mut crate::leanh::LeanObject,
    mut v_b_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_275_: u8 = 0;
    let mut v_r_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_275_ = l_Std_Time_instOrdValidDate___lam__0(v_a_273_, v_b_274_);
    crate::leanh::lean_dec_ref(v_b_274_);
    crate::leanh::lean_dec_ref(v_a_273_);
    v_r_276_ = crate::leanh::lean_box((v_res_275_) as usize);
    return v_r_276_;
}
pub unsafe fn l_Std_Time_instOrdValidDate(mut v_leap_278_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___f_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_279_ = l_Std_Time_instOrdValidDate___closed__0;
    return v___f_279_;
}
pub unsafe fn l_Std_Time_instOrdValidDate___boxed(
    mut v_leap_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_281_: u8 = 0;
    let mut v_res_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_281_ = (crate::leanh::lean_unbox(v_leap_280_) as u8);
    v_res_282_ = l_Std_Time_instOrdValidDate(v_leap_boxed_281_);
    return v_res_282_;
}
pub unsafe fn l_Std_Time_ValidDate_dayOfYear(
    mut v_leap_283_: u8,
    mut v_ordinal_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_days_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bounded_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_285_ = crate::leanh::lean_ctor_get(v_ordinal_284_, 0);
    v_snd_286_ = crate::leanh::lean_ctor_get(v_ordinal_284_, 1);
    v_days_287_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_283_, v_fst_285_);
    v_bounded_288_ = lean_int_add(v_days_287_, v_snd_286_);
    crate::leanh::lean_dec(v_days_287_);
    return v_bounded_288_;
}
pub unsafe fn l_Std_Time_ValidDate_dayOfYear___boxed(
    mut v_leap_289_: *mut crate::leanh::LeanObject,
    mut v_ordinal_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_291_: u8 = 0;
    let mut v_res_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_291_ = (crate::leanh::lean_unbox(v_leap_289_) as u8);
    v_res_292_ = l_Std_Time_ValidDate_dayOfYear(v_leap_boxed_291_, v_ordinal_290_);
    crate::leanh::lean_dec_ref(v_ordinal_290_);
    return v_res_292_;
}
pub unsafe fn l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(
    mut v_leap_293_: u8,
    mut v_ordinal_294_: *mut crate::leanh::LeanObject,
    mut v_idx_295_: *mut crate::leanh::LeanObject,
    mut v_acc_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_monthDays_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: u8 = 0;
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_u2082_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_days_u2081_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_monthDays_297_ = l_Std_Time_Month_Ordinal_days(v_leap_293_, v_idx_295_);
                v___x_298_ = lean_int_add(v_acc_296_, v_monthDays_297_);
                crate::leanh::lean_dec(v_monthDays_297_);
                v___x_299_ = lean_int_dec_le(v_ordinal_294_, v___x_298_);
                if v___x_299_ == 0 {
                    crate::leanh::lean_dec(v_acc_296_);
                    v___x_300_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
                        _init_l_Std_Time_instInhabitedValidDate___closed__0,
                    );
                    v_idx_u2082_301_ = lean_int_add(v_idx_295_, v___x_300_);
                    crate::leanh::lean_dec(v_idx_295_);
                    v_idx_295_ = v_idx_u2082_301_;
                    v_acc_296_ = v___x_298_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_298_);
                    v___x_303_ = lean_int_neg(v_acc_296_);
                    crate::leanh::lean_dec(v_acc_296_);
                    v_days_u2081_304_ = lean_int_add(v_ordinal_294_, v___x_303_);
                    crate::leanh::lean_dec(v___x_303_);
                    v___x_305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_305_, 0, v_idx_295_);
                    crate::leanh::lean_ctor_set(v___x_305_, 1, v_days_u2081_304_);
                    return v___x_305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(
    mut v_leap_306_: *mut crate::leanh::LeanObject,
    mut v_ordinal_307_: *mut crate::leanh::LeanObject,
    mut v_idx_308_: *mut crate::leanh::LeanObject,
    mut v_acc_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_310_: u8 = 0;
    let mut v_res_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_310_ = (crate::leanh::lean_unbox(v_leap_306_) as u8);
    v_res_311_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(
        v_leap_boxed_310_,
        v_ordinal_307_,
        v_idx_308_,
        v_acc_309_,
    );
    crate::leanh::lean_dec(v_ordinal_307_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(
    mut v_leap_312_: u8,
    mut v_ordinal_313_: *mut crate::leanh::LeanObject,
    mut v_idx_314_: *mut crate::leanh::LeanObject,
    mut v_acc_315_: *mut crate::leanh::LeanObject,
    mut v_h_316_: *mut crate::leanh::LeanObject,
    mut v_p_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(
        v_leap_312_,
        v_ordinal_313_,
        v_idx_314_,
        v_acc_315_,
    );
    return v___x_318_;
}
pub unsafe fn l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___boxed(
    mut v_leap_319_: *mut crate::leanh::LeanObject,
    mut v_ordinal_320_: *mut crate::leanh::LeanObject,
    mut v_idx_321_: *mut crate::leanh::LeanObject,
    mut v_acc_322_: *mut crate::leanh::LeanObject,
    mut v_h_323_: *mut crate::leanh::LeanObject,
    mut v_p_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_325_: u8 = 0;
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_325_ = (crate::leanh::lean_unbox(v_leap_319_) as u8);
    v_res_326_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(
        v_leap_boxed_325_,
        v_ordinal_320_,
        v_idx_321_,
        v_acc_322_,
        v_h_323_,
        v_p_324_,
    );
    crate::leanh::lean_dec(v_ordinal_320_);
    return v_res_326_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_328_ = lean_nat_to_int(v___x_327_);
    return v___x_328_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__0_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__0,
    );
    v___x_330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_331_ = lean_int_add(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_333_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__1_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__1,
    );
    v___x_334_ = lean_int_sub(v___x_333_, v___x_332_);
    return v___x_334_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_336_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__2_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__2,
    );
    v_range_337_ = lean_int_add(v___x_336_, v___x_335_);
    return v_range_337_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__3,
    );
    v___x_339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__5_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__5,
    );
    v___x_340_ = lean_int_emod(v___x_339_, v_range_338_);
    return v___x_340_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v_range_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__3,
    );
    v___x_342_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__4_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__4,
    );
    v___x_343_ = lean_int_add(v___x_342_, v_range_341_);
    return v___x_343_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v_range_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__3_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__3,
    );
    v___x_345_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__5_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__5,
    );
    v___x_346_ = lean_int_emod(v___x_345_, v_range_344_);
    return v___x_346_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedValidDate___closed__0_once),
        _init_l_Std_Time_instInhabitedValidDate___closed__0,
    );
    v___x_348_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__6_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__6,
    );
    v___x_349_ = lean_int_add(v___x_348_, v___x_347_);
    return v___x_349_;
}
pub unsafe fn _init_l_Std_Time_ValidDate_ofOrdinal___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_351_ = lean_nat_to_int(v___x_350_);
    return v___x_351_;
}
pub unsafe fn l_Std_Time_ValidDate_ofOrdinal(
    mut v_leap_352_: u8,
    mut v_ordinal_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__7_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__7,
    );
    v___x_355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_ValidDate_ofOrdinal___closed__8_once),
        _init_l_Std_Time_ValidDate_ofOrdinal___closed__8,
    );
    v___x_356_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(
        v_leap_352_,
        v_ordinal_353_,
        v___x_354_,
        v___x_355_,
    );
    return v___x_356_;
}
pub unsafe fn l_Std_Time_ValidDate_ofOrdinal___boxed(
    mut v_leap_357_: *mut crate::leanh::LeanObject,
    mut v_ordinal_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_359_: u8 = 0;
    let mut v_res_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_359_ = (crate::leanh::lean_unbox(v_leap_357_) as u8);
    v_res_360_ = l_Std_Time_ValidDate_ofOrdinal(v_leap_boxed_359_, v_ordinal_358_);
    crate::leanh::lean_dec(v_ordinal_358_);
    return v_res_360_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_ValidDate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_ValidDate(
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
pub unsafe fn initialize_Std_Time_Date_ValidDate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_ValidDate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_ValidDate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_ValidDate(builtin);
}
