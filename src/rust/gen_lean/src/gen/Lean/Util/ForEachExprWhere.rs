// Lean compiler output
// Module: Lean.Util.ForEachExprWhere
// Imports: Lean.Expr Lean.Util.MonadCache
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_eqv___boxed, l_Lean_Expr_hash___boxed,
    runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Util::MonadCache::{
    initialize_Lean_Util_MonadCache, runtime_initialize_Lean_Util_MonadCache,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_usize_mod;
use crate::ffi::{lean_usize_sub, lean_usize_to_nat};
use crate::ffi::lean_usize_dec_eq;
use crate::ffi::lean_ptr_addr;
static mut l_Lean_ForEachExprWhere_cacheSize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_cacheSize___closed__0: usize = 0;
pub static mut l_Lean_ForEachExprWhere_cacheSize: usize = 0;
pub static l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_ForEachExprWhere_initCache___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_initCache___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ForEachExprWhere_initCache___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_initCache___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ForEachExprWhere_initCache___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_initCache___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ForEachExprWhere_initCache___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_initCache___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ForEachExprWhere_initCache___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_initCache___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ForEachExprWhere_initCache: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ForEachExprWhere_checked___redArg___closed__0_value:
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
    m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ForEachExprWhere_checked___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ForEachExprWhere_checked___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ForEachExprWhere_checked___redArg___closed__1_value:
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
    m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ForEachExprWhere_checked___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ForEachExprWhere_checked___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ForEachExprWhere_visit___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ForEachExprWhere_visit___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_ForEachExprWhere_cacheSize___closed__0() -> usize {
    let mut v___x_548_: usize = 0;
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    v___x_548_ = 1usize;
    v___x_549_ = 8192usize;
    v___x_550_ = lean_usize_sub(v___x_549_, v___x_548_);
    return v___x_550_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_cacheSize() -> usize {
    let mut v___x_551_: usize = 0;
    v___x_551_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0_once),
        _init_l_Lean_ForEachExprWhere_cacheSize___closed__0,
    );
    return v___x_551_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_555_: usize = 0;
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0_once),
        _init_l_Lean_ForEachExprWhere_cacheSize___closed__0,
    );
    v___x_556_ = lean_usize_to_nat(v___x_555_);
    return v___x_556_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr;
    v___x_558_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__0_once),
        _init_l_Lean_ForEachExprWhere_initCache___closed__0,
    );
    v___x_559_ = lean_mk_array(v___x_558_, v___x_557_);
    return v___x_559_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = crate::leanh::lean_box(0);
    v___x_561_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_562_ = lean_mk_array(v___x_561_, v___x_560_);
    return v___x_562_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__2),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__2_once),
        _init_l_Lean_ForEachExprWhere_initCache___closed__2,
    );
    v___x_564_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_565_, 0, v___x_564_);
    crate::leanh::lean_ctor_set(v___x_565_, 1, v___x_563_);
    return v___x_565_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__3),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__3_once),
        _init_l_Lean_ForEachExprWhere_initCache___closed__3,
    );
    v___x_567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__1_once),
        _init_l_Lean_ForEachExprWhere_initCache___closed__1,
    );
    v___x_568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    crate::leanh::lean_ctor_set(v___x_568_, 1, v___x_566_);
    return v___x_568_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_initCache() -> *mut crate::leanh::LeanObject {
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__4),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_initCache___closed__4_once),
        _init_l_Lean_ForEachExprWhere_initCache___closed__4,
    );
    return v___x_569_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__0(
    mut v___x_570_: usize,
    mut v_e_571_: *mut crate::leanh::LeanObject,
    mut v_s_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visited_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_573_ = crate::leanh::lean_ctor_get(v_s_572_, 0);
                v_checked_574_ = crate::leanh::lean_ctor_get(v_s_572_, 1);
                v_isSharedCheck_584_ = (!crate::leanh::lean_is_exclusive(v_s_572_)) as u8;
                if v_isSharedCheck_584_ == 0 {
                    v___x_576_ = v_s_572_;
                    v_isShared_577_ = v_isSharedCheck_584_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_checked_574_);
                    crate::leanh::lean_inc(v_visited_573_);
                    crate::leanh::lean_dec(v_s_572_);
                    v___x_576_ = crate::leanh::lean_box(0);
                    v_isShared_577_ = v_isSharedCheck_584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_578_ = crate::leanh::lean_box(0);
                v___x_579_ = lean_array_uset(v_visited_573_, v___x_570_, v_e_571_);
                if v_isShared_577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_579_);
                    v___x_581_ = v___x_576_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_583_, 1, v_checked_574_);
                    v___x_581_ = v_reuseFailAlloc_583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_582_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_578_);
                crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
                return v___x_582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(
    mut v___x_585_: *mut crate::leanh::LeanObject,
    mut v_e_586_: *mut crate::leanh::LeanObject,
    mut v_s_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328__boxed_588_: usize = 0;
    let mut v_res_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328__boxed_588_ = crate::leanh::lean_unbox_usize(v___x_585_);
    crate::leanh::lean_dec(v___x_585_);
    v_res_589_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(
        v___x_328__boxed_588_,
        v_e_586_,
        v_s_587_,
    );
    return v_res_589_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__1(
    mut v_toApplicative_590_: *mut crate::leanh::LeanObject,
    mut v___x_591_: u8,
    mut v_a_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_593_ = crate::leanh::lean_ctor_get(v_toApplicative_590_, 1);
    crate::leanh::lean_inc(v_toPure_593_);
    crate::leanh::lean_dec_ref(v_toApplicative_590_);
    v___x_594_ = crate::leanh::lean_box((v___x_591_) as usize);
    v___x_595_ = crate::leanh::lean_apply_2(v_toPure_593_, crate::leanh::lean_box(0), v___x_594_);
    return v___x_595_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(
    mut v_toApplicative_596_: *mut crate::leanh::LeanObject,
    mut v___x_597_: *mut crate::leanh::LeanObject,
    mut v_a_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351__boxed_599_: u8 = 0;
    let mut v_res_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351__boxed_599_ = (crate::leanh::lean_unbox(v___x_597_) as u8);
    v_res_600_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(
        v_toApplicative_596_,
        v___x_351__boxed_599_,
        v_a_598_,
    );
    return v_res_600_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__2(
    mut v_e_601_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
    mut v_inst_604_: *mut crate::leanh::LeanObject,
    mut v_toBind_605_: *mut crate::leanh::LeanObject,
    mut v_a_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visited_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: usize = 0;
    let mut v___x_609_: usize = 0;
    let mut v___x_610_: usize = 0;
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: usize = 0;
    let mut v___x_613_: u8 = 0;
    v_visited_607_ = crate::leanh::lean_ctor_get(v_a_606_, 0);
    v___x_608_ = lean_ptr_addr(v_e_601_);
    v___x_609_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_cacheSize___closed__0_once),
        _init_l_Lean_ForEachExprWhere_cacheSize___closed__0,
    );
    v___x_610_ = lean_usize_mod(v___x_608_, v___x_609_);
    v___x_611_ = lean_array_uget_borrowed(v_visited_607_, v___x_610_);
    v___x_612_ = lean_ptr_addr(v___x_611_);
    v___x_613_ = lean_usize_dec_eq(v___x_612_, v___x_608_);
    if v___x_613_ == 0 {
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_614_ = crate::leanh::lean_box_usize(v___x_610_);
        v___f_615_ = crate::leanh::lean_alloc_closure(
            l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_615_, 0, v___x_614_);
        crate::leanh::lean_closure_set(v___f_615_, 1, v_e_601_);
        v___x_616_ = crate::leanh::lean_box((v___x_613_) as usize);
        v___f_617_ = crate::leanh::lean_alloc_closure(
            l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_617_, 0, v_toApplicative_602_);
        crate::leanh::lean_closure_set(v___f_617_, 1, v___x_616_);
        crate::leanh::lean_inc(v_a_603_);
        v___x_618_ = crate::leanh::lean_alloc_closure(
            l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___x_618_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_618_, 1, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_618_, 2, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_618_, 3, v_a_603_);
        crate::leanh::lean_closure_set(v___x_618_, 4, v___f_615_);
        v___x_619_ = crate::leanh::lean_apply_2(v_inst_604_, crate::leanh::lean_box(0), v___x_618_);
        v___x_620_ = crate::leanh::lean_apply_4(
            v_toBind_605_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_619_,
            v___f_617_,
        );
        return v___x_620_;
    } else {
        let mut v_toPure_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_605_);
        crate::leanh::lean_dec(v_inst_604_);
        crate::leanh::lean_dec_ref(v_e_601_);
        v_toPure_621_ = crate::leanh::lean_ctor_get(v_toApplicative_602_, 1);
        crate::leanh::lean_inc(v_toPure_621_);
        crate::leanh::lean_dec_ref(v_toApplicative_602_);
        v___x_622_ = crate::leanh::lean_box((v___x_613_) as usize);
        v___x_623_ =
            crate::leanh::lean_apply_2(v_toPure_621_, crate::leanh::lean_box(0), v___x_622_);
        return v___x_623_;
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed(
    mut v_e_624_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_inst_627_: *mut crate::leanh::LeanObject,
    mut v_toBind_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l_Lean_ForEachExprWhere_visited___redArg___lam__2(
        v_e_624_,
        v_toApplicative_625_,
        v_a_626_,
        v_inst_627_,
        v_toBind_628_,
        v_a_629_,
    );
    crate::leanh::lean_dec_ref(v_a_629_);
    crate::leanh::lean_dec(v_a_626_);
    return v_res_630_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg(
    mut v_inst_631_: *mut crate::leanh::LeanObject,
    mut v_inst_632_: *mut crate::leanh::LeanObject,
    mut v_e_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_635_ = crate::leanh::lean_ctor_get(v_inst_632_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_635_);
    v_toBind_636_ = crate::leanh::lean_ctor_get(v_inst_632_, 1);
    crate::leanh::lean_inc_n(v_toBind_636_, 2);
    crate::leanh::lean_dec_ref(v_inst_632_);
    crate::leanh::lean_inc(v_inst_631_);
    crate::leanh::lean_inc_n(v_a_634_, 2);
    v___f_637_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_637_, 0, v_e_633_);
    crate::leanh::lean_closure_set(v___f_637_, 1, v_toApplicative_635_);
    crate::leanh::lean_closure_set(v___f_637_, 2, v_a_634_);
    crate::leanh::lean_closure_set(v___f_637_, 3, v_inst_631_);
    crate::leanh::lean_closure_set(v___f_637_, 4, v_toBind_636_);
    v___x_638_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_638_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_638_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_638_, 2, v_a_634_);
    v___x_639_ = crate::leanh::lean_apply_2(v_inst_631_, crate::leanh::lean_box(0), v___x_638_);
    v___x_640_ = crate::leanh::lean_apply_4(
        v_toBind_636_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_639_,
        v___f_637_,
    );
    return v___x_640_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___redArg___boxed(
    mut v_inst_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_e_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_645_ =
        l_Lean_ForEachExprWhere_visited___redArg(v_inst_641_, v_inst_642_, v_e_643_, v_a_644_);
    crate::leanh::lean_dec(v_a_644_);
    return v_res_645_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited(
    mut v_00_u03c9_646_: *mut crate::leanh::LeanObject,
    mut v_m_647_: *mut crate::leanh::LeanObject,
    mut v_inst_648_: *mut crate::leanh::LeanObject,
    mut v_inst_649_: *mut crate::leanh::LeanObject,
    mut v_inst_650_: *mut crate::leanh::LeanObject,
    mut v_e_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_653_ =
        l_Lean_ForEachExprWhere_visited___redArg(v_inst_649_, v_inst_650_, v_e_651_, v_a_652_);
    return v___x_653_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___boxed(
    mut v_00_u03c9_654_: *mut crate::leanh::LeanObject,
    mut v_m_655_: *mut crate::leanh::LeanObject,
    mut v_inst_656_: *mut crate::leanh::LeanObject,
    mut v_inst_657_: *mut crate::leanh::LeanObject,
    mut v_inst_658_: *mut crate::leanh::LeanObject,
    mut v_e_659_: *mut crate::leanh::LeanObject,
    mut v_a_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_661_ = l_Lean_ForEachExprWhere_visited(
        v_00_u03c9_654_,
        v_m_655_,
        v_inst_656_,
        v_inst_657_,
        v_inst_658_,
        v_e_659_,
        v_a_660_,
    );
    crate::leanh::lean_dec(v_a_660_);
    return v_res_661_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___lam__0(
    mut v___x_662_: *mut crate::leanh::LeanObject,
    mut v___x_663_: *mut crate::leanh::LeanObject,
    mut v_e_664_: *mut crate::leanh::LeanObject,
    mut v_s_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visited_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_666_ = crate::leanh::lean_ctor_get(v_s_665_, 0);
                v_checked_667_ = crate::leanh::lean_ctor_get(v_s_665_, 1);
                v_isSharedCheck_677_ = (!crate::leanh::lean_is_exclusive(v_s_665_)) as u8;
                if v_isSharedCheck_677_ == 0 {
                    v___x_669_ = v_s_665_;
                    v_isShared_670_ = v_isSharedCheck_677_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_checked_667_);
                    crate::leanh::lean_inc(v_visited_666_);
                    crate::leanh::lean_dec(v_s_665_);
                    v___x_669_ = crate::leanh::lean_box(0);
                    v_isShared_670_ = v_isSharedCheck_677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_671_ = crate::leanh::lean_box(0);
                v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_662_,
                    v___x_663_,
                    v_checked_667_,
                    v_e_664_,
                    v___x_671_,
                );
                if v_isShared_670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_669_, 1, v___x_672_);
                    v___x_674_ = v___x_669_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v_visited_666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_672_);
                    v___x_674_ = v_reuseFailAlloc_676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_671_);
                crate::leanh::lean_ctor_set(v___x_675_, 1, v___x_674_);
                return v___x_675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___lam__1(
    mut v_toApplicative_678_: *mut crate::leanh::LeanObject,
    mut v___x_679_: u8,
    mut v_a_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_681_ = crate::leanh::lean_ctor_get(v_toApplicative_678_, 1);
    crate::leanh::lean_inc(v_toPure_681_);
    crate::leanh::lean_dec_ref(v_toApplicative_678_);
    v___x_682_ = crate::leanh::lean_box((v___x_679_) as usize);
    v___x_683_ = crate::leanh::lean_apply_2(v_toPure_681_, crate::leanh::lean_box(0), v___x_682_);
    return v___x_683_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(
    mut v_toApplicative_684_: *mut crate::leanh::LeanObject,
    mut v___x_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_371__boxed_687_: u8 = 0;
    let mut v_res_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_371__boxed_687_ = (crate::leanh::lean_unbox(v___x_685_) as u8);
    v_res_688_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(
        v_toApplicative_684_,
        v___x_371__boxed_687_,
        v_a_686_,
    );
    return v_res_688_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___lam__2(
    mut v___x_689_: *mut crate::leanh::LeanObject,
    mut v___x_690_: *mut crate::leanh::LeanObject,
    mut v_e_691_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
    mut v___f_694_: *mut crate::leanh::LeanObject,
    mut v_inst_695_: *mut crate::leanh::LeanObject,
    mut v_toBind_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checked_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    v_checked_698_ = crate::leanh::lean_ctor_get(v_a_697_, 1);
    v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_689_,
        v___x_690_,
        v_checked_698_,
        v_e_691_,
    );
    if v___x_699_ == 0 {
        let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_700_ = crate::leanh::lean_box((v___x_699_) as usize);
        v___f_701_ = crate::leanh::lean_alloc_closure(
            l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_701_, 0, v_toApplicative_692_);
        crate::leanh::lean_closure_set(v___f_701_, 1, v___x_700_);
        crate::leanh::lean_inc(v_a_693_);
        v___x_702_ = crate::leanh::lean_alloc_closure(
            l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___x_702_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_702_, 1, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_702_, 2, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_702_, 3, v_a_693_);
        crate::leanh::lean_closure_set(v___x_702_, 4, v___f_694_);
        v___x_703_ = crate::leanh::lean_apply_2(v_inst_695_, crate::leanh::lean_box(0), v___x_702_);
        v___x_704_ = crate::leanh::lean_apply_4(
            v_toBind_696_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_703_,
            v___f_701_,
        );
        return v___x_704_;
    } else {
        let mut v_toPure_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_696_);
        crate::leanh::lean_dec(v_inst_695_);
        crate::leanh::lean_dec_ref(v___f_694_);
        v_toPure_705_ = crate::leanh::lean_ctor_get(v_toApplicative_692_, 1);
        crate::leanh::lean_inc(v_toPure_705_);
        crate::leanh::lean_dec_ref(v_toApplicative_692_);
        v___x_706_ = crate::leanh::lean_box((v___x_699_) as usize);
        v___x_707_ =
            crate::leanh::lean_apply_2(v_toPure_705_, crate::leanh::lean_box(0), v___x_706_);
        return v___x_707_;
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(
    mut v___x_708_: *mut crate::leanh::LeanObject,
    mut v___x_709_: *mut crate::leanh::LeanObject,
    mut v_e_710_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_711_: *mut crate::leanh::LeanObject,
    mut v_a_712_: *mut crate::leanh::LeanObject,
    mut v___f_713_: *mut crate::leanh::LeanObject,
    mut v_inst_714_: *mut crate::leanh::LeanObject,
    mut v_toBind_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(
        v___x_708_,
        v___x_709_,
        v_e_710_,
        v_toApplicative_711_,
        v_a_712_,
        v___f_713_,
        v_inst_714_,
        v_toBind_715_,
        v_a_716_,
    );
    crate::leanh::lean_dec_ref(v_a_716_);
    crate::leanh::lean_dec(v_a_712_);
    return v_res_717_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg(
    mut v_inst_720_: *mut crate::leanh::LeanObject,
    mut v_inst_721_: *mut crate::leanh::LeanObject,
    mut v_e_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_724_ = crate::leanh::lean_ctor_get(v_inst_721_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_724_);
    v_toBind_725_ = crate::leanh::lean_ctor_get(v_inst_721_, 1);
    crate::leanh::lean_inc_n(v_toBind_725_, 2);
    crate::leanh::lean_dec_ref(v_inst_721_);
    v___x_726_ = l_Lean_ForEachExprWhere_checked___redArg___closed__0;
    v___x_727_ = l_Lean_ForEachExprWhere_checked___redArg___closed__1;
    crate::leanh::lean_inc_ref(v_e_722_);
    v___f_728_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_checked___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_728_, 0, v___x_726_);
    crate::leanh::lean_closure_set(v___f_728_, 1, v___x_727_);
    crate::leanh::lean_closure_set(v___f_728_, 2, v_e_722_);
    crate::leanh::lean_inc(v_inst_720_);
    crate::leanh::lean_inc_n(v_a_723_, 2);
    v___f_729_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_729_, 0, v___x_726_);
    crate::leanh::lean_closure_set(v___f_729_, 1, v___x_727_);
    crate::leanh::lean_closure_set(v___f_729_, 2, v_e_722_);
    crate::leanh::lean_closure_set(v___f_729_, 3, v_toApplicative_724_);
    crate::leanh::lean_closure_set(v___f_729_, 4, v_a_723_);
    crate::leanh::lean_closure_set(v___f_729_, 5, v___f_728_);
    crate::leanh::lean_closure_set(v___f_729_, 6, v_inst_720_);
    crate::leanh::lean_closure_set(v___f_729_, 7, v_toBind_725_);
    v___x_730_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_730_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_730_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_730_, 2, v_a_723_);
    v___x_731_ = crate::leanh::lean_apply_2(v_inst_720_, crate::leanh::lean_box(0), v___x_730_);
    v___x_732_ = crate::leanh::lean_apply_4(
        v_toBind_725_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_731_,
        v___f_729_,
    );
    return v___x_732_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___redArg___boxed(
    mut v_inst_733_: *mut crate::leanh::LeanObject,
    mut v_inst_734_: *mut crate::leanh::LeanObject,
    mut v_e_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ =
        l_Lean_ForEachExprWhere_checked___redArg(v_inst_733_, v_inst_734_, v_e_735_, v_a_736_);
    crate::leanh::lean_dec(v_a_736_);
    return v_res_737_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked(
    mut v_00_u03c9_738_: *mut crate::leanh::LeanObject,
    mut v_m_739_: *mut crate::leanh::LeanObject,
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_inst_742_: *mut crate::leanh::LeanObject,
    mut v_e_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ =
        l_Lean_ForEachExprWhere_checked___redArg(v_inst_741_, v_inst_742_, v_e_743_, v_a_744_);
    return v___x_745_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___boxed(
    mut v_00_u03c9_746_: *mut crate::leanh::LeanObject,
    mut v_m_747_: *mut crate::leanh::LeanObject,
    mut v_inst_748_: *mut crate::leanh::LeanObject,
    mut v_inst_749_: *mut crate::leanh::LeanObject,
    mut v_inst_750_: *mut crate::leanh::LeanObject,
    mut v_e_751_: *mut crate::leanh::LeanObject,
    mut v_a_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Lean_ForEachExprWhere_checked(
        v_00_u03c9_746_,
        v_m_747_,
        v_inst_748_,
        v_inst_749_,
        v_inst_750_,
        v_e_751_,
        v_a_752_,
    );
    crate::leanh::lean_dec(v_a_752_);
    return v_res_753_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(
    mut v_p_754_: *mut crate::leanh::LeanObject,
    mut v_e_755_: *mut crate::leanh::LeanObject,
    mut v___f_756_: *mut crate::leanh::LeanObject,
    mut v_a_757_: *mut crate::leanh::LeanObject,
    mut v_inst_758_: *mut crate::leanh::LeanObject,
    mut v_inst_759_: *mut crate::leanh::LeanObject,
    mut v_toBind_760_: *mut crate::leanh::LeanObject,
    mut v___f_761_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_a_763_ == 0 {
        let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: u8 = 0;
        crate::leanh::lean_dec_ref(v_toApplicative_762_);
        crate::leanh::lean_inc_ref(v_e_755_);
        v___x_764_ = crate::leanh::lean_apply_1(v_p_754_, v_e_755_);
        v___x_765_ = (crate::leanh::lean_unbox(v___x_764_) as u8);
        if v___x_765_ == 0 {
            let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_761_);
            crate::leanh::lean_dec(v_toBind_760_);
            crate::leanh::lean_dec_ref(v_inst_759_);
            crate::leanh::lean_dec(v_inst_758_);
            crate::leanh::lean_dec_ref(v_e_755_);
            v___x_766_ = crate::leanh::lean_box(0);
            crate::leanh::lean_inc(v_a_757_);
            v___x_767_ = crate::leanh::lean_apply_2(v___f_756_, v___x_766_, v_a_757_);
            return v___x_767_;
        } else {
            let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_756_);
            v___x_768_ = l_Lean_ForEachExprWhere_checked___redArg(
                v_inst_758_,
                v_inst_759_,
                v_e_755_,
                v_a_757_,
            );
            v___x_769_ = crate::leanh::lean_apply_4(
                v_toBind_760_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_768_,
                v___f_761_,
            );
            return v___x_769_;
        }
    } else {
        let mut v_toPure_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_761_);
        crate::leanh::lean_dec(v_toBind_760_);
        crate::leanh::lean_dec_ref(v_inst_759_);
        crate::leanh::lean_dec(v_inst_758_);
        crate::leanh::lean_dec(v___f_756_);
        crate::leanh::lean_dec_ref(v_e_755_);
        crate::leanh::lean_dec_ref(v_p_754_);
        v_toPure_770_ = crate::leanh::lean_ctor_get(v_toApplicative_762_, 1);
        crate::leanh::lean_inc(v_toPure_770_);
        crate::leanh::lean_dec_ref(v_toApplicative_762_);
        v___x_771_ = crate::leanh::lean_box(0);
        v___x_772_ =
            crate::leanh::lean_apply_2(v_toPure_770_, crate::leanh::lean_box(0), v___x_771_);
        return v___x_772_;
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(
    mut v_p_773_: *mut crate::leanh::LeanObject,
    mut v_e_774_: *mut crate::leanh::LeanObject,
    mut v___f_775_: *mut crate::leanh::LeanObject,
    mut v_a_776_: *mut crate::leanh::LeanObject,
    mut v_inst_777_: *mut crate::leanh::LeanObject,
    mut v_inst_778_: *mut crate::leanh::LeanObject,
    mut v_toBind_779_: *mut crate::leanh::LeanObject,
    mut v___f_780_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_781_: *mut crate::leanh::LeanObject,
    mut v_a_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_783_: u8 = 0;
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_783_ = (crate::leanh::lean_unbox(v_a_782_) as u8);
    v_res_784_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(
            v_p_773_,
            v_e_774_,
            v___f_775_,
            v_a_776_,
            v_inst_777_,
            v_inst_778_,
            v_toBind_779_,
            v___f_780_,
            v_toApplicative_781_,
            v_a_boxed_783_,
        );
    crate::leanh::lean_dec(v_a_776_);
    return v_res_784_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(
    mut v_stopWhenVisited_785_: u8,
    mut v___f_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_788_: *mut crate::leanh::LeanObject,
    mut v_a_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_stopWhenVisited_785_ == 0 {
        let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_788_);
        v___x_790_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_a_787_);
        v___x_791_ = crate::leanh::lean_apply_2(v___f_786_, v___x_790_, v_a_787_);
        return v___x_791_;
    } else {
        let mut v_toPure_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_786_);
        v_toPure_792_ = crate::leanh::lean_ctor_get(v_toApplicative_788_, 1);
        crate::leanh::lean_inc(v_toPure_792_);
        crate::leanh::lean_dec_ref(v_toApplicative_788_);
        v___x_793_ = crate::leanh::lean_box(0);
        v___x_794_ =
            crate::leanh::lean_apply_2(v_toPure_792_, crate::leanh::lean_box(0), v___x_793_);
        return v___x_794_;
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(
    mut v_stopWhenVisited_795_: *mut crate::leanh::LeanObject,
    mut v___f_796_: *mut crate::leanh::LeanObject,
    mut v_a_797_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_800_: u8 = 0;
    let mut v_res_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_800_ = (crate::leanh::lean_unbox(v_stopWhenVisited_795_) as u8);
    v_res_801_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(
            v_stopWhenVisited_boxed_800_,
            v___f_796_,
            v_a_797_,
            v_toApplicative_798_,
            v_a_799_,
        );
    crate::leanh::lean_dec(v_a_797_);
    return v_res_801_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(
    mut v_f_802_: *mut crate::leanh::LeanObject,
    mut v_e_803_: *mut crate::leanh::LeanObject,
    mut v_toBind_804_: *mut crate::leanh::LeanObject,
    mut v___f_805_: *mut crate::leanh::LeanObject,
    mut v___f_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_a_808_ == 0 {
        let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_806_);
        v___x_809_ = crate::leanh::lean_apply_1(v_f_802_, v_e_803_);
        v___x_810_ = crate::leanh::lean_apply_4(
            v_toBind_804_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_809_,
            v___f_805_,
        );
        return v___x_810_;
    } else {
        let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_805_);
        crate::leanh::lean_dec(v_toBind_804_);
        crate::leanh::lean_dec_ref(v_e_803_);
        crate::leanh::lean_dec(v_f_802_);
        v___x_811_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_a_807_);
        v___x_812_ = crate::leanh::lean_apply_2(v___f_806_, v___x_811_, v_a_807_);
        return v___x_812_;
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(
    mut v_f_813_: *mut crate::leanh::LeanObject,
    mut v_e_814_: *mut crate::leanh::LeanObject,
    mut v_toBind_815_: *mut crate::leanh::LeanObject,
    mut v___f_816_: *mut crate::leanh::LeanObject,
    mut v___f_817_: *mut crate::leanh::LeanObject,
    mut v_a_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_820_: u8 = 0;
    let mut v_res_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_820_ = (crate::leanh::lean_unbox(v_a_819_) as u8);
    v_res_821_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(
            v_f_813_,
            v_e_814_,
            v_toBind_815_,
            v___f_816_,
            v___f_817_,
            v_a_818_,
            v_a_boxed_820_,
        );
    crate::leanh::lean_dec(v_a_818_);
    return v_res_821_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(
    mut v_inst_822_: *mut crate::leanh::LeanObject,
    mut v_inst_823_: *mut crate::leanh::LeanObject,
    mut v_p_824_: *mut crate::leanh::LeanObject,
    mut v_f_825_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_826_: *mut crate::leanh::LeanObject,
    mut v_b_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_830_: u8 = 0;
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_830_ = (crate::leanh::lean_unbox(v_stopWhenVisited_826_) as u8);
    v_res_831_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(
            v_inst_822_,
            v_inst_823_,
            v_p_824_,
            v_f_825_,
            v_stopWhenVisited_boxed_830_,
            v_b_827_,
            v___y_828_,
            v_a_829_,
        );
    crate::leanh::lean_dec(v___y_828_);
    return v_res_831_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(
    mut v_inst_832_: *mut crate::leanh::LeanObject,
    mut v_inst_833_: *mut crate::leanh::LeanObject,
    mut v_p_834_: *mut crate::leanh::LeanObject,
    mut v_f_835_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_836_: u8,
    mut v_body_837_: *mut crate::leanh::LeanObject,
    mut v___y_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_832_,
        v_inst_833_,
        v_p_834_,
        v_f_835_,
        v_stopWhenVisited_836_,
        v_body_837_,
        v___y_838_,
    );
    return v___x_840_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(
    mut v_inst_841_: *mut crate::leanh::LeanObject,
    mut v_inst_842_: *mut crate::leanh::LeanObject,
    mut v_p_843_: *mut crate::leanh::LeanObject,
    mut v_f_844_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_845_: *mut crate::leanh::LeanObject,
    mut v_body_846_: *mut crate::leanh::LeanObject,
    mut v___y_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_849_: u8 = 0;
    let mut v_res_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_849_ = (crate::leanh::lean_unbox(v_stopWhenVisited_845_) as u8);
    v_res_850_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(
            v_inst_841_,
            v_inst_842_,
            v_p_843_,
            v_f_844_,
            v_stopWhenVisited_boxed_849_,
            v_body_846_,
            v___y_847_,
            v_a_848_,
        );
    crate::leanh::lean_dec(v___y_847_);
    return v_res_850_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(
    mut v_inst_851_: *mut crate::leanh::LeanObject,
    mut v_inst_852_: *mut crate::leanh::LeanObject,
    mut v_p_853_: *mut crate::leanh::LeanObject,
    mut v_f_854_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_855_: u8,
    mut v_value_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v_toBind_858_: *mut crate::leanh::LeanObject,
    mut v___f_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_851_,
        v_inst_852_,
        v_p_853_,
        v_f_854_,
        v_stopWhenVisited_855_,
        v_value_856_,
        v___y_857_,
    );
    v___x_862_ = crate::leanh::lean_apply_4(
        v_toBind_858_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_861_,
        v___f_859_,
    );
    return v___x_862_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(
    mut v_inst_863_: *mut crate::leanh::LeanObject,
    mut v_inst_864_: *mut crate::leanh::LeanObject,
    mut v_p_865_: *mut crate::leanh::LeanObject,
    mut v_f_866_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_867_: *mut crate::leanh::LeanObject,
    mut v_value_868_: *mut crate::leanh::LeanObject,
    mut v___y_869_: *mut crate::leanh::LeanObject,
    mut v_toBind_870_: *mut crate::leanh::LeanObject,
    mut v___f_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_873_: u8 = 0;
    let mut v_res_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_873_ = (crate::leanh::lean_unbox(v_stopWhenVisited_867_) as u8);
    v_res_874_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(
            v_inst_863_,
            v_inst_864_,
            v_p_865_,
            v_f_866_,
            v_stopWhenVisited_boxed_873_,
            v_value_868_,
            v___y_869_,
            v_toBind_870_,
            v___f_871_,
            v_a_872_,
        );
    crate::leanh::lean_dec(v___y_869_);
    return v_res_874_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(
    mut v_inst_875_: *mut crate::leanh::LeanObject,
    mut v_inst_876_: *mut crate::leanh::LeanObject,
    mut v_p_877_: *mut crate::leanh::LeanObject,
    mut v_f_878_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_879_: u8,
    mut v_arg_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v_a_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_875_,
        v_inst_876_,
        v_p_877_,
        v_f_878_,
        v_stopWhenVisited_879_,
        v_arg_880_,
        v___y_881_,
    );
    return v___x_883_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(
    mut v_inst_884_: *mut crate::leanh::LeanObject,
    mut v_inst_885_: *mut crate::leanh::LeanObject,
    mut v_p_886_: *mut crate::leanh::LeanObject,
    mut v_f_887_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_888_: *mut crate::leanh::LeanObject,
    mut v_arg_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_892_: u8 = 0;
    let mut v_res_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_892_ = (crate::leanh::lean_unbox(v_stopWhenVisited_888_) as u8);
    v_res_893_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(
            v_inst_884_,
            v_inst_885_,
            v_p_886_,
            v_f_887_,
            v_stopWhenVisited_boxed_892_,
            v_arg_889_,
            v___y_890_,
            v_a_891_,
        );
    crate::leanh::lean_dec(v___y_890_);
    return v_res_893_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(
    mut v_inst_894_: *mut crate::leanh::LeanObject,
    mut v_inst_895_: *mut crate::leanh::LeanObject,
    mut v_p_896_: *mut crate::leanh::LeanObject,
    mut v_f_897_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_898_: u8,
    mut v_toBind_899_: *mut crate::leanh::LeanObject,
    mut v_e_900_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_901_: *mut crate::leanh::LeanObject,
    mut v_____r_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_900_) {
                7 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    v_binderType_911_ = crate::leanh::lean_ctor_get(v_e_900_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_911_);
                    v_body_912_ = crate::leanh::lean_ctor_get(v_e_900_, 2);
                    crate::leanh::lean_inc_ref(v_body_912_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 3);
                    v_d_905_ = v_binderType_911_;
                    v_b_906_ = v_body_912_;
                    state = 1;
                    continue;
                }
                6 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    v_binderType_913_ = crate::leanh::lean_ctor_get(v_e_900_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_913_);
                    v_body_914_ = crate::leanh::lean_ctor_get(v_e_900_, 2);
                    crate::leanh::lean_inc_ref(v_body_914_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 3);
                    v_d_905_ = v_binderType_913_;
                    v_b_906_ = v_body_914_;
                    state = 1;
                    continue;
                }
                8 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    v_type_915_ = crate::leanh::lean_ctor_get(v_e_900_, 1);
                    crate::leanh::lean_inc_ref(v_type_915_);
                    v_value_916_ = crate::leanh::lean_ctor_get(v_e_900_, 2);
                    crate::leanh::lean_inc_ref(v_value_916_);
                    v_body_917_ = crate::leanh::lean_ctor_get(v_e_900_, 3);
                    crate::leanh::lean_inc_ref(v_body_917_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 4);
                    v___x_918_ = crate::leanh::lean_box((v_stopWhenVisited_898_) as usize);
                    crate::leanh::lean_inc_n(v___y_903_, 2);
                    crate::leanh::lean_inc_n(v_f_897_, 2);
                    crate::leanh::lean_inc_ref_n(v_p_896_, 2);
                    crate::leanh::lean_inc_ref_n(v_inst_895_, 2);
                    crate::leanh::lean_inc_n(v_inst_894_, 2);
                    v___f_919_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 8, 7);
                    crate::leanh::lean_closure_set(v___f_919_, 0, v_inst_894_);
                    crate::leanh::lean_closure_set(v___f_919_, 1, v_inst_895_);
                    crate::leanh::lean_closure_set(v___f_919_, 2, v_p_896_);
                    crate::leanh::lean_closure_set(v___f_919_, 3, v_f_897_);
                    crate::leanh::lean_closure_set(v___f_919_, 4, v___x_918_);
                    crate::leanh::lean_closure_set(v___f_919_, 5, v_body_917_);
                    crate::leanh::lean_closure_set(v___f_919_, 6, v___y_903_);
                    v___x_920_ = crate::leanh::lean_box((v_stopWhenVisited_898_) as usize);
                    crate::leanh::lean_inc(v_toBind_899_);
                    v___f_921_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 9);
                    crate::leanh::lean_closure_set(v___f_921_, 0, v_inst_894_);
                    crate::leanh::lean_closure_set(v___f_921_, 1, v_inst_895_);
                    crate::leanh::lean_closure_set(v___f_921_, 2, v_p_896_);
                    crate::leanh::lean_closure_set(v___f_921_, 3, v_f_897_);
                    crate::leanh::lean_closure_set(v___f_921_, 4, v___x_920_);
                    crate::leanh::lean_closure_set(v___f_921_, 5, v_value_916_);
                    crate::leanh::lean_closure_set(v___f_921_, 6, v___y_903_);
                    crate::leanh::lean_closure_set(v___f_921_, 7, v_toBind_899_);
                    crate::leanh::lean_closure_set(v___f_921_, 8, v___f_919_);
                    v___x_922_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_894_, v_inst_895_, v_p_896_, v_f_897_, v_stopWhenVisited_898_, v_type_915_, v___y_903_);
                    v___x_923_ = crate::leanh::lean_apply_4(
                        v_toBind_899_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_922_,
                        v___f_921_,
                    );
                    return v___x_923_;
                }
                5 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    v_fn_924_ = crate::leanh::lean_ctor_get(v_e_900_, 0);
                    crate::leanh::lean_inc_ref(v_fn_924_);
                    v_arg_925_ = crate::leanh::lean_ctor_get(v_e_900_, 1);
                    crate::leanh::lean_inc_ref(v_arg_925_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 2);
                    v___x_926_ = crate::leanh::lean_box((v_stopWhenVisited_898_) as usize);
                    crate::leanh::lean_inc(v___y_903_);
                    crate::leanh::lean_inc(v_f_897_);
                    crate::leanh::lean_inc_ref(v_p_896_);
                    crate::leanh::lean_inc_ref(v_inst_895_);
                    crate::leanh::lean_inc(v_inst_894_);
                    v___f_927_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 8, 7);
                    crate::leanh::lean_closure_set(v___f_927_, 0, v_inst_894_);
                    crate::leanh::lean_closure_set(v___f_927_, 1, v_inst_895_);
                    crate::leanh::lean_closure_set(v___f_927_, 2, v_p_896_);
                    crate::leanh::lean_closure_set(v___f_927_, 3, v_f_897_);
                    crate::leanh::lean_closure_set(v___f_927_, 4, v___x_926_);
                    crate::leanh::lean_closure_set(v___f_927_, 5, v_arg_925_);
                    crate::leanh::lean_closure_set(v___f_927_, 6, v___y_903_);
                    v___x_928_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_894_, v_inst_895_, v_p_896_, v_f_897_, v_stopWhenVisited_898_, v_fn_924_, v___y_903_);
                    v___x_929_ = crate::leanh::lean_apply_4(
                        v_toBind_899_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_928_,
                        v___f_927_,
                    );
                    return v___x_929_;
                }
                10 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    crate::leanh::lean_dec(v_toBind_899_);
                    v_expr_930_ = crate::leanh::lean_ctor_get(v_e_900_, 1);
                    crate::leanh::lean_inc_ref(v_expr_930_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 2);
                    v___x_931_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_894_, v_inst_895_, v_p_896_, v_f_897_, v_stopWhenVisited_898_, v_expr_930_, v___y_903_);
                    return v___x_931_;
                }
                11 => {
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    crate::leanh::lean_dec(v_toBind_899_);
                    v_struct_932_ = crate::leanh::lean_ctor_get(v_e_900_, 2);
                    crate::leanh::lean_inc_ref(v_struct_932_);
                    crate::leanh::lean_dec_ref_known(v_e_900_, 3);
                    v___x_933_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_894_, v_inst_895_, v_p_896_, v_f_897_, v_stopWhenVisited_898_, v_struct_932_, v___y_903_);
                    return v___x_933_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_900_);
                    crate::leanh::lean_dec(v_toBind_899_);
                    crate::leanh::lean_dec(v_f_897_);
                    crate::leanh::lean_dec_ref(v_p_896_);
                    crate::leanh::lean_dec_ref(v_inst_895_);
                    crate::leanh::lean_dec(v_inst_894_);
                    v_toPure_934_ = crate::leanh::lean_ctor_get(v_toApplicative_901_, 1);
                    crate::leanh::lean_inc(v_toPure_934_);
                    crate::leanh::lean_dec_ref(v_toApplicative_901_);
                    v___x_935_ = crate::leanh::lean_box(0);
                    v___x_936_ = crate::leanh::lean_apply_2(
                        v_toPure_934_,
                        crate::leanh::lean_box(0),
                        v___x_935_,
                    );
                    return v___x_936_;
                }
            },
            1 => {
                v___x_907_ = crate::leanh::lean_box((v_stopWhenVisited_898_) as usize);
                crate::leanh::lean_inc(v___y_903_);
                crate::leanh::lean_inc(v_f_897_);
                crate::leanh::lean_inc_ref(v_p_896_);
                crate::leanh::lean_inc_ref(v_inst_895_);
                crate::leanh::lean_inc(v_inst_894_);
                v___f_908_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
                crate::leanh::lean_closure_set(v___f_908_, 0, v_inst_894_);
                crate::leanh::lean_closure_set(v___f_908_, 1, v_inst_895_);
                crate::leanh::lean_closure_set(v___f_908_, 2, v_p_896_);
                crate::leanh::lean_closure_set(v___f_908_, 3, v_f_897_);
                crate::leanh::lean_closure_set(v___f_908_, 4, v___x_907_);
                crate::leanh::lean_closure_set(v___f_908_, 5, v_b_906_);
                crate::leanh::lean_closure_set(v___f_908_, 6, v___y_903_);
                v___x_909_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_894_, v_inst_895_, v_p_896_, v_f_897_, v_stopWhenVisited_898_, v_d_905_, v___y_903_);
                v___x_910_ = crate::leanh::lean_apply_4(
                    v_toBind_899_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_909_,
                    v___f_908_,
                );
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(
    mut v_inst_937_: *mut crate::leanh::LeanObject,
    mut v_inst_938_: *mut crate::leanh::LeanObject,
    mut v_p_939_: *mut crate::leanh::LeanObject,
    mut v_f_940_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_941_: *mut crate::leanh::LeanObject,
    mut v_toBind_942_: *mut crate::leanh::LeanObject,
    mut v_e_943_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_944_: *mut crate::leanh::LeanObject,
    mut v_____r_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_947_: u8 = 0;
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_947_ = (crate::leanh::lean_unbox(v_stopWhenVisited_941_) as u8);
    v_res_948_ =
        l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(
            v_inst_937_,
            v_inst_938_,
            v_p_939_,
            v_f_940_,
            v_stopWhenVisited_boxed_947_,
            v_toBind_942_,
            v_e_943_,
            v_toApplicative_944_,
            v_____r_945_,
            v___y_946_,
        );
    crate::leanh::lean_dec(v___y_946_);
    return v_res_948_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
    mut v_inst_949_: *mut crate::leanh::LeanObject,
    mut v_inst_950_: *mut crate::leanh::LeanObject,
    mut v_p_951_: *mut crate::leanh::LeanObject,
    mut v_f_952_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_953_: u8,
    mut v_e_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_956_ = crate::leanh::lean_ctor_get(v_inst_950_, 0);
    v_toBind_957_ = crate::leanh::lean_ctor_get(v_inst_950_, 1);
    crate::leanh::lean_inc_n(v_toBind_957_, 4);
    v___x_958_ = crate::leanh::lean_box((v_stopWhenVisited_953_) as usize);
    crate::leanh::lean_inc_ref_n(v_toApplicative_956_, 3);
    crate::leanh::lean_inc_ref_n(v_e_954_, 3);
    crate::leanh::lean_inc(v_f_952_);
    crate::leanh::lean_inc_ref(v_p_951_);
    crate::leanh::lean_inc_ref_n(v_inst_950_, 2);
    crate::leanh::lean_inc_n(v_inst_949_, 2);
    v___f_959_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed as *mut core::ffi::c_void, 10, 8);
    crate::leanh::lean_closure_set(v___f_959_, 0, v_inst_949_);
    crate::leanh::lean_closure_set(v___f_959_, 1, v_inst_950_);
    crate::leanh::lean_closure_set(v___f_959_, 2, v_p_951_);
    crate::leanh::lean_closure_set(v___f_959_, 3, v_f_952_);
    crate::leanh::lean_closure_set(v___f_959_, 4, v___x_958_);
    crate::leanh::lean_closure_set(v___f_959_, 5, v_toBind_957_);
    crate::leanh::lean_closure_set(v___f_959_, 6, v_e_954_);
    crate::leanh::lean_closure_set(v___f_959_, 7, v_toApplicative_956_);
    v___x_960_ = crate::leanh::lean_box((v_stopWhenVisited_953_) as usize);
    crate::leanh::lean_inc_n(v_a_955_, 3);
    crate::leanh::lean_inc_ref_n(v___f_959_, 2);
    v___f_961_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_961_, 0, v___x_960_);
    crate::leanh::lean_closure_set(v___f_961_, 1, v___f_959_);
    crate::leanh::lean_closure_set(v___f_961_, 2, v_a_955_);
    crate::leanh::lean_closure_set(v___f_961_, 3, v_toApplicative_956_);
    v___f_962_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed as *mut core::ffi::c_void, 7, 6);
    crate::leanh::lean_closure_set(v___f_962_, 0, v_f_952_);
    crate::leanh::lean_closure_set(v___f_962_, 1, v_e_954_);
    crate::leanh::lean_closure_set(v___f_962_, 2, v_toBind_957_);
    crate::leanh::lean_closure_set(v___f_962_, 3, v___f_961_);
    crate::leanh::lean_closure_set(v___f_962_, 4, v___f_959_);
    crate::leanh::lean_closure_set(v___f_962_, 5, v_a_955_);
    v___f_963_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed as *mut core::ffi::c_void, 10, 9);
    crate::leanh::lean_closure_set(v___f_963_, 0, v_p_951_);
    crate::leanh::lean_closure_set(v___f_963_, 1, v_e_954_);
    crate::leanh::lean_closure_set(v___f_963_, 2, v___f_959_);
    crate::leanh::lean_closure_set(v___f_963_, 3, v_a_955_);
    crate::leanh::lean_closure_set(v___f_963_, 4, v_inst_949_);
    crate::leanh::lean_closure_set(v___f_963_, 5, v_inst_950_);
    crate::leanh::lean_closure_set(v___f_963_, 6, v_toBind_957_);
    crate::leanh::lean_closure_set(v___f_963_, 7, v___f_962_);
    crate::leanh::lean_closure_set(v___f_963_, 8, v_toApplicative_956_);
    v___x_964_ =
        l_Lean_ForEachExprWhere_visited___redArg(v_inst_949_, v_inst_950_, v_e_954_, v_a_955_);
    v___x_965_ = crate::leanh::lean_apply_4(
        v_toBind_957_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_964_,
        v___f_963_,
    );
    return v___x_965_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(
    mut v_inst_966_: *mut crate::leanh::LeanObject,
    mut v_inst_967_: *mut crate::leanh::LeanObject,
    mut v_p_968_: *mut crate::leanh::LeanObject,
    mut v_f_969_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_970_: u8,
    mut v_b_971_: *mut crate::leanh::LeanObject,
    mut v___y_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_966_,
        v_inst_967_,
        v_p_968_,
        v_f_969_,
        v_stopWhenVisited_970_,
        v_b_971_,
        v___y_972_,
    );
    return v___x_974_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(
    mut v_inst_975_: *mut crate::leanh::LeanObject,
    mut v_inst_976_: *mut crate::leanh::LeanObject,
    mut v_p_977_: *mut crate::leanh::LeanObject,
    mut v_f_978_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_979_: *mut crate::leanh::LeanObject,
    mut v_e_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_982_: u8 = 0;
    let mut v_res_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_982_ = (crate::leanh::lean_unbox(v_stopWhenVisited_979_) as u8);
    v_res_983_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_975_,
        v_inst_976_,
        v_p_977_,
        v_f_978_,
        v_stopWhenVisited_boxed_982_,
        v_e_980_,
        v_a_981_,
    );
    crate::leanh::lean_dec(v_a_981_);
    return v_res_983_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(
    mut v_00_u03c9_984_: *mut crate::leanh::LeanObject,
    mut v_m_985_: *mut crate::leanh::LeanObject,
    mut v_inst_986_: *mut crate::leanh::LeanObject,
    mut v_inst_987_: *mut crate::leanh::LeanObject,
    mut v_inst_988_: *mut crate::leanh::LeanObject,
    mut v_p_989_: *mut crate::leanh::LeanObject,
    mut v_f_990_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_991_: u8,
    mut v_e_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_987_,
        v_inst_988_,
        v_p_989_,
        v_f_990_,
        v_stopWhenVisited_991_,
        v_e_992_,
        v_a_993_,
    );
    return v___x_994_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(
    mut v_00_u03c9_995_: *mut crate::leanh::LeanObject,
    mut v_m_996_: *mut crate::leanh::LeanObject,
    mut v_inst_997_: *mut crate::leanh::LeanObject,
    mut v_inst_998_: *mut crate::leanh::LeanObject,
    mut v_inst_999_: *mut crate::leanh::LeanObject,
    mut v_p_1000_: *mut crate::leanh::LeanObject,
    mut v_f_1001_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1002_: *mut crate::leanh::LeanObject,
    mut v_e_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_1005_: u8 = 0;
    let mut v_res_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_1005_ = (crate::leanh::lean_unbox(v_stopWhenVisited_1002_) as u8);
    v_res_1006_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(
        v_00_u03c9_995_,
        v_m_996_,
        v_inst_997_,
        v_inst_998_,
        v_inst_999_,
        v_p_1000_,
        v_f_1001_,
        v_stopWhenVisited_boxed_1005_,
        v_e_1003_,
        v_a_1004_,
    );
    crate::leanh::lean_dec(v_a_1004_);
    return v_res_1006_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___lam__0(
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_toPure_1008_: *mut crate::leanh::LeanObject,
    mut v_s_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1010_, 0, v_a_1007_);
    crate::leanh::lean_ctor_set(v___x_1010_, 1, v_s_1009_);
    v___x_1011_ =
        crate::leanh::lean_apply_2(v_toPure_1008_, crate::leanh::lean_box(0), v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___lam__1(
    mut v_toPure_1012_: *mut crate::leanh::LeanObject,
    mut v_ref_1013_: *mut crate::leanh::LeanObject,
    mut v_inst_1014_: *mut crate::leanh::LeanObject,
    mut v_toBind_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1017_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_visit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1017_, 0, v_a_1016_);
    crate::leanh::lean_closure_set(v___f_1017_, 1, v_toPure_1012_);
    v___x_1018_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1018_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1018_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1018_, 2, v_ref_1013_);
    v___x_1019_ = crate::leanh::lean_apply_2(v_inst_1014_, crate::leanh::lean_box(0), v___x_1018_);
    v___x_1020_ = crate::leanh::lean_apply_4(
        v_toBind_1015_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1019_,
        v___f_1017_,
    );
    return v___x_1020_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___lam__2(
    mut v_toPure_1021_: *mut crate::leanh::LeanObject,
    mut v_inst_1022_: *mut crate::leanh::LeanObject,
    mut v_toBind_1023_: *mut crate::leanh::LeanObject,
    mut v_inst_1024_: *mut crate::leanh::LeanObject,
    mut v_p_1025_: *mut crate::leanh::LeanObject,
    mut v_f_1026_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1027_: u8,
    mut v_e_1028_: *mut crate::leanh::LeanObject,
    mut v_ref_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1023_);
    crate::leanh::lean_inc(v_inst_1022_);
    crate::leanh::lean_inc(v_ref_1029_);
    v___f_1030_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_visit___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1030_, 0, v_toPure_1021_);
    crate::leanh::lean_closure_set(v___f_1030_, 1, v_ref_1029_);
    crate::leanh::lean_closure_set(v___f_1030_, 2, v_inst_1022_);
    crate::leanh::lean_closure_set(v___f_1030_, 3, v_toBind_1023_);
    v___x_1031_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(
        v_inst_1022_,
        v_inst_1024_,
        v_p_1025_,
        v_f_1026_,
        v_stopWhenVisited_1027_,
        v_e_1028_,
        v_ref_1029_,
    );
    crate::leanh::lean_dec(v_ref_1029_);
    v___x_1032_ = crate::leanh::lean_apply_4(
        v_toBind_1023_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1031_,
        v___f_1030_,
    );
    return v___x_1032_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(
    mut v_toPure_1033_: *mut crate::leanh::LeanObject,
    mut v_inst_1034_: *mut crate::leanh::LeanObject,
    mut v_toBind_1035_: *mut crate::leanh::LeanObject,
    mut v_inst_1036_: *mut crate::leanh::LeanObject,
    mut v_p_1037_: *mut crate::leanh::LeanObject,
    mut v_f_1038_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1039_: *mut crate::leanh::LeanObject,
    mut v_e_1040_: *mut crate::leanh::LeanObject,
    mut v_ref_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_1042_: u8 = 0;
    let mut v_res_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_1042_ = (crate::leanh::lean_unbox(v_stopWhenVisited_1039_) as u8);
    v_res_1043_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(
        v_toPure_1033_,
        v_inst_1034_,
        v_toBind_1035_,
        v_inst_1036_,
        v_p_1037_,
        v_f_1038_,
        v_stopWhenVisited_boxed_1042_,
        v_e_1040_,
        v_ref_1041_,
    );
    return v_res_1043_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___lam__3(
    mut v_toPure_1044_: *mut crate::leanh::LeanObject,
    mut v_____x_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1046_ = crate::leanh::lean_ctor_get(v_____x_1045_, 0);
    crate::leanh::lean_inc(v_fst_1046_);
    crate::leanh::lean_dec_ref(v_____x_1045_);
    v___x_1047_ =
        crate::leanh::lean_apply_2(v_toPure_1044_, crate::leanh::lean_box(0), v_fst_1046_);
    return v___x_1047_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = l_Lean_ForEachExprWhere_initCache;
    v___x_1049_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1049_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1049_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1049_, 2, v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg(
    mut v_inst_1050_: *mut crate::leanh::LeanObject,
    mut v_inst_1051_: *mut crate::leanh::LeanObject,
    mut v_p_1052_: *mut crate::leanh::LeanObject,
    mut v_f_1053_: *mut crate::leanh::LeanObject,
    mut v_e_1054_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1055_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1056_ = crate::leanh::lean_ctor_get(v_inst_1051_, 0);
    v_toBind_1057_ = crate::leanh::lean_ctor_get(v_inst_1051_, 1);
    crate::leanh::lean_inc_n(v_toBind_1057_, 3);
    v_toPure_1058_ = crate::leanh::lean_ctor_get(v_toApplicative_1056_, 1);
    crate::leanh::lean_inc_n(v_toPure_1058_, 2);
    v___x_1059_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visit___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visit___redArg___closed__0_once),
        _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0,
    );
    crate::leanh::lean_inc(v_inst_1050_);
    v___x_1060_ = crate::leanh::lean_apply_2(v_inst_1050_, crate::leanh::lean_box(0), v___x_1059_);
    v___x_1061_ = crate::leanh::lean_box((v_stopWhenVisited_1055_) as usize);
    v___f_1062_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1062_, 0, v_toPure_1058_);
    crate::leanh::lean_closure_set(v___f_1062_, 1, v_inst_1050_);
    crate::leanh::lean_closure_set(v___f_1062_, 2, v_toBind_1057_);
    crate::leanh::lean_closure_set(v___f_1062_, 3, v_inst_1051_);
    crate::leanh::lean_closure_set(v___f_1062_, 4, v_p_1052_);
    crate::leanh::lean_closure_set(v___f_1062_, 5, v_f_1053_);
    crate::leanh::lean_closure_set(v___f_1062_, 6, v___x_1061_);
    crate::leanh::lean_closure_set(v___f_1062_, 7, v_e_1054_);
    v___f_1063_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExprWhere_visit___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1063_, 0, v_toPure_1058_);
    v___x_1064_ = crate::leanh::lean_apply_4(
        v_toBind_1057_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1060_,
        v___f_1062_,
    );
    v___x_1065_ = crate::leanh::lean_apply_4(
        v_toBind_1057_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1064_,
        v___f_1063_,
    );
    return v___x_1065_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___redArg___boxed(
    mut v_inst_1066_: *mut crate::leanh::LeanObject,
    mut v_inst_1067_: *mut crate::leanh::LeanObject,
    mut v_p_1068_: *mut crate::leanh::LeanObject,
    mut v_f_1069_: *mut crate::leanh::LeanObject,
    mut v_e_1070_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_1072_: u8 = 0;
    let mut v_res_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_1072_ = (crate::leanh::lean_unbox(v_stopWhenVisited_1071_) as u8);
    v_res_1073_ = l_Lean_ForEachExprWhere_visit___redArg(
        v_inst_1066_,
        v_inst_1067_,
        v_p_1068_,
        v_f_1069_,
        v_e_1070_,
        v_stopWhenVisited_boxed_1072_,
    );
    return v_res_1073_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit(
    mut v_00_u03c9_1074_: *mut crate::leanh::LeanObject,
    mut v_m_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_inst_1077_: *mut crate::leanh::LeanObject,
    mut v_inst_1078_: *mut crate::leanh::LeanObject,
    mut v_p_1079_: *mut crate::leanh::LeanObject,
    mut v_f_1080_: *mut crate::leanh::LeanObject,
    mut v_e_1081_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1082_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_ForEachExprWhere_visit___redArg(
        v_inst_1077_,
        v_inst_1078_,
        v_p_1079_,
        v_f_1080_,
        v_e_1081_,
        v_stopWhenVisited_1082_,
    );
    return v___x_1083_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___boxed(
    mut v_00_u03c9_1084_: *mut crate::leanh::LeanObject,
    mut v_m_1085_: *mut crate::leanh::LeanObject,
    mut v_inst_1086_: *mut crate::leanh::LeanObject,
    mut v_inst_1087_: *mut crate::leanh::LeanObject,
    mut v_inst_1088_: *mut crate::leanh::LeanObject,
    mut v_p_1089_: *mut crate::leanh::LeanObject,
    mut v_f_1090_: *mut crate::leanh::LeanObject,
    mut v_e_1091_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_1093_: u8 = 0;
    let mut v_res_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_1093_ = (crate::leanh::lean_unbox(v_stopWhenVisited_1092_) as u8);
    v_res_1094_ = l_Lean_ForEachExprWhere_visit(
        v_00_u03c9_1084_,
        v_m_1085_,
        v_inst_1086_,
        v_inst_1087_,
        v_inst_1088_,
        v_p_1089_,
        v_f_1090_,
        v_e_1091_,
        v_stopWhenVisited_boxed_1093_,
    );
    return v_res_1094_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ForEachExprWhere(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_ForEachExprWhere_cacheSize = _init_l_Lean_ForEachExprWhere_cacheSize();
    l_Lean_ForEachExprWhere_initCache = _init_l_Lean_ForEachExprWhere_initCache();
    crate::leanh::lean_mark_persistent(l_Lean_ForEachExprWhere_initCache);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ForEachExprWhere(
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
pub unsafe fn initialize_Lean_Util_ForEachExprWhere(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ForEachExprWhere(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ForEachExprWhere(builtin);
}
