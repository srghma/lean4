// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: Lean.Compiler.LCNF.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Lean::Compiler::ExternAttr::l_Lean_instHashableExternAttrData_hash;
use crate::r#gen::Lean::Compiler::InlineAttrs::l_Lean_Compiler_instHashableInlineAttributeKind_hash;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, l_Lean_Compiler_LCNF_instHashableArg_hash___redArg,
    l_Lean_Compiler_LCNF_instHashableCtorInfo_hash, l_Lean_Compiler_LCNF_instHashableLetValue_hash,
    runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hash, l_Lean_instHashableFVarId_hash};
pub static l_Lean_Compiler_LCNF_instHashableParam___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instHashableParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instHashableParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_hashAlt___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_hashAlt___closed__0: u64 = 0;
pub unsafe fn l_Lean_Compiler_LCNF_instHashableParam___lam__0(
    mut v_p_500_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_fvarId_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u64 = 0;
    let mut v___x_504_: u64 = 0;
    let mut v___x_505_: u64 = 0;
    v_fvarId_501_ = crate::leanh::lean_ctor_get(v_p_500_, 0);
    v_type_502_ = crate::leanh::lean_ctor_get(v_p_500_, 2);
    v___x_503_ = l_Lean_instHashableFVarId_hash(v_fvarId_501_);
    v___x_504_ = l_Lean_Expr_hash(v_type_502_);
    v___x_505_ = lean_uint64_mix_hash(v___x_503_, v___x_504_);
    return v___x_505_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(
    mut v_p_506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_507_: u64 = 0;
    let mut v_r_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_507_ = l_Lean_Compiler_LCNF_instHashableParam___lam__0(v_p_506_);
    crate::leanh::lean_dec_ref(v_p_506_);
    v_r_508_ = crate::leanh::lean_box_uint64(v_res_507_);
    return v_r_508_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableParam(
    mut v_pu_510_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_511_ = l_Lean_Compiler_LCNF_instHashableParam___closed__0;
    return v___f_511_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableParam___boxed(
    mut v_pu_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_513_: u8 = 0;
    let mut v_res_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_513_ = (crate::leanh::lean_unbox(v_pu_512_) as u8);
    v_res_514_ = l_Lean_Compiler_LCNF_instHashableParam(v_pu_boxed_513_);
    return v_res_514_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(
    mut v_as_515_: *mut crate::leanh::LeanObject,
    mut v_i_516_: usize,
    mut v_stop_517_: usize,
    mut v_b_518_: u64,
) -> u64 {
    let mut v___x_519_: u8 = 0;
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u64 = 0;
    let mut v___x_524_: u64 = 0;
    let mut v___x_525_: u64 = 0;
    let mut v___x_526_: u64 = 0;
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_519_ = lean_usize_dec_eq(v_i_516_, v_stop_517_);
                if v___x_519_ == 0 {
                    v___x_520_ = lean_array_uget_borrowed(v_as_515_, v_i_516_);
                    v_fvarId_521_ = crate::leanh::lean_ctor_get(v___x_520_, 0);
                    v_type_522_ = crate::leanh::lean_ctor_get(v___x_520_, 2);
                    v___x_523_ = l_Lean_instHashableFVarId_hash(v_fvarId_521_);
                    v___x_524_ = l_Lean_Expr_hash(v_type_522_);
                    v___x_525_ = lean_uint64_mix_hash(v___x_523_, v___x_524_);
                    v___x_526_ = lean_uint64_mix_hash(v_b_518_, v___x_525_);
                    v___x_527_ = 1usize;
                    v___x_528_ = lean_usize_add(v_i_516_, v___x_527_);
                    v_i_516_ = v___x_528_;
                    v_b_518_ = v___x_526_;
                    state = 0;
                    continue;
                } else {
                    return v_b_518_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(
    mut v_as_530_: *mut crate::leanh::LeanObject,
    mut v_i_531_: *mut crate::leanh::LeanObject,
    mut v_stop_532_: *mut crate::leanh::LeanObject,
    mut v_b_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_534_: usize = 0;
    let mut v_stop_boxed_535_: usize = 0;
    let mut v_b_boxed_536_: u64 = 0;
    let mut v_res_537_: u64 = 0;
    let mut v_r_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_534_ = crate::leanh::lean_unbox_usize(v_i_531_);
    crate::leanh::lean_dec(v_i_531_);
    v_stop_boxed_535_ = crate::leanh::lean_unbox_usize(v_stop_532_);
    crate::leanh::lean_dec(v_stop_532_);
    v_b_boxed_536_ = crate::leanh::lean_unbox_uint64(v_b_533_);
    crate::leanh::lean_dec_ref(v_b_533_);
    v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_as_530_, v_i_boxed_534_, v_stop_boxed_535_, v_b_boxed_536_);
    crate::leanh::lean_dec_ref(v_as_530_);
    v_r_538_ = crate::leanh::lean_box_uint64(v_res_537_);
    return v_r_538_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashParams___redArg(
    mut v_ps_539_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_540_: u64 = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    v___x_540_ = 7u64;
    v___x_541_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_542_ = lean_array_get_size(v_ps_539_);
    v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
    if v___x_543_ == 0 {
        return v___x_540_;
    } else {
        let mut v___x_544_: u8 = 0;
        v___x_544_ = lean_nat_dec_le(v___x_542_, v___x_542_);
        if v___x_544_ == 0 {
            if v___x_543_ == 0 {
                return v___x_540_;
            } else {
                let mut v___x_545_: usize = 0;
                let mut v___x_546_: usize = 0;
                let mut v___x_547_: u64 = 0;
                v___x_545_ = 0usize;
                v___x_546_ = lean_usize_of_nat(v___x_542_);
                v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_539_, v___x_545_, v___x_546_, v___x_540_);
                return v___x_547_;
            }
        } else {
            let mut v___x_548_: usize = 0;
            let mut v___x_549_: usize = 0;
            let mut v___x_550_: u64 = 0;
            v___x_548_ = 0usize;
            v___x_549_ = lean_usize_of_nat(v___x_542_);
            v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_539_, v___x_548_, v___x_549_, v___x_540_);
            return v___x_550_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_hashParams___redArg___boxed(
    mut v_ps_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_552_: u64 = 0;
    let mut v_r_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_551_);
    crate::leanh::lean_dec_ref(v_ps_551_);
    v_r_553_ = crate::leanh::lean_box_uint64(v_res_552_);
    return v_r_553_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashParams(
    mut v_pu_554_: u8,
    mut v_ps_555_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_556_: u64 = 0;
    v___x_556_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashParams___boxed(
    mut v_pu_557_: *mut crate::leanh::LeanObject,
    mut v_ps_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_559_: u8 = 0;
    let mut v_res_560_: u64 = 0;
    let mut v_r_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_559_ = (crate::leanh::lean_unbox(v_pu_557_) as u8);
    v_res_560_ = l_Lean_Compiler_LCNF_hashParams(v_pu_boxed_559_, v_ps_558_);
    crate::leanh::lean_dec_ref(v_ps_558_);
    v_r_561_ = crate::leanh::lean_box_uint64(v_res_560_);
    return v_r_561_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(
    mut v_as_562_: *mut crate::leanh::LeanObject,
    mut v_i_563_: usize,
    mut v_stop_564_: usize,
    mut v_b_565_: u64,
) -> u64 {
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u64 = 0;
    let mut v___x_569_: u64 = 0;
    let mut v___x_570_: usize = 0;
    let mut v___x_571_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = lean_usize_dec_eq(v_i_563_, v_stop_564_);
                if v___x_566_ == 0 {
                    v___x_567_ = lean_array_uget_borrowed(v_as_562_, v_i_563_);
                    v___x_568_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v___x_567_);
                    v___x_569_ = lean_uint64_mix_hash(v_b_565_, v___x_568_);
                    v___x_570_ = 1usize;
                    v___x_571_ = lean_usize_add(v_i_563_, v___x_570_);
                    v_i_563_ = v___x_571_;
                    v_b_565_ = v___x_569_;
                    state = 0;
                    continue;
                } else {
                    return v_b_565_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(
    mut v_as_573_: *mut crate::leanh::LeanObject,
    mut v_i_574_: *mut crate::leanh::LeanObject,
    mut v_stop_575_: *mut crate::leanh::LeanObject,
    mut v_b_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_577_: usize = 0;
    let mut v_stop_boxed_578_: usize = 0;
    let mut v_b_boxed_579_: u64 = 0;
    let mut v_res_580_: u64 = 0;
    let mut v_r_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_577_ = crate::leanh::lean_unbox_usize(v_i_574_);
    crate::leanh::lean_dec(v_i_574_);
    v_stop_boxed_578_ = crate::leanh::lean_unbox_usize(v_stop_575_);
    crate::leanh::lean_dec(v_stop_575_);
    v_b_boxed_579_ = crate::leanh::lean_unbox_uint64(v_b_576_);
    crate::leanh::lean_dec_ref(v_b_576_);
    v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_573_, v_i_boxed_577_, v_stop_boxed_578_, v_b_boxed_579_);
    crate::leanh::lean_dec_ref(v_as_573_);
    v_r_581_ = crate::leanh::lean_box_uint64(v_res_580_);
    return v_r_581_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashAlts(
    mut v_pu_582_: u8,
    mut v_alts_583_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_584_: u64 = 0;
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    v___x_584_ = 7u64;
    v___x_585_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_586_ = lean_array_get_size(v_alts_583_);
    v___x_587_ = lean_nat_dec_lt(v___x_585_, v___x_586_);
    if v___x_587_ == 0 {
        return v___x_584_;
    } else {
        let mut v___x_588_: u8 = 0;
        v___x_588_ = lean_nat_dec_le(v___x_586_, v___x_586_);
        if v___x_588_ == 0 {
            if v___x_587_ == 0 {
                return v___x_584_;
            } else {
                let mut v___x_589_: usize = 0;
                let mut v___x_590_: usize = 0;
                let mut v___x_591_: u64 = 0;
                v___x_589_ = 0usize;
                v___x_590_ = lean_usize_of_nat(v___x_586_);
                v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_582_, v_alts_583_, v___x_589_, v___x_590_, v___x_584_);
                return v___x_591_;
            }
        } else {
            let mut v___x_592_: usize = 0;
            let mut v___x_593_: usize = 0;
            let mut v___x_594_: u64 = 0;
            v___x_592_ = 0usize;
            v___x_593_ = lean_usize_of_nat(v___x_586_);
            v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_582_, v_alts_583_, v___x_592_, v___x_593_, v___x_584_);
            return v___x_594_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_hashCode(
    mut v_pu_595_: u8,
    mut v_code_596_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_decl_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u64 = 0;
    let mut v___x_603_: u64 = 0;
    let mut v___x_604_: u64 = 0;
    let mut v___x_605_: u64 = 0;
    let mut v___x_606_: u64 = 0;
    let mut v___x_607_: u64 = 0;
    let mut v___x_608_: u64 = 0;
    let mut v_fvarId_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: u64 = 0;
    let mut v___x_612_: u64 = 0;
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: u64 = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: u64 = 0;
    let mut v___x_619_: usize = 0;
    let mut v___x_620_: usize = 0;
    let mut v___x_621_: u64 = 0;
    let mut v___x_622_: u64 = 0;
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: usize = 0;
    let mut v___x_625_: u64 = 0;
    let mut v___x_626_: u64 = 0;
    let mut v_cases_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u64 = 0;
    let mut v___x_632_: u64 = 0;
    let mut v___x_633_: u64 = 0;
    let mut v___x_634_: u64 = 0;
    let mut v___x_635_: u64 = 0;
    let mut v_fvarId_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u64 = 0;
    let mut v_type_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u64 = 0;
    let mut v_fvarId_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u64 = 0;
    let mut v___x_645_: u64 = 0;
    let mut v___x_646_: u64 = 0;
    let mut v___x_647_: u64 = 0;
    let mut v___x_648_: u64 = 0;
    let mut v___x_649_: u64 = 0;
    let mut v___x_650_: u64 = 0;
    let mut v_fvarId_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u64 = 0;
    let mut v___x_656_: u64 = 0;
    let mut v___x_657_: u64 = 0;
    let mut v___x_658_: u64 = 0;
    let mut v___x_659_: u64 = 0;
    let mut v___x_660_: u64 = 0;
    let mut v___x_661_: u64 = 0;
    let mut v_fvarId_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: u64 = 0;
    let mut v___x_669_: u64 = 0;
    let mut v___x_670_: u64 = 0;
    let mut v___x_671_: u64 = 0;
    let mut v___x_672_: u64 = 0;
    let mut v___x_673_: u64 = 0;
    let mut v___x_674_: u64 = 0;
    let mut v___x_675_: u64 = 0;
    let mut v___x_676_: u64 = 0;
    let mut v___x_677_: u64 = 0;
    let mut v___x_678_: u64 = 0;
    let mut v_fvarId_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u64 = 0;
    let mut v___x_683_: u64 = 0;
    let mut v___x_684_: u64 = 0;
    let mut v___x_685_: u64 = 0;
    let mut v___x_686_: u64 = 0;
    let mut v_fvarId_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_689_: u8 = 0;
    let mut v_persistent_690_: u8 = 0;
    let mut v_k_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: u64 = 0;
    let mut v___x_693_: u64 = 0;
    let mut v___x_694_: u64 = 0;
    let mut v___y_696_: u64 = 0;
    let mut v___y_697_: u64 = 0;
    let mut v___x_698_: u64 = 0;
    let mut v___x_699_: u64 = 0;
    let mut v___x_700_: u64 = 0;
    let mut v___x_701_: u64 = 0;
    let mut v___y_703_: u64 = 0;
    let mut v___x_704_: u64 = 0;
    let mut v___x_705_: u64 = 0;
    let mut v___x_706_: u64 = 0;
    let mut v___x_707_: u64 = 0;
    let mut v_fvarId_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_710_: u8 = 0;
    let mut v_persistent_711_: u8 = 0;
    let mut v_objs_x3f_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u64 = 0;
    let mut v___x_715_: u64 = 0;
    let mut v___x_716_: u64 = 0;
    let mut v___y_718_: u64 = 0;
    let mut v___y_719_: u64 = 0;
    let mut v___x_720_: u64 = 0;
    let mut v___x_721_: u64 = 0;
    let mut v___x_722_: u64 = 0;
    let mut v___x_723_: u64 = 0;
    let mut v___y_725_: u64 = 0;
    let mut v___y_726_: u64 = 0;
    let mut v___x_727_: u64 = 0;
    let mut v___x_728_: u64 = 0;
    let mut v_val_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u64 = 0;
    let mut v___x_731_: u64 = 0;
    let mut v___x_732_: u64 = 0;
    let mut v___y_734_: u64 = 0;
    let mut v___x_735_: u64 = 0;
    let mut v___x_736_: u64 = 0;
    let mut v___x_737_: u64 = 0;
    let mut v___x_738_: u64 = 0;
    let mut v_fvarId_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: u64 = 0;
    let mut v___x_742_: u64 = 0;
    let mut v___x_743_: u64 = 0;
    let mut v_decl_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u64 = 0;
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: u64 = 0;
    let mut v___x_753_: u64 = 0;
    let mut v___x_754_: u64 = 0;
    let mut v___x_755_: u64 = 0;
    let mut v___x_756_: u64 = 0;
    let mut v___x_757_: u64 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: u8 = 0;
    let mut v___x_761_: u64 = 0;
    let mut v___x_762_: u8 = 0;
    let mut v___x_763_: u64 = 0;
    let mut v___x_764_: usize = 0;
    let mut v___x_765_: usize = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut v___x_770_: u64 = 0;
    let mut v___x_771_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_596_) {
                0 => {
                    v_decl_597_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_k_598_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_fvarId_599_ = crate::leanh::lean_ctor_get(v_decl_597_, 0);
                    v_type_600_ = crate::leanh::lean_ctor_get(v_decl_597_, 2);
                    v_value_601_ = crate::leanh::lean_ctor_get(v_decl_597_, 3);
                    v___x_602_ = l_Lean_instHashableFVarId_hash(v_fvarId_599_);
                    v___x_603_ = l_Lean_Expr_hash(v_type_600_);
                    v___x_604_ = lean_uint64_mix_hash(v___x_602_, v___x_603_);
                    v___x_605_ =
                        l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_595_, v_value_601_);
                    v___x_606_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_598_);
                    v___x_607_ = lean_uint64_mix_hash(v___x_605_, v___x_606_);
                    v___x_608_ = lean_uint64_mix_hash(v___x_604_, v___x_607_);
                    return v___x_608_;
                }
                3 => {
                    v_fvarId_609_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_args_610_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v___x_611_ = l_Lean_instHashableFVarId_hash(v_fvarId_609_);
                    v___x_612_ = 7u64;
                    v___x_613_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_614_ = lean_array_get_size(v_args_610_);
                    v___x_615_ = lean_nat_dec_lt(v___x_613_, v___x_614_);
                    if v___x_615_ == 0 {
                        v___x_616_ = lean_uint64_mix_hash(v___x_611_, v___x_612_);
                        return v___x_616_;
                    } else {
                        v___x_617_ = lean_nat_dec_le(v___x_614_, v___x_614_);
                        if v___x_617_ == 0 {
                            if v___x_615_ == 0 {
                                v___x_618_ = lean_uint64_mix_hash(v___x_611_, v___x_612_);
                                return v___x_618_;
                            } else {
                                v___x_619_ = 0usize;
                                v___x_620_ = lean_usize_of_nat(v___x_614_);
                                v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_610_, v___x_619_, v___x_620_, v___x_612_);
                                v___x_622_ = lean_uint64_mix_hash(v___x_611_, v___x_621_);
                                return v___x_622_;
                            }
                        } else {
                            v___x_623_ = 0usize;
                            v___x_624_ = lean_usize_of_nat(v___x_614_);
                            v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_610_, v___x_623_, v___x_624_, v___x_612_);
                            v___x_626_ = lean_uint64_mix_hash(v___x_611_, v___x_625_);
                            return v___x_626_;
                        }
                    }
                }
                4 => {
                    v_cases_627_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_resultType_628_ = crate::leanh::lean_ctor_get(v_cases_627_, 1);
                    v_discr_629_ = crate::leanh::lean_ctor_get(v_cases_627_, 2);
                    v_alts_630_ = crate::leanh::lean_ctor_get(v_cases_627_, 3);
                    v___x_631_ = l_Lean_instHashableFVarId_hash(v_discr_629_);
                    v___x_632_ = l_Lean_Expr_hash(v_resultType_628_);
                    v___x_633_ = lean_uint64_mix_hash(v___x_631_, v___x_632_);
                    v___x_634_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_595_, v_alts_630_);
                    v___x_635_ = lean_uint64_mix_hash(v___x_633_, v___x_634_);
                    return v___x_635_;
                }
                5 => {
                    v_fvarId_636_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v___x_637_ = l_Lean_instHashableFVarId_hash(v_fvarId_636_);
                    return v___x_637_;
                }
                6 => {
                    v_type_638_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v___x_639_ = l_Lean_Expr_hash(v_type_638_);
                    return v___x_639_;
                }
                7 => {
                    v_fvarId_640_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_i_641_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_y_642_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v_k_643_ = crate::leanh::lean_ctor_get(v_code_596_, 3);
                    v___x_644_ = l_Lean_instHashableFVarId_hash(v_fvarId_640_);
                    v___x_645_ = lean_uint64_of_nat(v_i_641_);
                    v___x_646_ = lean_uint64_mix_hash(v___x_644_, v___x_645_);
                    v___x_647_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_642_);
                    v___x_648_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_643_);
                    v___x_649_ = lean_uint64_mix_hash(v___x_647_, v___x_648_);
                    v___x_650_ = lean_uint64_mix_hash(v___x_646_, v___x_649_);
                    return v___x_650_;
                }
                8 => {
                    v_fvarId_651_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_i_652_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_y_653_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v_k_654_ = crate::leanh::lean_ctor_get(v_code_596_, 3);
                    v___x_655_ = l_Lean_instHashableFVarId_hash(v_fvarId_651_);
                    v___x_656_ = lean_uint64_of_nat(v_i_652_);
                    v___x_657_ = lean_uint64_mix_hash(v___x_655_, v___x_656_);
                    v___x_658_ = l_Lean_instHashableFVarId_hash(v_y_653_);
                    v___x_659_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_654_);
                    v___x_660_ = lean_uint64_mix_hash(v___x_658_, v___x_659_);
                    v___x_661_ = lean_uint64_mix_hash(v___x_657_, v___x_660_);
                    return v___x_661_;
                }
                9 => {
                    v_fvarId_662_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_i_663_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_offset_664_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v_y_665_ = crate::leanh::lean_ctor_get(v_code_596_, 3);
                    v_ty_666_ = crate::leanh::lean_ctor_get(v_code_596_, 4);
                    v_k_667_ = crate::leanh::lean_ctor_get(v_code_596_, 5);
                    v___x_668_ = l_Lean_instHashableFVarId_hash(v_fvarId_662_);
                    v___x_669_ = lean_uint64_of_nat(v_i_663_);
                    v___x_670_ = lean_uint64_mix_hash(v___x_668_, v___x_669_);
                    v___x_671_ = lean_uint64_of_nat(v_offset_664_);
                    v___x_672_ = l_Lean_instHashableFVarId_hash(v_y_665_);
                    v___x_673_ = lean_uint64_mix_hash(v___x_671_, v___x_672_);
                    v___x_674_ = l_Lean_Expr_hash(v_ty_666_);
                    v___x_675_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_667_);
                    v___x_676_ = lean_uint64_mix_hash(v___x_674_, v___x_675_);
                    v___x_677_ = lean_uint64_mix_hash(v___x_673_, v___x_676_);
                    v___x_678_ = lean_uint64_mix_hash(v___x_670_, v___x_677_);
                    return v___x_678_;
                }
                10 => {
                    v_fvarId_679_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_cidx_680_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_k_681_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v___x_682_ = l_Lean_instHashableFVarId_hash(v_fvarId_679_);
                    v___x_683_ = lean_uint64_of_nat(v_cidx_680_);
                    v___x_684_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_681_);
                    v___x_685_ = lean_uint64_mix_hash(v___x_683_, v___x_684_);
                    v___x_686_ = lean_uint64_mix_hash(v___x_682_, v___x_685_);
                    return v___x_686_;
                }
                11 => {
                    v_fvarId_687_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_n_688_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_check_689_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_690_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_691_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v___x_692_ = l_Lean_instHashableFVarId_hash(v_fvarId_687_);
                    v___x_693_ = lean_uint64_of_nat(v_n_688_);
                    v___x_694_ = lean_uint64_mix_hash(v___x_692_, v___x_693_);
                    if v_persistent_690_ == 0 {
                        v___x_706_ = 13u64;
                        v___y_703_ = v___x_706_;
                        state = 2;
                        continue;
                    } else {
                        v___x_707_ = 11u64;
                        v___y_703_ = v___x_707_;
                        state = 2;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_708_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_n_709_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_check_710_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_711_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_712_ = crate::leanh::lean_ctor_get(v_code_596_, 2);
                    v_k_713_ = crate::leanh::lean_ctor_get(v_code_596_, 3);
                    v___x_714_ = l_Lean_instHashableFVarId_hash(v_fvarId_708_);
                    v___x_715_ = lean_uint64_of_nat(v_n_709_);
                    v___x_716_ = lean_uint64_mix_hash(v___x_714_, v___x_715_);
                    if v_persistent_711_ == 0 {
                        v___x_737_ = 13u64;
                        v___y_734_ = v___x_737_;
                        state = 5;
                        continue;
                    } else {
                        v___x_738_ = 11u64;
                        v___y_734_ = v___x_738_;
                        state = 5;
                        continue;
                    }
                }
                13 => {
                    v_fvarId_739_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_k_740_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v___x_741_ = l_Lean_instHashableFVarId_hash(v_fvarId_739_);
                    v___x_742_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_740_);
                    v___x_743_ = lean_uint64_mix_hash(v___x_741_, v___x_742_);
                    return v___x_743_;
                }
                _ => {
                    v_decl_744_ = crate::leanh::lean_ctor_get(v_code_596_, 0);
                    v_k_745_ = crate::leanh::lean_ctor_get(v_code_596_, 1);
                    v_fvarId_746_ = crate::leanh::lean_ctor_get(v_decl_744_, 0);
                    v_params_747_ = crate::leanh::lean_ctor_get(v_decl_744_, 2);
                    v_type_748_ = crate::leanh::lean_ctor_get(v_decl_744_, 3);
                    v_value_749_ = crate::leanh::lean_ctor_get(v_decl_744_, 4);
                    v___x_750_ = l_Lean_instHashableFVarId_hash(v_fvarId_746_);
                    v___x_751_ = l_Lean_Expr_hash(v_type_748_);
                    v___x_752_ = lean_uint64_mix_hash(v___x_750_, v___x_751_);
                    v___x_753_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_value_749_);
                    v___x_754_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_745_);
                    v___x_755_ = lean_uint64_mix_hash(v___x_753_, v___x_754_);
                    v___x_756_ = lean_uint64_mix_hash(v___x_752_, v___x_755_);
                    v___x_757_ = 7u64;
                    v___x_758_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_759_ = lean_array_get_size(v_params_747_);
                    v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
                    if v___x_760_ == 0 {
                        v___x_761_ = lean_uint64_mix_hash(v___x_756_, v___x_757_);
                        return v___x_761_;
                    } else {
                        v___x_762_ = lean_nat_dec_le(v___x_759_, v___x_759_);
                        if v___x_762_ == 0 {
                            if v___x_760_ == 0 {
                                v___x_763_ = lean_uint64_mix_hash(v___x_756_, v___x_757_);
                                return v___x_763_;
                            } else {
                                v___x_764_ = 0usize;
                                v___x_765_ = lean_usize_of_nat(v___x_759_);
                                v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_747_, v___x_764_, v___x_765_, v___x_757_);
                                v___x_767_ = lean_uint64_mix_hash(v___x_756_, v___x_766_);
                                return v___x_767_;
                            }
                        } else {
                            v___x_768_ = 0usize;
                            v___x_769_ = lean_usize_of_nat(v___x_759_);
                            v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_747_, v___x_768_, v___x_769_, v___x_757_);
                            v___x_771_ = lean_uint64_mix_hash(v___x_756_, v___x_770_);
                            return v___x_771_;
                        }
                    }
                }
            },
            1 => {
                v___x_698_ = lean_uint64_mix_hash(v___y_696_, v___y_697_);
                v___x_699_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_691_);
                v___x_700_ = lean_uint64_mix_hash(v___x_698_, v___x_699_);
                v___x_701_ = lean_uint64_mix_hash(v___x_694_, v___x_700_);
                return v___x_701_;
            }
            2 => {
                if v_check_689_ == 0 {
                    v___x_704_ = 13u64;
                    v___y_696_ = v___y_703_;
                    v___y_697_ = v___x_704_;
                    state = 1;
                    continue;
                } else {
                    v___x_705_ = 11u64;
                    v___y_696_ = v___y_703_;
                    v___y_697_ = v___x_705_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_720_ = l_Lean_Compiler_LCNF_hashCode(v_pu_595_, v_k_713_);
                v___x_721_ = lean_uint64_mix_hash(v___y_719_, v___x_720_);
                v___x_722_ = lean_uint64_mix_hash(v___y_718_, v___x_721_);
                v___x_723_ = lean_uint64_mix_hash(v___x_716_, v___x_722_);
                return v___x_723_;
            }
            4 => {
                v___x_727_ = lean_uint64_mix_hash(v___y_725_, v___y_726_);
                if crate::leanh::lean_obj_tag(v_objs_x3f_712_) == 0 {
                    v___x_728_ = 11u64;
                    v___y_718_ = v___x_727_;
                    v___y_719_ = v___x_728_;
                    state = 3;
                    continue;
                } else {
                    v_val_729_ = crate::leanh::lean_ctor_get(v_objs_x3f_712_, 0);
                    v___x_730_ = lean_uint64_of_nat(v_val_729_);
                    v___x_731_ = 13u64;
                    v___x_732_ = lean_uint64_mix_hash(v___x_730_, v___x_731_);
                    v___y_718_ = v___x_727_;
                    v___y_719_ = v___x_732_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v_check_710_ == 0 {
                    v___x_735_ = 13u64;
                    v___y_725_ = v___y_734_;
                    v___y_726_ = v___x_735_;
                    state = 4;
                    continue;
                } else {
                    v___x_736_ = 11u64;
                    v___y_725_ = v___y_734_;
                    v___y_726_ = v___x_736_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_hashAlt___closed__0() -> u64 {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u64 = 0;
    v___x_772_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_773_ = lean_uint64_of_nat(v___x_772_);
    return v___x_773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashAlt(
    mut v_pu_774_: u8,
    mut v_alt_775_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_ctorName_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_780_: u64 = 0;
    let mut v___y_781_: u64 = 0;
    let mut v___x_782_: u64 = 0;
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: u64 = 0;
    let mut v___y_786_: u64 = 0;
    let mut v___x_787_: u64 = 0;
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: usize = 0;
    let mut v___x_793_: usize = 0;
    let mut v___x_794_: u64 = 0;
    let mut v___x_795_: usize = 0;
    let mut v___x_796_: usize = 0;
    let mut v___x_797_: u64 = 0;
    let mut v___x_798_: u64 = 0;
    let mut v_hash_799_: u64 = 0;
    let mut v_info_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u64 = 0;
    let mut v___x_803_: u64 = 0;
    let mut v___x_804_: u64 = 0;
    let mut v_code_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_775_) {
                0 => {
                    v_ctorName_776_ = crate::leanh::lean_ctor_get(v_alt_775_, 0);
                    v_params_777_ = crate::leanh::lean_ctor_get(v_alt_775_, 1);
                    v_code_778_ = crate::leanh::lean_ctor_get(v_alt_775_, 2);
                    if crate::leanh::lean_obj_tag(v_ctorName_776_) == 0 {
                        v___x_798_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0_once),
                            _init_l_Lean_Compiler_LCNF_hashAlt___closed__0,
                        );
                        v___y_786_ = v___x_798_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_799_ = crate::leanh::lean_ctor_get_uint64(
                            v_ctorName_776_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_786_ = v_hash_799_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_info_800_ = crate::leanh::lean_ctor_get(v_alt_775_, 0);
                    v_code_801_ = crate::leanh::lean_ctor_get(v_alt_775_, 1);
                    v___x_802_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_800_);
                    v___x_803_ = l_Lean_Compiler_LCNF_hashCode(v_pu_774_, v_code_801_);
                    v___x_804_ = lean_uint64_mix_hash(v___x_802_, v___x_803_);
                    return v___x_804_;
                }
                _ => {
                    v_code_805_ = crate::leanh::lean_ctor_get(v_alt_775_, 0);
                    v___x_806_ = l_Lean_Compiler_LCNF_hashCode(v_pu_774_, v_code_805_);
                    return v___x_806_;
                }
            },
            1 => {
                v___x_782_ = lean_uint64_mix_hash(v___y_780_, v___y_781_);
                v___x_783_ = l_Lean_Compiler_LCNF_hashCode(v_pu_774_, v_code_778_);
                v___x_784_ = lean_uint64_mix_hash(v___x_782_, v___x_783_);
                return v___x_784_;
            }
            2 => {
                v___x_787_ = 7u64;
                v___x_788_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_789_ = lean_array_get_size(v_params_777_);
                v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
                if v___x_790_ == 0 {
                    v___y_780_ = v___y_786_;
                    v___y_781_ = v___x_787_;
                    state = 1;
                    continue;
                } else {
                    v___x_791_ = lean_nat_dec_le(v___x_789_, v___x_789_);
                    if v___x_791_ == 0 {
                        if v___x_790_ == 0 {
                            v___y_780_ = v___y_786_;
                            v___y_781_ = v___x_787_;
                            state = 1;
                            continue;
                        } else {
                            v___x_792_ = 0usize;
                            v___x_793_ = lean_usize_of_nat(v___x_789_);
                            v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_777_, v___x_792_, v___x_793_, v___x_787_);
                            v___y_780_ = v___y_786_;
                            v___y_781_ = v___x_794_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_795_ = 0usize;
                        v___x_796_ = lean_usize_of_nat(v___x_789_);
                        v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_777_, v___x_795_, v___x_796_, v___x_787_);
                        v___y_780_ = v___y_786_;
                        v___y_781_ = v___x_797_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(
    mut v_pu_807_: u8,
    mut v_as_808_: *mut crate::leanh::LeanObject,
    mut v_i_809_: usize,
    mut v_stop_810_: usize,
    mut v_b_811_: u64,
) -> u64 {
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u64 = 0;
    let mut v___x_815_: u64 = 0;
    let mut v___x_816_: usize = 0;
    let mut v___x_817_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_812_ = lean_usize_dec_eq(v_i_809_, v_stop_810_);
                if v___x_812_ == 0 {
                    v___x_813_ = lean_array_uget_borrowed(v_as_808_, v_i_809_);
                    v___x_814_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_807_, v___x_813_);
                    v___x_815_ = lean_uint64_mix_hash(v_b_811_, v___x_814_);
                    v___x_816_ = 1usize;
                    v___x_817_ = lean_usize_add(v_i_809_, v___x_816_);
                    v_i_809_ = v___x_817_;
                    v_b_811_ = v___x_815_;
                    state = 0;
                    continue;
                } else {
                    return v_b_811_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(
    mut v_pu_819_: *mut crate::leanh::LeanObject,
    mut v_as_820_: *mut crate::leanh::LeanObject,
    mut v_i_821_: *mut crate::leanh::LeanObject,
    mut v_stop_822_: *mut crate::leanh::LeanObject,
    mut v_b_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_824_: u8 = 0;
    let mut v_i_boxed_825_: usize = 0;
    let mut v_stop_boxed_826_: usize = 0;
    let mut v_b_boxed_827_: u64 = 0;
    let mut v_res_828_: u64 = 0;
    let mut v_r_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_824_ = (crate::leanh::lean_unbox(v_pu_819_) as u8);
    v_i_boxed_825_ = crate::leanh::lean_unbox_usize(v_i_821_);
    crate::leanh::lean_dec(v_i_821_);
    v_stop_boxed_826_ = crate::leanh::lean_unbox_usize(v_stop_822_);
    crate::leanh::lean_dec(v_stop_822_);
    v_b_boxed_827_ = crate::leanh::lean_unbox_uint64(v_b_823_);
    crate::leanh::lean_dec_ref(v_b_823_);
    v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_824_, v_as_820_, v_i_boxed_825_, v_stop_boxed_826_, v_b_boxed_827_);
    crate::leanh::lean_dec_ref(v_as_820_);
    v_r_829_ = crate::leanh::lean_box_uint64(v_res_828_);
    return v_r_829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashAlts___boxed(
    mut v_pu_830_: *mut crate::leanh::LeanObject,
    mut v_alts_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_832_: u8 = 0;
    let mut v_res_833_: u64 = 0;
    let mut v_r_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_832_ = (crate::leanh::lean_unbox(v_pu_830_) as u8);
    v_res_833_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_832_, v_alts_831_);
    crate::leanh::lean_dec_ref(v_alts_831_);
    v_r_834_ = crate::leanh::lean_box_uint64(v_res_833_);
    return v_r_834_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashAlt___boxed(
    mut v_pu_835_: *mut crate::leanh::LeanObject,
    mut v_alt_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_837_: u8 = 0;
    let mut v_res_838_: u64 = 0;
    let mut v_r_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_837_ = (crate::leanh::lean_unbox(v_pu_835_) as u8);
    v_res_838_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_837_, v_alt_836_);
    crate::leanh::lean_dec_ref(v_alt_836_);
    v_r_839_ = crate::leanh::lean_box_uint64(v_res_838_);
    return v_r_839_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hashCode___boxed(
    mut v_pu_840_: *mut crate::leanh::LeanObject,
    mut v_code_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_842_: u8 = 0;
    let mut v_res_843_: u64 = 0;
    let mut v_r_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_842_ = (crate::leanh::lean_unbox(v_pu_840_) as u8);
    v_res_843_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_842_, v_code_841_);
    crate::leanh::lean_dec_ref(v_code_841_);
    v_r_844_ = crate::leanh::lean_box_uint64(v_res_843_);
    return v_r_844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(
    mut v_pu_845_: u8,
    mut v_as_846_: *mut crate::leanh::LeanObject,
    mut v_i_847_: usize,
    mut v_stop_848_: usize,
    mut v_b_849_: u64,
) -> u64 {
    let mut v___x_850_: u64 = 0;
    v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_846_, v_i_847_, v_stop_848_, v_b_849_);
    return v___x_850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(
    mut v_pu_851_: *mut crate::leanh::LeanObject,
    mut v_as_852_: *mut crate::leanh::LeanObject,
    mut v_i_853_: *mut crate::leanh::LeanObject,
    mut v_stop_854_: *mut crate::leanh::LeanObject,
    mut v_b_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_856_: u8 = 0;
    let mut v_i_boxed_857_: usize = 0;
    let mut v_stop_boxed_858_: usize = 0;
    let mut v_b_boxed_859_: u64 = 0;
    let mut v_res_860_: u64 = 0;
    let mut v_r_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_856_ = (crate::leanh::lean_unbox(v_pu_851_) as u8);
    v_i_boxed_857_ = crate::leanh::lean_unbox_usize(v_i_853_);
    crate::leanh::lean_dec(v_i_853_);
    v_stop_boxed_858_ = crate::leanh::lean_unbox_usize(v_stop_854_);
    crate::leanh::lean_dec(v_stop_854_);
    v_b_boxed_859_ = crate::leanh::lean_unbox_uint64(v_b_855_);
    crate::leanh::lean_dec_ref(v_b_855_);
    v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_856_, v_as_852_, v_i_boxed_857_, v_stop_boxed_858_, v_b_boxed_859_);
    crate::leanh::lean_dec_ref(v_as_852_);
    v_r_861_ = crate::leanh::lean_box_uint64(v_res_860_);
    return v_r_861_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableCode___lam__0(
    mut v_pu_862_: u8,
    mut v_c_863_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_864_: u64 = 0;
    v___x_864_ = l_Lean_Compiler_LCNF_hashCode(v_pu_862_, v_c_863_);
    return v___x_864_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(
    mut v_pu_865_: *mut crate::leanh::LeanObject,
    mut v_c_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_867_: u8 = 0;
    let mut v_res_868_: u64 = 0;
    let mut v_r_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_867_ = (crate::leanh::lean_unbox(v_pu_865_) as u8);
    v_res_868_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_867_, v_c_866_);
    crate::leanh::lean_dec_ref(v_c_866_);
    v_r_869_ = crate::leanh::lean_box_uint64(v_res_868_);
    return v_r_869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableCode(
    mut v_pu_870_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = crate::leanh::lean_box((v_pu_870_) as usize);
    v___f_872_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_872_, 0, v___x_871_);
    return v___f_872_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableCode___boxed(
    mut v_pu_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_874_: u8 = 0;
    let mut v_res_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_874_ = (crate::leanh::lean_unbox(v_pu_873_) as u8);
    v_res_875_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_874_);
    return v_res_875_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDeclValue_hash(
    mut v_pu_876_: u8,
    mut v_x_877_: *mut crate::leanh::LeanObject,
) -> u64 {
    if crate::leanh::lean_obj_tag(v_x_877_) == 0 {
        let mut v_code_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_879_: u64 = 0;
        let mut v___x_880_: u64 = 0;
        let mut v___x_881_: u64 = 0;
        v_code_878_ = crate::leanh::lean_ctor_get(v_x_877_, 0);
        v___x_879_ = 0u64;
        v___x_880_ = l_Lean_Compiler_LCNF_hashCode(v_pu_876_, v_code_878_);
        v___x_881_ = lean_uint64_mix_hash(v___x_879_, v___x_880_);
        return v___x_881_;
    } else {
        let mut v_externAttrData_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: u64 = 0;
        let mut v___x_884_: u64 = 0;
        let mut v___x_885_: u64 = 0;
        v_externAttrData_882_ = crate::leanh::lean_ctor_get(v_x_877_, 0);
        v___x_883_ = 1u64;
        v___x_884_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_882_);
        v___x_885_ = lean_uint64_mix_hash(v___x_883_, v___x_884_);
        return v___x_885_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(
    mut v_pu_886_: *mut crate::leanh::LeanObject,
    mut v_x_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_47__boxed_888_: u8 = 0;
    let mut v_res_889_: u64 = 0;
    let mut v_r_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_47__boxed_888_ = (crate::leanh::lean_unbox(v_pu_886_) as u8);
    v_res_889_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_888_, v_x_887_);
    crate::leanh::lean_dec_ref(v_x_887_);
    v_r_890_ = crate::leanh::lean_box_uint64(v_res_889_);
    return v_r_890_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDeclValue(
    mut v_pu_891_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = crate::leanh::lean_box((v_pu_891_) as usize);
    v___x_893_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_893_, 0, v___x_892_);
    return v___x_893_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(
    mut v_pu_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_5__boxed_895_: u8 = 0;
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_5__boxed_895_ = (crate::leanh::lean_unbox(v_pu_894_) as u8);
    v_res_896_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_895_);
    return v_res_896_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(
    mut v_x_897_: u64,
    mut v_x_898_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_head_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_902_: u64 = 0;
    let mut v___x_903_: u64 = 0;
    let mut v___x_905_: u64 = 0;
    let mut v_hash_906_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_898_) == 0 {
                    return v_x_897_;
                } else {
                    v_head_899_ = crate::leanh::lean_ctor_get(v_x_898_, 0);
                    v_tail_900_ = crate::leanh::lean_ctor_get(v_x_898_, 1);
                    if crate::leanh::lean_obj_tag(v_head_899_) == 0 {
                        v___x_905_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0_once),
                            _init_l_Lean_Compiler_LCNF_hashAlt___closed__0,
                        );
                        v___y_902_ = v___x_905_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_906_ = crate::leanh::lean_ctor_get_uint64(
                            v_head_899_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_902_ = v_hash_906_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_903_ = lean_uint64_mix_hash(v_x_897_, v___y_902_);
                v_x_897_ = v___x_903_;
                v_x_898_ = v_tail_900_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(
    mut v_x_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_205__boxed_909_: u64 = 0;
    let mut v_res_910_: u64 = 0;
    let mut v_r_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_205__boxed_909_ = crate::leanh::lean_unbox_uint64(v_x_907_);
    crate::leanh::lean_dec_ref(v_x_907_);
    v_res_910_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(
        v_x_205__boxed_909_,
        v_x_908_,
    );
    crate::leanh::lean_dec(v_x_908_);
    v_r_911_ = crate::leanh::lean_box_uint64(v_res_910_);
    return v_r_911_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(
    mut v_x_912_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_name_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_917_: u8 = 0;
    let mut v___y_919_: u64 = 0;
    let mut v___y_920_: u64 = 0;
    let mut v___x_921_: u64 = 0;
    let mut v___x_922_: u64 = 0;
    let mut v___x_923_: u64 = 0;
    let mut v___x_924_: u64 = 0;
    let mut v___x_925_: u64 = 0;
    let mut v___x_926_: u64 = 0;
    let mut v___y_928_: u64 = 0;
    let mut v___x_929_: u64 = 0;
    let mut v___x_930_: u64 = 0;
    let mut v___x_931_: u64 = 0;
    let mut v___x_932_: u64 = 0;
    let mut v___x_933_: u64 = 0;
    let mut v___x_934_: u64 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: u8 = 0;
    let mut v___x_938_: u8 = 0;
    let mut v___x_939_: usize = 0;
    let mut v___x_940_: usize = 0;
    let mut v___x_941_: u64 = 0;
    let mut v___x_942_: usize = 0;
    let mut v___x_943_: usize = 0;
    let mut v___x_944_: u64 = 0;
    let mut v___x_945_: u64 = 0;
    let mut v_hash_946_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_913_ = crate::leanh::lean_ctor_get(v_x_912_, 0);
                v_levelParams_914_ = crate::leanh::lean_ctor_get(v_x_912_, 1);
                v_type_915_ = crate::leanh::lean_ctor_get(v_x_912_, 2);
                v_params_916_ = crate::leanh::lean_ctor_get(v_x_912_, 3);
                v_safe_917_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_912_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v___x_926_ = 0u64;
                if crate::leanh::lean_obj_tag(v_name_913_) == 0 {
                    v___x_945_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_hashAlt___closed__0_once),
                        _init_l_Lean_Compiler_LCNF_hashAlt___closed__0,
                    );
                    v___y_928_ = v___x_945_;
                    state = 2;
                    continue;
                } else {
                    v_hash_946_ = crate::leanh::lean_ctor_get_uint64(
                        v_name_913_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_928_ = v_hash_946_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_921_ = lean_uint64_mix_hash(v___y_919_, v___y_920_);
                if v_safe_917_ == 0 {
                    v___x_922_ = 13u64;
                    v___x_923_ = lean_uint64_mix_hash(v___x_921_, v___x_922_);
                    return v___x_923_;
                } else {
                    v___x_924_ = 11u64;
                    v___x_925_ = lean_uint64_mix_hash(v___x_921_, v___x_924_);
                    return v___x_925_;
                }
            }
            2 => {
                v___x_929_ = lean_uint64_mix_hash(v___x_926_, v___y_928_);
                v___x_930_ = 7u64;
                v___x_931_ =
                    l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(
                        v___x_930_,
                        v_levelParams_914_,
                    );
                v___x_932_ = lean_uint64_mix_hash(v___x_929_, v___x_931_);
                v___x_933_ = l_Lean_Expr_hash(v_type_915_);
                v___x_934_ = lean_uint64_mix_hash(v___x_932_, v___x_933_);
                v___x_935_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_936_ = lean_array_get_size(v_params_916_);
                v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
                if v___x_937_ == 0 {
                    v___y_919_ = v___x_934_;
                    v___y_920_ = v___x_930_;
                    state = 1;
                    continue;
                } else {
                    v___x_938_ = lean_nat_dec_le(v___x_936_, v___x_936_);
                    if v___x_938_ == 0 {
                        if v___x_937_ == 0 {
                            v___y_919_ = v___x_934_;
                            v___y_920_ = v___x_930_;
                            state = 1;
                            continue;
                        } else {
                            v___x_939_ = 0usize;
                            v___x_940_ = lean_usize_of_nat(v___x_936_);
                            v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_916_, v___x_939_, v___x_940_, v___x_930_);
                            v___y_919_ = v___x_934_;
                            v___y_920_ = v___x_941_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_942_ = 0usize;
                        v___x_943_ = lean_usize_of_nat(v___x_936_);
                        v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_916_, v___x_942_, v___x_943_, v___x_930_);
                        v___y_919_ = v___x_934_;
                        v___y_920_ = v___x_944_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(
    mut v_x_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: u64 = 0;
    let mut v_r_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_947_);
    crate::leanh::lean_dec_ref(v_x_947_);
    v_r_949_ = crate::leanh::lean_box_uint64(v_res_948_);
    return v_r_949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature_hash(
    mut v_pu_950_: u8,
    mut v_x_951_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_952_: u64 = 0;
    v___x_952_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_951_);
    return v___x_952_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(
    mut v_pu_953_: *mut crate::leanh::LeanObject,
    mut v_x_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_298__boxed_955_: u8 = 0;
    let mut v_res_956_: u64 = 0;
    let mut v_r_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_298__boxed_955_ = (crate::leanh::lean_unbox(v_pu_953_) as u8);
    v_res_956_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_298__boxed_955_, v_x_954_);
    crate::leanh::lean_dec_ref(v_x_954_);
    v_r_957_ = crate::leanh::lean_box_uint64(v_res_956_);
    return v_r_957_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature(
    mut v_pu_958_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_959_ = crate::leanh::lean_box((v_pu_958_) as usize);
    v___x_960_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_960_, 0, v___x_959_);
    return v___x_960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableSignature___boxed(
    mut v_pu_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_5__boxed_962_: u8 = 0;
    let mut v_res_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_5__boxed_962_ = (crate::leanh::lean_unbox(v_pu_961_) as u8);
    v_res_963_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_962_);
    return v_res_963_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDecl_hash(
    mut v_pu_964_: u8,
    mut v_x_965_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_toSignature_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_968_: u8 = 0;
    let mut v_inlineAttr_x3f_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: u64 = 0;
    let mut v___x_971_: u64 = 0;
    let mut v___x_972_: u64 = 0;
    let mut v___x_973_: u64 = 0;
    let mut v___x_974_: u64 = 0;
    let mut v___y_976_: u64 = 0;
    let mut v___x_977_: u64 = 0;
    let mut v___x_978_: u64 = 0;
    let mut v___x_979_: u64 = 0;
    let mut v_val_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: u64 = 0;
    let mut v___x_983_: u64 = 0;
    let mut v___x_984_: u64 = 0;
    let mut v___x_985_: u64 = 0;
    let mut v___x_986_: u64 = 0;
    let mut v___x_987_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_966_ = crate::leanh::lean_ctor_get(v_x_965_, 0);
                v_value_967_ = crate::leanh::lean_ctor_get(v_x_965_, 1);
                v_recursive_968_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_965_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_969_ = crate::leanh::lean_ctor_get(v_x_965_, 2);
                v___x_970_ = 0u64;
                v___x_971_ =
                    l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_966_);
                v___x_972_ = lean_uint64_mix_hash(v___x_970_, v___x_971_);
                v___x_973_ =
                    l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_964_, v_value_967_);
                v___x_974_ = lean_uint64_mix_hash(v___x_972_, v___x_973_);
                if v_recursive_968_ == 0 {
                    v___x_986_ = 13u64;
                    v___y_976_ = v___x_986_;
                    state = 1;
                    continue;
                } else {
                    v___x_987_ = 11u64;
                    v___y_976_ = v___x_987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_977_ = lean_uint64_mix_hash(v___x_974_, v___y_976_);
                if crate::leanh::lean_obj_tag(v_inlineAttr_x3f_969_) == 0 {
                    v___x_978_ = 11u64;
                    v___x_979_ = lean_uint64_mix_hash(v___x_977_, v___x_978_);
                    return v___x_979_;
                } else {
                    v_val_980_ = crate::leanh::lean_ctor_get(v_inlineAttr_x3f_969_, 0);
                    v___x_981_ = (crate::leanh::lean_unbox(v_val_980_) as u8);
                    v___x_982_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_981_);
                    v___x_983_ = 13u64;
                    v___x_984_ = lean_uint64_mix_hash(v___x_982_, v___x_983_);
                    v___x_985_ = lean_uint64_mix_hash(v___x_977_, v___x_984_);
                    return v___x_985_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(
    mut v_pu_988_: *mut crate::leanh::LeanObject,
    mut v_x_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_91__boxed_990_: u8 = 0;
    let mut v_res_991_: u64 = 0;
    let mut v_r_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_91__boxed_990_ = (crate::leanh::lean_unbox(v_pu_988_) as u8);
    v_res_991_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_91__boxed_990_, v_x_989_);
    crate::leanh::lean_dec_ref(v_x_989_);
    v_r_992_ = crate::leanh::lean_box_uint64(v_res_991_);
    return v_r_992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDecl(
    mut v_pu_993_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = crate::leanh::lean_box((v_pu_993_) as usize);
    v___x_995_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_995_, 0, v___x_994_);
    return v___x_995_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableDecl___boxed(
    mut v_pu_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_5__boxed_997_: u8 = 0;
    let mut v_res_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_5__boxed_997_ = (crate::leanh::lean_unbox(v_pu_996_) as u8);
    v_res_998_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_997_);
    return v_res_998_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_DeclHash(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_DeclHash(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_DeclHash(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DeclHash(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_DeclHash(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_DeclHash(builtin);
}
