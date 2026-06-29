// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Reverse Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop Init.Data.Nat.Linear Init.Omega
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Var::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::ShiftRight::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Append::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Replicate::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Extract::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::RotateLeft::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::RotateRight::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Mul::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Umod::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Reverse::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Clz::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Cpop::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop};
use crate::r#gen::Init::Data::Nat::Linear::{initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::l_Nat_testBit;
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{l_Std_Tactic_BVDecide_BVExpr_decEq___redArg, l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed, l_Std_Tactic_BVDecide_instHashableBVBit_hash};
use crate::r#gen::Std::Sat::AIG::Basic::{l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg, l_Std_Sat_AIG_instHashableFanin_hash};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Prelude::{l_BitVec_ofNat, l_instBEqOfDecidableEq___redArg___lam__0___boxed};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg, l_Std_DHashMap_Internal_Raw_u2080_insert___redArg};
use crate::r#gen::Init::Data::BitVec::BasicAux::l_BitVec_sub;
use crate::ffi::{lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_land, lean_nat_lor, lean_nat_mod, lean_nat_mul, lean_nat_pow, lean_nat_shiftr, lean_nat_sub, lean_uint64_mix_hash, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub};
pub static l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0_value:
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
    m_fun: l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_BVExpr_instHashableKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(
    mut v_x_4416_: *mut crate::leanh::LeanObject,
    mut v_x_4417_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_w_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    v_w_4418_ = crate::leanh::lean_ctor_get(v_x_4416_, 0);
    v_expr_4419_ = crate::leanh::lean_ctor_get(v_x_4416_, 1);
    v_w_4420_ = crate::leanh::lean_ctor_get(v_x_4417_, 0);
    v_expr_4421_ = crate::leanh::lean_ctor_get(v_x_4417_, 1);
    v___x_4422_ = lean_nat_dec_eq(v_w_4418_, v_w_4420_);
    if v___x_4422_ == 0 {
        return v___x_4422_;
    } else {
        let mut v___x_4423_: u8 = 0;
        v___x_4423_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_4419_, v_expr_4421_);
        return v___x_4423_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq___boxed(
    mut v_x_4424_: *mut crate::leanh::LeanObject,
    mut v_x_4425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4426_: u8 = 0;
    let mut v_r_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4426_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_x_4424_, v_x_4425_);
    crate::leanh::lean_dec_ref(v_x_4425_);
    crate::leanh::lean_dec_ref(v_x_4424_);
    v_r_4427_ = crate::leanh::lean_box((v_res_4426_) as usize);
    return v_r_4427_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey(
    mut v_x_4428_: *mut crate::leanh::LeanObject,
    mut v_x_4429_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4430_: u8 = 0;
    v___x_4430_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_x_4428_, v_x_4429_);
    return v___x_4430_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey___boxed(
    mut v_x_4431_: *mut crate::leanh::LeanObject,
    mut v_x_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4433_: u8 = 0;
    let mut v_r_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey(v_x_4431_, v_x_4432_);
    crate::leanh::lean_dec_ref(v_x_4432_);
    crate::leanh::lean_dec_ref(v_x_4431_);
    v_r_4434_ = crate::leanh::lean_box((v_res_4433_) as usize);
    return v_r_4434_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0(
    mut v_key_4435_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_expr_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expr_4436_ = crate::leanh::lean_ctor_get(v_key_4435_, 1);
    match crate::leanh::lean_obj_tag(v_expr_4436_) {
        0 => {
            let mut v_hashCode_4437_: u64 = 0;
            v_hashCode_4437_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_4437_;
        }
        1 => {
            let mut v_hashCode_4438_: u64 = 0;
            v_hashCode_4438_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_4438_;
        }
        3 => {
            let mut v_hashCode_4439_: u64 = 0;
            v_hashCode_4439_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_4439_;
        }
        4 => {
            let mut v_hashCode_4440_: u64 = 0;
            v_hashCode_4440_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_4440_;
        }
        5 => {
            let mut v_hashCode_4441_: u64 = 0;
            v_hashCode_4441_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
            );
            return v_hashCode_4441_;
        }
        _ => {
            let mut v_hashCode_4442_: u64 = 0;
            v_hashCode_4442_ = crate::leanh::lean_ctor_get_uint64(
                v_expr_4436_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            return v_hashCode_4442_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0___boxed(
    mut v_key_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4444_: u64 = 0;
    let mut v_r_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0(v_key_4443_);
    crate::leanh::lean_dec_ref(v_key_4443_);
    v_r_4445_ = crate::leanh::lean_box_uint64(v_res_4444_);
    return v_r_4445_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4448_ = crate::leanh::lean_box(0);
    v___x_4449_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4450_ = lean_mk_array(v___x_4449_, v___x_4448_);
    return v___x_4450_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0_once),
        _init_l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__0,
    );
    v___x_4452_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4453_, 0, v___x_4452_);
    crate::leanh::lean_ctor_set(v___x_4453_, 1, v___x_4451_);
    return v___x_4453_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_empty(
    mut v_aig_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1_once),
        _init_l_Std_Tactic_BVDecide_BVExpr_Cache_empty___closed__1,
    );
    return v___x_4455_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_empty___boxed(
    mut v_aig_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Std_Tactic_BVDecide_BVExpr_Cache_empty(v_aig_4456_);
    crate::leanh::lean_dec_ref(v_aig_4456_);
    return v_res_4457_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4458_ = crate::leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_4459_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4459_, 0, v___x_4458_);
    return v___f_4459_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg(
    mut v_w_4460_: *mut crate::leanh::LeanObject,
    mut v_cache_4461_: *mut crate::leanh::LeanObject,
    mut v_expr_4462_: *mut crate::leanh::LeanObject,
    mut v_refs_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4464_ = l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0;
    v___f_4465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0,
    );
    v___x_4466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4466_, 0, v_w_4460_);
    crate::leanh::lean_ctor_set(v___x_4466_, 1, v_expr_4462_);
    v___x_4467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_4465_,
        v___f_4464_,
        v_cache_4461_,
        v___x_4466_,
        v_refs_4463_,
    );
    return v___x_4467_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_insert(
    mut v_aig_4468_: *mut crate::leanh::LeanObject,
    mut v_w_4469_: *mut crate::leanh::LeanObject,
    mut v_cache_4470_: *mut crate::leanh::LeanObject,
    mut v_expr_4471_: *mut crate::leanh::LeanObject,
    mut v_refs_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4473_ = l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0;
    v___f_4474_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0,
    );
    v___x_4475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4475_, 0, v_w_4469_);
    crate::leanh::lean_ctor_set(v___x_4475_, 1, v_expr_4471_);
    v___x_4476_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_4474_,
        v___f_4473_,
        v_cache_4470_,
        v___x_4475_,
        v_refs_4472_,
    );
    return v___x_4476_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_insert___boxed(
    mut v_aig_4477_: *mut crate::leanh::LeanObject,
    mut v_w_4478_: *mut crate::leanh::LeanObject,
    mut v_cache_4479_: *mut crate::leanh::LeanObject,
    mut v_expr_4480_: *mut crate::leanh::LeanObject,
    mut v_refs_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Std_Tactic_BVDecide_BVExpr_Cache_insert(
        v_aig_4477_,
        v_w_4478_,
        v_cache_4479_,
        v_expr_4480_,
        v_refs_4481_,
    );
    crate::leanh::lean_dec_ref(v_aig_4477_);
    return v_res_4482_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f___redArg(
    mut v_w_4483_: *mut crate::leanh::LeanObject,
    mut v_cache_4484_: *mut crate::leanh::LeanObject,
    mut v_expr_4485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4486_ = l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0;
                v___f_4487_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0_once
                    ),
                    _init_l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0,
                );
                v___x_4488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4488_, 0, v_w_4483_);
                crate::leanh::lean_ctor_set(v___x_4488_, 1, v_expr_4485_);
                v___x_4489_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
                    v___f_4487_,
                    v___f_4486_,
                    v_cache_4484_,
                    v___x_4488_,
                );
                if crate::leanh::lean_obj_tag(v___x_4489_) == 0 {
                    v___x_4490_ = crate::leanh::lean_box(0);
                    return v___x_4490_;
                } else {
                    v_val_4491_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                    v_isSharedCheck_4498_ = (!crate::leanh::lean_is_exclusive(v___x_4489_)) as u8;
                    if v_isSharedCheck_4498_ == 0 {
                        v___x_4493_ = v___x_4489_;
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4491_);
                        crate::leanh::lean_dec(v___x_4489_);
                        v___x_4493_ = crate::leanh::lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4494_ == 0 {
                    v___x_4496_ = v___x_4493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_val_4491_);
                    v___x_4496_ = v_reuseFailAlloc_4497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f___redArg___boxed(
    mut v_w_4499_: *mut crate::leanh::LeanObject,
    mut v_cache_4500_: *mut crate::leanh::LeanObject,
    mut v_expr_4501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4502_ =
        l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f___redArg(v_w_4499_, v_cache_4500_, v_expr_4501_);
    crate::leanh::lean_dec_ref(v_cache_4500_);
    return v_res_4502_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f(
    mut v_aig_4503_: *mut crate::leanh::LeanObject,
    mut v_w_4504_: *mut crate::leanh::LeanObject,
    mut v_cache_4505_: *mut crate::leanh::LeanObject,
    mut v_expr_4506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4507_ = l_Std_Tactic_BVDecide_BVExpr_instHashableKey___closed__0;
                v___f_4508_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0_once
                    ),
                    _init_l_Std_Tactic_BVDecide_BVExpr_Cache_insert___redArg___closed__0,
                );
                v___x_4509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4509_, 0, v_w_4504_);
                crate::leanh::lean_ctor_set(v___x_4509_, 1, v_expr_4506_);
                v___x_4510_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
                    v___f_4508_,
                    v___f_4507_,
                    v_cache_4505_,
                    v___x_4509_,
                );
                if crate::leanh::lean_obj_tag(v___x_4510_) == 0 {
                    v___x_4511_ = crate::leanh::lean_box(0);
                    return v___x_4511_;
                } else {
                    v_val_4512_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                    v_isSharedCheck_4519_ = (!crate::leanh::lean_is_exclusive(v___x_4510_)) as u8;
                    if v_isSharedCheck_4519_ == 0 {
                        v___x_4514_ = v___x_4510_;
                        v_isShared_4515_ = v_isSharedCheck_4519_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4512_);
                        crate::leanh::lean_dec(v___x_4510_);
                        v___x_4514_ = crate::leanh::lean_box(0);
                        v_isShared_4515_ = v_isSharedCheck_4519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4515_ == 0 {
                    v___x_4517_ = v___x_4514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_val_4512_);
                    v___x_4517_ = v_reuseFailAlloc_4518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f___boxed(
    mut v_aig_4520_: *mut crate::leanh::LeanObject,
    mut v_w_4521_: *mut crate::leanh::LeanObject,
    mut v_cache_4522_: *mut crate::leanh::LeanObject,
    mut v_expr_4523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4524_ = l_Std_Tactic_BVDecide_BVExpr_Cache_get_x3f(
        v_aig_4520_,
        v_w_4521_,
        v_cache_4522_,
        v_expr_4523_,
    );
    crate::leanh::lean_dec_ref(v_cache_4522_);
    crate::leanh::lean_dec_ref(v_aig_4520_);
    return v_res_4524_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_cast___redArg(
    mut v_cache_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_cache_4525_);
    return v_cache_4525_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_cast___redArg___boxed(
    mut v_cache_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4527_ = l_Std_Tactic_BVDecide_BVExpr_Cache_cast___redArg(v_cache_4526_);
    crate::leanh::lean_dec_ref(v_cache_4526_);
    return v_res_4527_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_cast(
    mut v_aig1_4528_: *mut crate::leanh::LeanObject,
    mut v_aig2_4529_: *mut crate::leanh::LeanObject,
    mut v_cache_4530_: *mut crate::leanh::LeanObject,
    mut v_h_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_cache_4530_);
    return v_cache_4530_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Cache_cast___boxed(
    mut v_aig1_4532_: *mut crate::leanh::LeanObject,
    mut v_aig2_4533_: *mut crate::leanh::LeanObject,
    mut v_cache_4534_: *mut crate::leanh::LeanObject,
    mut v_h_4535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4536_ = l_Std_Tactic_BVDecide_BVExpr_Cache_cast(
        v_aig1_4532_,
        v_aig2_4533_,
        v_cache_4534_,
        v_h_4535_,
    );
    crate::leanh::lean_dec_ref(v_cache_4534_);
    crate::leanh::lean_dec_ref(v_aig2_4533_);
    crate::leanh::lean_dec_ref(v_aig1_4532_);
    return v_res_4536_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___redArg(
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_x_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4538_) == 0 {
                    v___x_4539_ = crate::leanh::lean_box(0);
                    return v___x_4539_;
                } else {
                    v_key_4540_ = crate::leanh::lean_ctor_get(v_x_4538_, 0);
                    v_value_4541_ = crate::leanh::lean_ctor_get(v_x_4538_, 1);
                    v_tail_4542_ = crate::leanh::lean_ctor_get(v_x_4538_, 2);
                    v___x_4543_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(
                        v_key_4540_,
                        v_a_4537_,
                    );
                    if v___x_4543_ == 0 {
                        v_x_4538_ = v_tail_4542_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4541_);
                        v___x_4545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4545_, 0, v_value_4541_);
                        return v___x_4545_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___redArg___boxed(
    mut v_a_4546_: *mut crate::leanh::LeanObject,
    mut v_x_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___redArg(v_a_4546_, v_x_4547_);
    crate::leanh::lean_dec(v_x_4547_);
    crate::leanh::lean_dec_ref(v_a_4546_);
    return v_res_4548_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___redArg(
    mut v_m_4549_: *mut crate::leanh::LeanObject,
    mut v_a_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4555_: u64 = 0;
    let mut v___x_4556_: u64 = 0;
    let mut v___x_4557_: u64 = 0;
    let mut v_fold_4558_: u64 = 0;
    let mut v___x_4559_: u64 = 0;
    let mut v___x_4560_: u64 = 0;
    let mut v___x_4561_: u64 = 0;
    let mut v___x_4562_: usize = 0;
    let mut v___x_4563_: usize = 0;
    let mut v___x_4564_: usize = 0;
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: usize = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_4569_: u64 = 0;
    let mut v_hashCode_4570_: u64 = 0;
    let mut v_hashCode_4571_: u64 = 0;
    let mut v_hashCode_4572_: u64 = 0;
    let mut v_hashCode_4573_: u64 = 0;
    let mut v_hashCode_4574_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4551_ = crate::leanh::lean_ctor_get(v_m_4549_, 1);
                v_expr_4552_ = crate::leanh::lean_ctor_get(v_a_4550_, 1);
                v___x_4553_ = lean_array_get_size(v_buckets_4551_);
                match crate::leanh::lean_obj_tag(v_expr_4552_) {
                    0 => {
                        v_hashCode_4569_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4555_ = v_hashCode_4569_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_hashCode_4570_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4555_ = v_hashCode_4570_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_hashCode_4571_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4555_ = v_hashCode_4571_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_hashCode_4572_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4555_ = v_hashCode_4572_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_hashCode_4573_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_4555_ = v_hashCode_4573_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_hashCode_4574_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_4555_ = v_hashCode_4574_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4556_ = 32u64;
                v___x_4557_ = lean_uint64_shift_right(v___y_4555_, v___x_4556_);
                v_fold_4558_ = lean_uint64_xor(v___y_4555_, v___x_4557_);
                v___x_4559_ = 16u64;
                v___x_4560_ = lean_uint64_shift_right(v_fold_4558_, v___x_4559_);
                v___x_4561_ = lean_uint64_xor(v_fold_4558_, v___x_4560_);
                v___x_4562_ = lean_uint64_to_usize(v___x_4561_);
                v___x_4563_ = lean_usize_of_nat(v___x_4553_);
                v___x_4564_ = 1usize;
                v___x_4565_ = lean_usize_sub(v___x_4563_, v___x_4564_);
                v___x_4566_ = lean_usize_land(v___x_4562_, v___x_4565_);
                v___x_4567_ = lean_array_uget_borrowed(v_buckets_4551_, v___x_4566_);
                v___x_4568_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___redArg(v_a_4550_, v___x_4567_);
                return v___x_4568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___redArg___boxed(
    mut v_m_4575_: *mut crate::leanh::LeanObject,
    mut v_a_4576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4577_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___redArg(v_m_4575_, v_a_4576_);
    crate::leanh::lean_dec_ref(v_a_4576_);
    crate::leanh::lean_dec_ref(v_m_4575_);
    return v_res_4577_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7_spec__32___redArg(
    mut v_x_4578_: *mut crate::leanh::LeanObject,
    mut v_x_4579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v_expr_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4589_: u64 = 0;
    let mut v___x_4590_: u64 = 0;
    let mut v___x_4591_: u64 = 0;
    let mut v_fold_4592_: u64 = 0;
    let mut v___x_4593_: u64 = 0;
    let mut v___x_4594_: u64 = 0;
    let mut v___x_4595_: u64 = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: usize = 0;
    let mut v___x_4598_: usize = 0;
    let mut v___x_4599_: usize = 0;
    let mut v___x_4600_: usize = 0;
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_4607_: u64 = 0;
    let mut v_hashCode_4608_: u64 = 0;
    let mut v_hashCode_4609_: u64 = 0;
    let mut v_hashCode_4610_: u64 = 0;
    let mut v_hashCode_4611_: u64 = 0;
    let mut v_hashCode_4612_: u64 = 0;
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4579_) == 0 {
                    return v_x_4578_;
                } else {
                    v_key_4580_ = crate::leanh::lean_ctor_get(v_x_4579_, 0);
                    v_value_4581_ = crate::leanh::lean_ctor_get(v_x_4579_, 1);
                    v_tail_4582_ = crate::leanh::lean_ctor_get(v_x_4579_, 2);
                    v_isSharedCheck_4613_ = (!crate::leanh::lean_is_exclusive(v_x_4579_)) as u8;
                    if v_isSharedCheck_4613_ == 0 {
                        v___x_4584_ = v_x_4579_;
                        v_isShared_4585_ = v_isSharedCheck_4613_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4582_);
                        crate::leanh::lean_inc(v_value_4581_);
                        crate::leanh::lean_inc(v_key_4580_);
                        crate::leanh::lean_dec(v_x_4579_);
                        v___x_4584_ = crate::leanh::lean_box(0);
                        v_isShared_4585_ = v_isSharedCheck_4613_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_expr_4586_ = crate::leanh::lean_ctor_get(v_key_4580_, 1);
                v___x_4587_ = lean_array_get_size(v_x_4578_);
                match crate::leanh::lean_obj_tag(v_expr_4586_) {
                    0 => {
                        v_hashCode_4607_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4589_ = v_hashCode_4607_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_4608_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4589_ = v_hashCode_4608_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_4609_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4589_ = v_hashCode_4609_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_4610_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4589_ = v_hashCode_4610_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_4611_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_4589_ = v_hashCode_4611_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_4612_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_4589_ = v_hashCode_4612_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4590_ = 32u64;
                v___x_4591_ = lean_uint64_shift_right(v___y_4589_, v___x_4590_);
                v_fold_4592_ = lean_uint64_xor(v___y_4589_, v___x_4591_);
                v___x_4593_ = 16u64;
                v___x_4594_ = lean_uint64_shift_right(v_fold_4592_, v___x_4593_);
                v___x_4595_ = lean_uint64_xor(v_fold_4592_, v___x_4594_);
                v___x_4596_ = lean_uint64_to_usize(v___x_4595_);
                v___x_4597_ = lean_usize_of_nat(v___x_4587_);
                v___x_4598_ = 1usize;
                v___x_4599_ = lean_usize_sub(v___x_4597_, v___x_4598_);
                v___x_4600_ = lean_usize_land(v___x_4596_, v___x_4599_);
                v___x_4601_ = lean_array_uget_borrowed(v_x_4578_, v___x_4600_);
                crate::leanh::lean_inc(v___x_4601_);
                if v_isShared_4585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4584_, 2, v___x_4601_);
                    v___x_4603_ = v___x_4584_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_key_4580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_value_4581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 2, v___x_4601_);
                    v___x_4603_ = v_reuseFailAlloc_4606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4604_ = lean_array_uset(v_x_4578_, v___x_4600_, v___x_4603_);
                v_x_4578_ = v___x_4604_;
                v_x_4579_ = v_tail_4582_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7___redArg(
    mut v_i_4614_: *mut crate::leanh::LeanObject,
    mut v_source_4615_: *mut crate::leanh::LeanObject,
    mut v_target_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v_es_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4617_ = lean_array_get_size(v_source_4615_);
                v___x_4618_ = lean_nat_dec_lt(v_i_4614_, v___x_4617_);
                if v___x_4618_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4615_);
                    crate::leanh::lean_dec(v_i_4614_);
                    return v_target_4616_;
                } else {
                    v_es_4619_ = lean_array_fget(v_source_4615_, v_i_4614_);
                    v___x_4620_ = crate::leanh::lean_box(0);
                    v_source_4621_ = lean_array_fset(v_source_4615_, v_i_4614_, v___x_4620_);
                    v_target_4622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7_spec__32___redArg(v_target_4616_, v_es_4619_);
                    v___x_4623_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4624_ = lean_nat_add(v_i_4614_, v___x_4623_);
                    crate::leanh::lean_dec(v_i_4614_);
                    v_i_4614_ = v___x_4624_;
                    v_source_4615_ = v_source_4621_;
                    v_target_4616_ = v_target_4622_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3___redArg(
    mut v_data_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = lean_array_get_size(v_data_4626_);
    v___x_4628_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4629_ = lean_nat_mul(v___x_4627_, v___x_4628_);
    v___x_4630_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4631_ = crate::leanh::lean_box(0);
    v___x_4632_ = lean_mk_array(v_nbuckets_4629_, v___x_4631_);
    v___x_4633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7___redArg(v___x_4630_, v_data_4626_, v___x_4632_);
    return v___x_4633_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__4___redArg(
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_b_4635_: *mut crate::leanh::LeanObject,
    mut v_x_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4636_) == 0 {
                    crate::leanh::lean_dec(v_b_4635_);
                    crate::leanh::lean_dec_ref(v_a_4634_);
                    return v_x_4636_;
                } else {
                    v_key_4637_ = crate::leanh::lean_ctor_get(v_x_4636_, 0);
                    v_value_4638_ = crate::leanh::lean_ctor_get(v_x_4636_, 1);
                    v_tail_4639_ = crate::leanh::lean_ctor_get(v_x_4636_, 2);
                    v_isSharedCheck_4651_ = (!crate::leanh::lean_is_exclusive(v_x_4636_)) as u8;
                    if v_isSharedCheck_4651_ == 0 {
                        v___x_4641_ = v_x_4636_;
                        v_isShared_4642_ = v_isSharedCheck_4651_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4639_);
                        crate::leanh::lean_inc(v_value_4638_);
                        crate::leanh::lean_inc(v_key_4637_);
                        crate::leanh::lean_dec(v_x_4636_);
                        v___x_4641_ = crate::leanh::lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4651_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4643_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(
                    v_key_4637_,
                    v_a_4634_,
                );
                if v___x_4643_ == 0 {
                    v___x_4644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__4___redArg(v_a_4634_, v_b_4635_, v_tail_4639_);
                    if v_isShared_4642_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4641_, 2, v___x_4644_);
                        v___x_4646_ = v___x_4641_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4647_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_key_4637_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_value_4638_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 2, v___x_4644_);
                        v___x_4646_ = v_reuseFailAlloc_4647_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4638_);
                    crate::leanh::lean_dec(v_key_4637_);
                    if v_isShared_4642_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4641_, 1, v_b_4635_);
                        crate::leanh::lean_ctor_set(v___x_4641_, 0, v_a_4634_);
                        v___x_4649_ = v___x_4641_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4650_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_b_4635_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_tail_4639_);
                        v___x_4649_ = v_reuseFailAlloc_4650_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4646_;
            }
            3 => {
                return v___x_4649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___redArg(
    mut v_a_4652_: *mut crate::leanh::LeanObject,
    mut v_x_4653_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4654_: u8 = 0;
    let mut v_key_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4653_) == 0 {
                    v___x_4654_ = 0;
                    return v___x_4654_;
                } else {
                    v_key_4655_ = crate::leanh::lean_ctor_get(v_x_4653_, 0);
                    v_tail_4656_ = crate::leanh::lean_ctor_get(v_x_4653_, 2);
                    v___x_4657_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(
                        v_key_4655_,
                        v_a_4652_,
                    );
                    if v___x_4657_ == 0 {
                        v_x_4653_ = v_tail_4656_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4657_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___redArg___boxed(
    mut v_a_4659_: *mut crate::leanh::LeanObject,
    mut v_x_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4661_: u8 = 0;
    let mut v_r_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___redArg(v_a_4659_, v_x_4660_);
    crate::leanh::lean_dec(v_x_4660_);
    crate::leanh::lean_dec_ref(v_a_4659_);
    v_r_4662_ = crate::leanh::lean_box((v_res_4661_) as usize);
    return v_r_4662_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1___redArg(
    mut v_m_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
    mut v_b_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v_expr_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4674_: u64 = 0;
    let mut v___x_4675_: u64 = 0;
    let mut v___x_4676_: u64 = 0;
    let mut v_fold_4677_: u64 = 0;
    let mut v___x_4678_: u64 = 0;
    let mut v___x_4679_: u64 = 0;
    let mut v___x_4680_: u64 = 0;
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4683_: usize = 0;
    let mut v___x_4684_: usize = 0;
    let mut v___x_4685_: usize = 0;
    let mut v_bkt_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: u8 = 0;
    let mut v_val_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_4712_: u64 = 0;
    let mut v_hashCode_4713_: u64 = 0;
    let mut v_hashCode_4714_: u64 = 0;
    let mut v_hashCode_4715_: u64 = 0;
    let mut v_hashCode_4716_: u64 = 0;
    let mut v_hashCode_4717_: u64 = 0;
    let mut v_isSharedCheck_4718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4666_ = crate::leanh::lean_ctor_get(v_m_4663_, 0);
                v_buckets_4667_ = crate::leanh::lean_ctor_get(v_m_4663_, 1);
                v_isSharedCheck_4718_ = (!crate::leanh::lean_is_exclusive(v_m_4663_)) as u8;
                if v_isSharedCheck_4718_ == 0 {
                    v___x_4669_ = v_m_4663_;
                    v_isShared_4670_ = v_isSharedCheck_4718_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4667_);
                    crate::leanh::lean_inc(v_size_4666_);
                    crate::leanh::lean_dec(v_m_4663_);
                    v___x_4669_ = crate::leanh::lean_box(0);
                    v_isShared_4670_ = v_isSharedCheck_4718_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_expr_4671_ = crate::leanh::lean_ctor_get(v_a_4664_, 1);
                v___x_4672_ = lean_array_get_size(v_buckets_4667_);
                match crate::leanh::lean_obj_tag(v_expr_4671_) {
                    0 => {
                        v_hashCode_4712_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4674_ = v_hashCode_4712_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_4713_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4674_ = v_hashCode_4713_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_4714_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4674_ = v_hashCode_4714_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_4715_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4674_ = v_hashCode_4715_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_4716_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_4674_ = v_hashCode_4716_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_4717_ = crate::leanh::lean_ctor_get_uint64(
                            v_expr_4671_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_4674_ = v_hashCode_4717_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4675_ = 32u64;
                v___x_4676_ = lean_uint64_shift_right(v___y_4674_, v___x_4675_);
                v_fold_4677_ = lean_uint64_xor(v___y_4674_, v___x_4676_);
                v___x_4678_ = 16u64;
                v___x_4679_ = lean_uint64_shift_right(v_fold_4677_, v___x_4678_);
                v___x_4680_ = lean_uint64_xor(v_fold_4677_, v___x_4679_);
                v___x_4681_ = lean_uint64_to_usize(v___x_4680_);
                v___x_4682_ = lean_usize_of_nat(v___x_4672_);
                v___x_4683_ = 1usize;
                v___x_4684_ = lean_usize_sub(v___x_4682_, v___x_4683_);
                v___x_4685_ = lean_usize_land(v___x_4681_, v___x_4684_);
                v_bkt_4686_ = lean_array_uget_borrowed(v_buckets_4667_, v___x_4685_);
                v___x_4687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___redArg(v_a_4664_, v_bkt_4686_);
                if v___x_4687_ == 0 {
                    v___x_4688_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4689_ = lean_nat_add(v_size_4666_, v___x_4688_);
                    crate::leanh::lean_dec(v_size_4666_);
                    crate::leanh::lean_inc(v_bkt_4686_);
                    v___x_4690_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4690_, 0, v_a_4664_);
                    crate::leanh::lean_ctor_set(v___x_4690_, 1, v_b_4665_);
                    crate::leanh::lean_ctor_set(v___x_4690_, 2, v_bkt_4686_);
                    v_buckets_x27_4691_ =
                        lean_array_uset(v_buckets_4667_, v___x_4685_, v___x_4690_);
                    v___x_4692_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4693_ = lean_nat_mul(v_size_x27_4689_, v___x_4692_);
                    v___x_4694_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4695_ = lean_nat_div(v___x_4693_, v___x_4694_);
                    crate::leanh::lean_dec(v___x_4693_);
                    v___x_4696_ = lean_array_get_size(v_buckets_x27_4691_);
                    v___x_4697_ = lean_nat_dec_le(v___x_4695_, v___x_4696_);
                    crate::leanh::lean_dec(v___x_4695_);
                    if v___x_4697_ == 0 {
                        v_val_4698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3___redArg(v_buckets_x27_4691_);
                        if v_isShared_4670_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4669_, 1, v_val_4698_);
                            crate::leanh::lean_ctor_set(v___x_4669_, 0, v_size_x27_4689_);
                            v___x_4700_ = v___x_4669_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4701_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4701_,
                                0,
                                v_size_x27_4689_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_val_4698_);
                            v___x_4700_ = v_reuseFailAlloc_4701_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4670_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4669_, 1, v_buckets_x27_4691_);
                            crate::leanh::lean_ctor_set(v___x_4669_, 0, v_size_x27_4689_);
                            v___x_4703_ = v___x_4669_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4704_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4704_,
                                0,
                                v_size_x27_4689_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4704_,
                                1,
                                v_buckets_x27_4691_,
                            );
                            v___x_4703_ = v_reuseFailAlloc_4704_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4686_);
                    v___x_4705_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4706_ =
                        lean_array_uset(v_buckets_4667_, v___x_4685_, v___x_4705_);
                    v___x_4707_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__4___redArg(v_a_4664_, v_b_4665_, v_bkt_4686_);
                    v___x_4708_ = lean_array_uset(v_buckets_x27_4706_, v___x_4685_, v___x_4707_);
                    if v_isShared_4670_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4669_, 1, v___x_4708_);
                        v___x_4710_ = v___x_4669_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_size_4666_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4711_, 1, v___x_4708_);
                        v___x_4710_ = v_reuseFailAlloc_4711_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4700_;
            }
            4 => {
                return v___x_4703_;
            }
            5 => {
                return v___x_4710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38(
    mut v_x_4719_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_4719_) {
        0 => {
            let mut v___x_4720_: u64 = 0;
            v___x_4720_ = 0u64;
            return v___x_4720_;
        }
        1 => {
            let mut v_idx_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4722_: u64 = 0;
            let mut v___x_4723_: u64 = 0;
            let mut v___x_4724_: u64 = 0;
            v_idx_4721_ = crate::leanh::lean_ctor_get(v_x_4719_, 0);
            v___x_4722_ = 1u64;
            v___x_4723_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_4721_);
            v___x_4724_ = lean_uint64_mix_hash(v___x_4722_, v___x_4723_);
            return v___x_4724_;
        }
        _ => {
            let mut v_l_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4727_: u64 = 0;
            let mut v___x_4728_: u64 = 0;
            let mut v___x_4729_: u64 = 0;
            let mut v___x_4730_: u64 = 0;
            let mut v___x_4731_: u64 = 0;
            v_l_4725_ = crate::leanh::lean_ctor_get(v_x_4719_, 0);
            v_r_4726_ = crate::leanh::lean_ctor_get(v_x_4719_, 1);
            v___x_4727_ = 2u64;
            v___x_4728_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_4725_);
            v___x_4729_ = lean_uint64_mix_hash(v___x_4727_, v___x_4728_);
            v___x_4730_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_4726_);
            v___x_4731_ = lean_uint64_mix_hash(v___x_4729_, v___x_4730_);
            return v___x_4731_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38___boxed(
    mut v_x_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4733_: u64 = 0;
    let mut v_r_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38(v_x_4732_);
    crate::leanh::lean_dec(v_x_4732_);
    v_r_4734_ = crate::leanh::lean_box_uint64(v_res_4733_);
    return v_r_4734_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68_spec__83___redArg(
    mut v_x_4735_: *mut crate::leanh::LeanObject,
    mut v_x_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: u64 = 0;
    let mut v___x_4745_: u64 = 0;
    let mut v___x_4746_: u64 = 0;
    let mut v_fold_4747_: u64 = 0;
    let mut v___x_4748_: u64 = 0;
    let mut v___x_4749_: u64 = 0;
    let mut v___x_4750_: u64 = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: usize = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4736_) == 0 {
                    return v_x_4735_;
                } else {
                    v_key_4737_ = crate::leanh::lean_ctor_get(v_x_4736_, 0);
                    v_value_4738_ = crate::leanh::lean_ctor_get(v_x_4736_, 1);
                    v_tail_4739_ = crate::leanh::lean_ctor_get(v_x_4736_, 2);
                    v_isSharedCheck_4762_ = (!crate::leanh::lean_is_exclusive(v_x_4736_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4741_ = v_x_4736_;
                        v_isShared_4742_ = v_isSharedCheck_4762_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4739_);
                        crate::leanh::lean_inc(v_value_4738_);
                        crate::leanh::lean_inc(v_key_4737_);
                        crate::leanh::lean_dec(v_x_4736_);
                        v___x_4741_ = crate::leanh::lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4762_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4743_ = lean_array_get_size(v_x_4735_);
                v___x_4744_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38(v_key_4737_);
                v___x_4745_ = 32u64;
                v___x_4746_ = lean_uint64_shift_right(v___x_4744_, v___x_4745_);
                v_fold_4747_ = lean_uint64_xor(v___x_4744_, v___x_4746_);
                v___x_4748_ = 16u64;
                v___x_4749_ = lean_uint64_shift_right(v_fold_4747_, v___x_4748_);
                v___x_4750_ = lean_uint64_xor(v_fold_4747_, v___x_4749_);
                v___x_4751_ = lean_uint64_to_usize(v___x_4750_);
                v___x_4752_ = lean_usize_of_nat(v___x_4743_);
                v___x_4753_ = 1usize;
                v___x_4754_ = lean_usize_sub(v___x_4752_, v___x_4753_);
                v___x_4755_ = lean_usize_land(v___x_4751_, v___x_4754_);
                v___x_4756_ = lean_array_uget_borrowed(v_x_4735_, v___x_4755_);
                crate::leanh::lean_inc(v___x_4756_);
                if v_isShared_4742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4741_, 2, v___x_4756_);
                    v___x_4758_ = v___x_4741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4761_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_key_4737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 1, v_value_4738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 2, v___x_4756_);
                    v___x_4758_ = v_reuseFailAlloc_4761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4759_ = lean_array_uset(v_x_4735_, v___x_4755_, v___x_4758_);
                v_x_4735_ = v___x_4759_;
                v_x_4736_ = v_tail_4739_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68___redArg(
    mut v_i_4763_: *mut crate::leanh::LeanObject,
    mut v_source_4764_: *mut crate::leanh::LeanObject,
    mut v_target_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v_es_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4766_ = lean_array_get_size(v_source_4764_);
                v___x_4767_ = lean_nat_dec_lt(v_i_4763_, v___x_4766_);
                if v___x_4767_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4764_);
                    crate::leanh::lean_dec(v_i_4763_);
                    return v_target_4765_;
                } else {
                    v_es_4768_ = lean_array_fget(v_source_4764_, v_i_4763_);
                    v___x_4769_ = crate::leanh::lean_box(0);
                    v_source_4770_ = lean_array_fset(v_source_4764_, v_i_4763_, v___x_4769_);
                    v_target_4771_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68_spec__83___redArg(v_target_4765_, v_es_4768_);
                    v___x_4772_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4773_ = lean_nat_add(v_i_4763_, v___x_4772_);
                    crate::leanh::lean_dec(v_i_4763_);
                    v_i_4763_ = v___x_4773_;
                    v_source_4764_ = v_source_4770_;
                    v_target_4765_ = v_target_4771_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43___redArg(
    mut v_data_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = lean_array_get_size(v_data_4775_);
    v___x_4777_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4778_ = lean_nat_mul(v___x_4776_, v___x_4777_);
    v___x_4779_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4780_ = crate::leanh::lean_box(0);
    v___x_4781_ = lean_mk_array(v_nbuckets_4778_, v___x_4780_);
    v___x_4782_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68___redArg(v___x_4779_, v_data_4775_, v___x_4781_);
    return v___x_4782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__44___redArg(
    mut v_a_4783_: *mut crate::leanh::LeanObject,
    mut v_b_4784_: *mut crate::leanh::LeanObject,
    mut v_x_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4785_) == 0 {
                    crate::leanh::lean_dec(v_b_4784_);
                    crate::leanh::lean_dec(v_a_4783_);
                    return v_x_4785_;
                } else {
                    v_key_4786_ = crate::leanh::lean_ctor_get(v_x_4785_, 0);
                    v_value_4787_ = crate::leanh::lean_ctor_get(v_x_4785_, 1);
                    v_tail_4788_ = crate::leanh::lean_ctor_get(v_x_4785_, 2);
                    v_isSharedCheck_4801_ = (!crate::leanh::lean_is_exclusive(v_x_4785_)) as u8;
                    if v_isSharedCheck_4801_ == 0 {
                        v___x_4790_ = v_x_4785_;
                        v_isShared_4791_ = v_isSharedCheck_4801_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4788_);
                        crate::leanh::lean_inc(v_value_4787_);
                        crate::leanh::lean_inc(v_key_4786_);
                        crate::leanh::lean_dec(v_x_4785_);
                        v___x_4790_ = crate::leanh::lean_box(0);
                        v_isShared_4791_ = v_isSharedCheck_4801_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4792_ = crate::leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                crate::leanh::lean_inc(v_a_4783_);
                crate::leanh::lean_inc(v_key_4786_);
                v___x_4793_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                    v___x_4792_,
                    v_key_4786_,
                    v_a_4783_,
                );
                if v___x_4793_ == 0 {
                    v___x_4794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__44___redArg(v_a_4783_, v_b_4784_, v_tail_4788_);
                    if v_isShared_4791_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4790_, 2, v___x_4794_);
                        v___x_4796_ = v___x_4790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4797_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_key_4786_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 1, v_value_4787_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 2, v___x_4794_);
                        v___x_4796_ = v_reuseFailAlloc_4797_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4787_);
                    crate::leanh::lean_dec(v_key_4786_);
                    if v_isShared_4791_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4790_, 1, v_b_4784_);
                        crate::leanh::lean_ctor_set(v___x_4790_, 0, v_a_4783_);
                        v___x_4799_ = v___x_4790_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4800_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4783_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4800_, 1, v_b_4784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4800_, 2, v_tail_4788_);
                        v___x_4799_ = v_reuseFailAlloc_4800_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4796_;
            }
            3 => {
                return v___x_4799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___redArg(
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_x_4803_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4804_: u8 = 0;
    let mut v_key_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4803_) == 0 {
                    crate::leanh::lean_dec(v_a_4802_);
                    v___x_4804_ = 0;
                    return v___x_4804_;
                } else {
                    v_key_4805_ = crate::leanh::lean_ctor_get(v_x_4803_, 0);
                    crate::leanh::lean_inc(v_key_4805_);
                    v_tail_4806_ = crate::leanh::lean_ctor_get(v_x_4803_, 2);
                    crate::leanh::lean_inc(v_tail_4806_);
                    crate::leanh::lean_dec_ref_known(v_x_4803_, 3);
                    v___x_4807_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_4802_);
                    v___x_4808_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_4807_,
                        v_key_4805_,
                        v_a_4802_,
                    );
                    if v___x_4808_ == 0 {
                        v_x_4803_ = v_tail_4806_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4806_);
                        crate::leanh::lean_dec(v_a_4802_);
                        return v___x_4808_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___redArg___boxed(
    mut v_a_4810_: *mut crate::leanh::LeanObject,
    mut v_x_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4812_: u8 = 0;
    let mut v_r_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___redArg(v_a_4810_, v_x_4811_);
    v_r_4813_ = crate::leanh::lean_box((v_res_4812_) as usize);
    return v_r_4813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18___redArg(
    mut v_m_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_b_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4821_: u8 = 0;
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: u64 = 0;
    let mut v___x_4824_: u64 = 0;
    let mut v___x_4825_: u64 = 0;
    let mut v_fold_4826_: u64 = 0;
    let mut v___x_4827_: u64 = 0;
    let mut v___x_4828_: u64 = 0;
    let mut v___x_4829_: u64 = 0;
    let mut v___x_4830_: usize = 0;
    let mut v___x_4831_: usize = 0;
    let mut v___x_4832_: usize = 0;
    let mut v___x_4833_: usize = 0;
    let mut v___x_4834_: usize = 0;
    let mut v_bkt_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v_val_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4817_ = crate::leanh::lean_ctor_get(v_m_4814_, 0);
                v_buckets_4818_ = crate::leanh::lean_ctor_get(v_m_4814_, 1);
                v_isSharedCheck_4861_ = (!crate::leanh::lean_is_exclusive(v_m_4814_)) as u8;
                if v_isSharedCheck_4861_ == 0 {
                    v___x_4820_ = v_m_4814_;
                    v_isShared_4821_ = v_isSharedCheck_4861_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4818_);
                    crate::leanh::lean_inc(v_size_4817_);
                    crate::leanh::lean_dec(v_m_4814_);
                    v___x_4820_ = crate::leanh::lean_box(0);
                    v_isShared_4821_ = v_isSharedCheck_4861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4822_ = lean_array_get_size(v_buckets_4818_);
                v___x_4823_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38(v_a_4815_);
                v___x_4824_ = 32u64;
                v___x_4825_ = lean_uint64_shift_right(v___x_4823_, v___x_4824_);
                v_fold_4826_ = lean_uint64_xor(v___x_4823_, v___x_4825_);
                v___x_4827_ = 16u64;
                v___x_4828_ = lean_uint64_shift_right(v_fold_4826_, v___x_4827_);
                v___x_4829_ = lean_uint64_xor(v_fold_4826_, v___x_4828_);
                v___x_4830_ = lean_uint64_to_usize(v___x_4829_);
                v___x_4831_ = lean_usize_of_nat(v___x_4822_);
                v___x_4832_ = 1usize;
                v___x_4833_ = lean_usize_sub(v___x_4831_, v___x_4832_);
                v___x_4834_ = lean_usize_land(v___x_4830_, v___x_4833_);
                v_bkt_4835_ = lean_array_uget_borrowed(v_buckets_4818_, v___x_4834_);
                crate::leanh::lean_inc(v_bkt_4835_);
                crate::leanh::lean_inc(v_a_4815_);
                v___x_4836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___redArg(v_a_4815_, v_bkt_4835_);
                if v___x_4836_ == 0 {
                    v___x_4837_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4838_ = lean_nat_add(v_size_4817_, v___x_4837_);
                    crate::leanh::lean_dec(v_size_4817_);
                    crate::leanh::lean_inc(v_bkt_4835_);
                    v___x_4839_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4839_, 0, v_a_4815_);
                    crate::leanh::lean_ctor_set(v___x_4839_, 1, v_b_4816_);
                    crate::leanh::lean_ctor_set(v___x_4839_, 2, v_bkt_4835_);
                    v_buckets_x27_4840_ =
                        lean_array_uset(v_buckets_4818_, v___x_4834_, v___x_4839_);
                    v___x_4841_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4842_ = lean_nat_mul(v_size_x27_4838_, v___x_4841_);
                    v___x_4843_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4844_ = lean_nat_div(v___x_4842_, v___x_4843_);
                    crate::leanh::lean_dec(v___x_4842_);
                    v___x_4845_ = lean_array_get_size(v_buckets_x27_4840_);
                    v___x_4846_ = lean_nat_dec_le(v___x_4844_, v___x_4845_);
                    crate::leanh::lean_dec(v___x_4844_);
                    if v___x_4846_ == 0 {
                        v_val_4847_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43___redArg(v_buckets_x27_4840_);
                        if v_isShared_4821_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4820_, 1, v_val_4847_);
                            crate::leanh::lean_ctor_set(v___x_4820_, 0, v_size_x27_4838_);
                            v___x_4849_ = v___x_4820_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4850_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4850_,
                                0,
                                v_size_x27_4838_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_val_4847_);
                            v___x_4849_ = v_reuseFailAlloc_4850_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4821_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4820_, 1, v_buckets_x27_4840_);
                            crate::leanh::lean_ctor_set(v___x_4820_, 0, v_size_x27_4838_);
                            v___x_4852_ = v___x_4820_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4853_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4853_,
                                0,
                                v_size_x27_4838_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4853_,
                                1,
                                v_buckets_x27_4840_,
                            );
                            v___x_4852_ = v_reuseFailAlloc_4853_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4835_);
                    v___x_4854_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4855_ =
                        lean_array_uset(v_buckets_4818_, v___x_4834_, v___x_4854_);
                    v___x_4856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__44___redArg(v_a_4815_, v_b_4816_, v_bkt_4835_);
                    v___x_4857_ = lean_array_uset(v_buckets_x27_4855_, v___x_4834_, v___x_4856_);
                    if v_isShared_4821_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4820_, 1, v___x_4857_);
                        v___x_4859_ = v___x_4820_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_size_4817_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 1, v___x_4857_);
                        v___x_4859_ = v_reuseFailAlloc_4860_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4849_;
            }
            3 => {
                return v___x_4852_;
            }
            4 => {
                return v___x_4859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__39___redArg(
    mut v_a_4862_: *mut crate::leanh::LeanObject,
    mut v_x_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4863_) == 0 {
                    crate::leanh::lean_dec(v_a_4862_);
                    v___x_4864_ = crate::leanh::lean_box(0);
                    return v___x_4864_;
                } else {
                    v_key_4865_ = crate::leanh::lean_ctor_get(v_x_4863_, 0);
                    crate::leanh::lean_inc(v_key_4865_);
                    v_value_4866_ = crate::leanh::lean_ctor_get(v_x_4863_, 1);
                    crate::leanh::lean_inc(v_value_4866_);
                    v_tail_4867_ = crate::leanh::lean_ctor_get(v_x_4863_, 2);
                    crate::leanh::lean_inc(v_tail_4867_);
                    crate::leanh::lean_dec_ref_known(v_x_4863_, 3);
                    v___x_4868_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_4862_);
                    v___x_4869_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_4868_,
                        v_key_4865_,
                        v_a_4862_,
                    );
                    if v___x_4869_ == 0 {
                        crate::leanh::lean_dec(v_value_4866_);
                        v_x_4863_ = v_tail_4867_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4867_);
                        crate::leanh::lean_dec(v_a_4862_);
                        v___x_4871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4871_, 0, v_value_4866_);
                        return v___x_4871_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___redArg(
    mut v_m_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u64 = 0;
    let mut v___x_4877_: u64 = 0;
    let mut v___x_4878_: u64 = 0;
    let mut v_fold_4879_: u64 = 0;
    let mut v___x_4880_: u64 = 0;
    let mut v___x_4881_: u64 = 0;
    let mut v___x_4882_: u64 = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: usize = 0;
    let mut v___x_4885_: usize = 0;
    let mut v___x_4886_: usize = 0;
    let mut v___x_4887_: usize = 0;
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4874_ = crate::leanh::lean_ctor_get(v_m_4872_, 1);
    v___x_4875_ = lean_array_get_size(v_buckets_4874_);
    v___x_4876_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__38(v_a_4873_);
    v___x_4877_ = 32u64;
    v___x_4878_ = lean_uint64_shift_right(v___x_4876_, v___x_4877_);
    v_fold_4879_ = lean_uint64_xor(v___x_4876_, v___x_4878_);
    v___x_4880_ = 16u64;
    v___x_4881_ = lean_uint64_shift_right(v_fold_4879_, v___x_4880_);
    v___x_4882_ = lean_uint64_xor(v_fold_4879_, v___x_4881_);
    v___x_4883_ = lean_uint64_to_usize(v___x_4882_);
    v___x_4884_ = lean_usize_of_nat(v___x_4875_);
    v___x_4885_ = 1usize;
    v___x_4886_ = lean_usize_sub(v___x_4884_, v___x_4885_);
    v___x_4887_ = lean_usize_land(v___x_4883_, v___x_4886_);
    v___x_4888_ = lean_array_uget_borrowed(v_buckets_4874_, v___x_4887_);
    crate::leanh::lean_inc(v___x_4888_);
    v___x_4889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__39___redArg(v_a_4873_, v___x_4888_);
    return v___x_4889_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___redArg___boxed(
    mut v_m_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___redArg(v_m_4890_, v_a_4891_);
    crate::leanh::lean_dec_ref(v_m_4890_);
    return v_res_4892_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__17(
    mut v_aig_4893_: *mut crate::leanh::LeanObject,
    mut v_ref_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4896_: u8 = 0;
    let mut v_decls_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_4895_ = crate::leanh::lean_ctor_get(v_ref_4894_, 0);
    v_invert_4896_ = crate::leanh::lean_ctor_get_uint8(
        v_ref_4894_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_decls_4897_ = crate::leanh::lean_ctor_get(v_aig_4893_, 0);
    v_decl_4898_ = lean_array_fget_borrowed(v_decls_4897_, v_gate_4895_);
    if crate::leanh::lean_obj_tag(v_decl_4898_) == 0 {
        let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4899_ = crate::leanh::lean_box((v_invert_4896_) as usize);
        v___x_4900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4899_);
        return v___x_4900_;
    } else {
        let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4901_ = crate::leanh::lean_box(0);
        return v___x_4901_;
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__17___boxed(
    mut v_aig_4902_: *mut crate::leanh::LeanObject,
    mut v_ref_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4904_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__17(v_aig_4902_, v_ref_4903_);
    crate::leanh::lean_dec_ref(v_ref_4903_);
    crate::leanh::lean_dec_ref(v_aig_4902_);
    return v_res_4904_;
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12(
    mut v_aig_4908_: *mut crate::leanh::LeanObject,
    mut v_input_4909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v_decls_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v_gate_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4921_: u8 = 0;
    let mut v_gate_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4923_: u8 = 0;
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4942_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsVal_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhsVal_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v_val_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: u8 = 0;
    let mut v_val_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: u8 = 0;
    let mut v_val_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: u8 = 0;
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: u8 = 0;
    let mut v_g_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4975_: u8 = 0;
    let mut v_unused_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v_val_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_unused_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_4910_ = crate::leanh::lean_ctor_get(v_input_4909_, 0);
                v_rhs_4911_ = crate::leanh::lean_ctor_get(v_input_4909_, 1);
                v_isSharedCheck_4994_ = (!crate::leanh::lean_is_exclusive(v_input_4909_)) as u8;
                if v_isSharedCheck_4994_ == 0 {
                    v___x_4913_ = v_input_4909_;
                    v_isShared_4914_ = v_isSharedCheck_4994_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_4911_);
                    crate::leanh::lean_inc(v_lhs_4910_);
                    crate::leanh::lean_dec(v_input_4909_);
                    v___x_4913_ = crate::leanh::lean_box(0);
                    v_isShared_4914_ = v_isSharedCheck_4994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_4915_ = crate::leanh::lean_ctor_get(v_aig_4908_, 0);
                v_cache_4916_ = crate::leanh::lean_ctor_get(v_aig_4908_, 1);
                v_isSharedCheck_4993_ = (!crate::leanh::lean_is_exclusive(v_aig_4908_)) as u8;
                if v_isSharedCheck_4993_ == 0 {
                    v___x_4918_ = v_aig_4908_;
                    v_isShared_4919_ = v_isSharedCheck_4993_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_4916_);
                    crate::leanh::lean_inc(v_decls_4915_);
                    crate::leanh::lean_dec(v_aig_4908_);
                    v___x_4918_ = crate::leanh::lean_box(0);
                    v_isShared_4919_ = v_isSharedCheck_4993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_4920_ = crate::leanh::lean_ctor_get(v_lhs_4910_, 0);
                crate::leanh::lean_inc(v_gate_4920_);
                v_invert_4921_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_4910_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_gate_4922_ = crate::leanh::lean_ctor_get(v_rhs_4911_, 0);
                v_invert_4923_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_4911_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_4924_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4925_ = lean_nat_mul(v_gate_4920_, v___x_4924_);
                v___x_4926_ = l_Bool_toNat(v_invert_4921_);
                v___x_4927_ = lean_nat_lor(v___x_4925_, v___x_4926_);
                crate::leanh::lean_dec(v___x_4926_);
                crate::leanh::lean_dec(v___x_4925_);
                v___x_4928_ = lean_nat_mul(v_gate_4922_, v___x_4924_);
                v___x_4929_ = l_Bool_toNat(v_invert_4923_);
                v___x_4930_ = lean_nat_lor(v___x_4928_, v___x_4929_);
                crate::leanh::lean_dec(v___x_4929_);
                crate::leanh::lean_dec(v___x_4928_);
                if v_isShared_4914_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4913_, 2);
                    crate::leanh::lean_ctor_set(v___x_4913_, 1, v___x_4930_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 0, v___x_4927_);
                    v_decl_4932_ = v___x_4913_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4992_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___x_4930_);
                    v_decl_4932_ = v_reuseFailAlloc_4992_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_decl_4932_);
                v___x_4933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___redArg(v_cache_4916_, v_decl_4932_);
                if crate::leanh::lean_obj_tag(v___x_4933_) == 0 {
                    crate::leanh::lean_inc(v_gate_4922_);
                    crate::leanh::lean_inc_ref(v_cache_4916_);
                    crate::leanh::lean_inc_ref(v_decls_4915_);
                    if v_isShared_4919_ == 0 {
                        v___x_4935_ = v___x_4918_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_decls_4915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 1, v_cache_4916_);
                        v___x_4935_ = v_reuseFailAlloc_4977_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_4932_);
                    crate::leanh::lean_dec(v_gate_4920_);
                    crate::leanh::lean_dec_ref(v_lhs_4910_);
                    v_isSharedCheck_4990_ = (!crate::leanh::lean_is_exclusive(v_rhs_4911_)) as u8;
                    if v_isSharedCheck_4990_ == 0 {
                        v_unused_4991_ = crate::leanh::lean_ctor_get(v_rhs_4911_, 0);
                        crate::leanh::lean_dec(v_unused_4991_);
                        v___x_4979_ = v_rhs_4911_;
                        v_isShared_4980_ = v_isSharedCheck_4990_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rhs_4911_);
                        v___x_4979_ = crate::leanh::lean_box(0);
                        v_isShared_4980_ = v_isSharedCheck_4990_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v_lhsVal_4951_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__17(v___x_4935_, v_lhs_4910_);
                crate::leanh::lean_dec_ref(v_lhs_4910_);
                v_rhsVal_4952_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__17(v___x_4935_, v_rhs_4911_);
                v_isSharedCheck_4975_ = (!crate::leanh::lean_is_exclusive(v_rhs_4911_)) as u8;
                if v_isSharedCheck_4975_ == 0 {
                    v_unused_4976_ = crate::leanh::lean_ctor_get(v_rhs_4911_, 0);
                    crate::leanh::lean_dec(v_unused_4976_);
                    v___x_4954_ = v_rhs_4911_;
                    v_isShared_4955_ = v_isSharedCheck_4975_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rhs_4911_);
                    v___x_4954_ = crate::leanh::lean_box(0);
                    v_isShared_4955_ = v_isSharedCheck_4975_;
                    state = 9;
                    continue;
                }
            }
            5 => {
                v___x_4938_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ref_4939_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v_ref_4939_, 0, v___x_4938_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ref_4939_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_4937_,
                );
                v___x_4940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4940_, 0, v___x_4935_);
                crate::leanh::lean_ctor_set(v___x_4940_, 1, v_ref_4939_);
                return v___x_4940_;
            }
            6 => {
                if v___y_4942_ == 0 {
                    crate::leanh::lean_dec(v_gate_4920_);
                    v___y_4937_ = v___y_4942_;
                    state = 5;
                    continue;
                } else {
                    v___x_4943_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4943_, 0, v_gate_4920_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4943_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_4921_,
                    );
                    v___x_4944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4944_, 0, v___x_4935_);
                    crate::leanh::lean_ctor_set(v___x_4944_, 1, v___x_4943_);
                    return v___x_4944_;
                }
            }
            7 => {
                v___x_4946_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4946_, 0, v_gate_4922_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_4923_,
                );
                v___x_4947_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4947_, 0, v___x_4935_);
                crate::leanh::lean_ctor_set(v___x_4947_, 1, v___x_4946_);
                return v___x_4947_;
            }
            8 => {
                v_ref_4949_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0;
                v___x_4950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4935_);
                crate::leanh::lean_ctor_set(v___x_4950_, 1, v_ref_4949_);
                return v___x_4950_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_lhsVal_4951_) == 1 {
                    crate::leanh::lean_del_object(v___x_4954_);
                    crate::leanh::lean_dec_ref(v_decl_4932_);
                    crate::leanh::lean_dec(v_gate_4920_);
                    crate::leanh::lean_dec_ref(v_cache_4916_);
                    crate::leanh::lean_dec_ref(v_decls_4915_);
                    v_val_4956_ = crate::leanh::lean_ctor_get(v_lhsVal_4951_, 0);
                    crate::leanh::lean_inc(v_val_4956_);
                    crate::leanh::lean_dec_ref_known(v_lhsVal_4951_, 1);
                    v___x_4957_ = (crate::leanh::lean_unbox(v_val_4956_) as u8);
                    crate::leanh::lean_dec(v_val_4956_);
                    if v___x_4957_ == 0 {
                        crate::leanh::lean_dec(v_rhsVal_4952_);
                        crate::leanh::lean_dec(v_gate_4922_);
                        state = 8;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_rhsVal_4952_) == 1 {
                            v_val_4958_ = crate::leanh::lean_ctor_get(v_rhsVal_4952_, 0);
                            crate::leanh::lean_inc(v_val_4958_);
                            crate::leanh::lean_dec_ref_known(v_rhsVal_4952_, 1);
                            v___x_4959_ = (crate::leanh::lean_unbox(v_val_4958_) as u8);
                            crate::leanh::lean_dec(v_val_4958_);
                            if v___x_4959_ == 0 {
                                crate::leanh::lean_dec(v_gate_4922_);
                                state = 8;
                                continue;
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_rhsVal_4952_);
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lhsVal_4951_);
                    if crate::leanh::lean_obj_tag(v_rhsVal_4952_) == 1 {
                        crate::leanh::lean_dec_ref(v_decl_4932_);
                        crate::leanh::lean_dec(v_gate_4922_);
                        crate::leanh::lean_dec_ref(v_cache_4916_);
                        crate::leanh::lean_dec_ref(v_decls_4915_);
                        v_val_4960_ = crate::leanh::lean_ctor_get(v_rhsVal_4952_, 0);
                        crate::leanh::lean_inc(v_val_4960_);
                        crate::leanh::lean_dec_ref_known(v_rhsVal_4952_, 1);
                        v___x_4961_ = (crate::leanh::lean_unbox(v_val_4960_) as u8);
                        crate::leanh::lean_dec(v_val_4960_);
                        if v___x_4961_ == 0 {
                            crate::leanh::lean_del_object(v___x_4954_);
                            crate::leanh::lean_dec(v_gate_4920_);
                            state = 8;
                            continue;
                        } else {
                            if v_isShared_4955_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4954_, 0, v_gate_4920_);
                                v___x_4963_ = v___x_4954_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4965_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4965_,
                                    0,
                                    v_gate_4920_,
                                );
                                v___x_4963_ = v_reuseFailAlloc_4965_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_rhsVal_4952_);
                        v___x_4966_ = lean_nat_dec_eq(v_gate_4920_, v_gate_4922_);
                        crate::leanh::lean_dec(v_gate_4922_);
                        if v___x_4966_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4935_);
                            crate::leanh::lean_dec(v_gate_4920_);
                            v_g_4967_ = lean_array_get_size(v_decls_4915_);
                            crate::leanh::lean_inc_ref(v_decl_4932_);
                            v_cache_4968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18___redArg(v_cache_4916_, v_decl_4932_, v_g_4967_);
                            v_decls_4969_ = lean_array_push(v_decls_4915_, v_decl_4932_);
                            v___x_4970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4970_, 0, v_decls_4969_);
                            crate::leanh::lean_ctor_set(v___x_4970_, 1, v_cache_4968_);
                            if v_isShared_4955_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4954_, 0, v_g_4967_);
                                v___x_4972_ = v___x_4954_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_4974_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_g_4967_);
                                v___x_4972_ = v_reuseFailAlloc_4974_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4954_);
                            crate::leanh::lean_dec_ref(v_decl_4932_);
                            crate::leanh::lean_dec_ref(v_cache_4916_);
                            crate::leanh::lean_dec_ref(v_decls_4915_);
                            if v_invert_4921_ == 0 {
                                if v_invert_4923_ == 0 {
                                    v___y_4942_ = v___x_4966_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_gate_4920_);
                                    v___y_4937_ = v_invert_4921_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_4942_ = v_invert_4923_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4963_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_4921_,
                );
                v___x_4964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4964_, 0, v___x_4935_);
                crate::leanh::lean_ctor_set(v___x_4964_, 1, v___x_4963_);
                return v___x_4964_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4972_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4966_,
                );
                v___x_4973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4973_, 0, v___x_4970_);
                crate::leanh::lean_ctor_set(v___x_4973_, 1, v___x_4972_);
                return v___x_4973_;
            }
            12 => {
                v_val_4981_ = crate::leanh::lean_ctor_get(v___x_4933_, 0);
                crate::leanh::lean_inc(v_val_4981_);
                crate::leanh::lean_dec_ref_known(v___x_4933_, 1);
                if v_isShared_4919_ == 0 {
                    v___x_4983_ = v___x_4918_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_decls_4915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_cache_4916_);
                    v___x_4983_ = v_reuseFailAlloc_4989_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4984_ = 0;
                if v_isShared_4980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4979_, 0, v_val_4981_);
                    v___x_4986_ = v___x_4979_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_val_4981_);
                    v___x_4986_ = v_reuseFailAlloc_4988_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4984_,
                );
                v___x_4987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4987_, 0, v___x_4983_);
                crate::leanh::lean_ctor_set(v___x_4987_, 1, v___x_4986_);
                return v___x_4987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(
    mut v_aig_4995_: *mut crate::leanh::LeanObject,
    mut v_input_4996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v_gate_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_4997_ = crate::leanh::lean_ctor_get(v_input_4996_, 0);
                v_rhs_4998_ = crate::leanh::lean_ctor_get(v_input_4996_, 1);
                v_isSharedCheck_5013_ = (!crate::leanh::lean_is_exclusive(v_input_4996_)) as u8;
                if v_isSharedCheck_5013_ == 0 {
                    v___x_5000_ = v_input_4996_;
                    v_isShared_5001_ = v_isSharedCheck_5013_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_4998_);
                    crate::leanh::lean_inc(v_lhs_4997_);
                    crate::leanh::lean_dec(v_input_4996_);
                    v___x_5000_ = crate::leanh::lean_box(0);
                    v_isShared_5001_ = v_isSharedCheck_5013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_5002_ = crate::leanh::lean_ctor_get(v_lhs_4997_, 0);
                v_gate_5003_ = crate::leanh::lean_ctor_get(v_rhs_4998_, 0);
                v___x_5004_ = lean_nat_dec_lt(v_gate_5002_, v_gate_5003_);
                if v___x_5004_ == 0 {
                    if v_isShared_5001_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5000_, 1, v_lhs_4997_);
                        crate::leanh::lean_ctor_set(v___x_5000_, 0, v_rhs_4998_);
                        v___x_5006_ = v___x_5000_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5008_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_rhs_4998_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 1, v_lhs_4997_);
                        v___x_5006_ = v_reuseFailAlloc_5008_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5001_ == 0 {
                        v___x_5010_ = v___x_5000_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5012_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_lhs_4997_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_rhs_4998_);
                        v___x_5010_ = v_reuseFailAlloc_5012_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5007_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12(v_aig_4995_, v___x_5006_);
                return v___x_5007_;
            }
            3 => {
                v___x_5011_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12(v_aig_4995_, v___x_5010_);
                return v___x_5011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__7(
    mut v_aig_5014_: *mut crate::leanh::LeanObject,
    mut v_input_5015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5020_: u8 = 0;
    let mut v_aig_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5024_: u8 = 0;
    let mut v_gate_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5028_: u8 = 0;
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut v_unused_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5042_: u8 = 0;
    let mut v_gate_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5046_: u8 = 0;
    let mut v___x_5047_: u8 = 0;
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut v_unused_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5061_: u8 = 0;
    let mut v___y_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5064_: u8 = 0;
    let mut v_gate_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5068_: u8 = 0;
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut v_gate_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5080_: u8 = 0;
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5088_: u8 = 0;
    let mut v_invert_5089_: u8 = 0;
    let mut v_gate_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_gate_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5057_ = crate::leanh::lean_ctor_get(v_input_5015_, 0);
                v_rhs_5058_ = crate::leanh::lean_ctor_get(v_input_5015_, 1);
                v_isSharedCheck_5108_ = (!crate::leanh::lean_is_exclusive(v_input_5015_)) as u8;
                if v_isSharedCheck_5108_ == 0 {
                    v___x_5060_ = v_input_5015_;
                    v_isShared_5061_ = v_isSharedCheck_5108_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_5058_);
                    crate::leanh::lean_inc(v_lhs_5057_);
                    crate::leanh::lean_dec(v_input_5015_);
                    v___x_5060_ = crate::leanh::lean_box(0);
                    v_isShared_5061_ = v_isSharedCheck_5108_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_5018_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5014_, v___y_5017_);
                v_ref_5019_ = crate::leanh::lean_ctor_get(v_res_5018_, 1);
                crate::leanh::lean_inc_ref(v_ref_5019_);
                v_invert_5020_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5019_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5020_ == 0 {
                    v_aig_5021_ = crate::leanh::lean_ctor_get(v_res_5018_, 0);
                    v_isSharedCheck_5037_ = (!crate::leanh::lean_is_exclusive(v_res_5018_)) as u8;
                    if v_isSharedCheck_5037_ == 0 {
                        v_unused_5038_ = crate::leanh::lean_ctor_get(v_res_5018_, 1);
                        crate::leanh::lean_dec(v_unused_5038_);
                        v___x_5023_ = v_res_5018_;
                        v_isShared_5024_ = v_isSharedCheck_5037_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_5021_);
                        crate::leanh::lean_dec(v_res_5018_);
                        v___x_5023_ = crate::leanh::lean_box(0);
                        v_isShared_5024_ = v_isSharedCheck_5037_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_5039_ = crate::leanh::lean_ctor_get(v_res_5018_, 0);
                    v_isSharedCheck_5055_ = (!crate::leanh::lean_is_exclusive(v_res_5018_)) as u8;
                    if v_isSharedCheck_5055_ == 0 {
                        v_unused_5056_ = crate::leanh::lean_ctor_get(v_res_5018_, 1);
                        crate::leanh::lean_dec(v_unused_5056_);
                        v___x_5041_ = v_res_5018_;
                        v_isShared_5042_ = v_isSharedCheck_5055_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_5039_);
                        crate::leanh::lean_dec(v_res_5018_);
                        v___x_5041_ = crate::leanh::lean_box(0);
                        v_isShared_5042_ = v_isSharedCheck_5055_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_5025_ = crate::leanh::lean_ctor_get(v_ref_5019_, 0);
                v_isSharedCheck_5036_ = (!crate::leanh::lean_is_exclusive(v_ref_5019_)) as u8;
                if v_isSharedCheck_5036_ == 0 {
                    v___x_5027_ = v_ref_5019_;
                    v_isShared_5028_ = v_isSharedCheck_5036_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5025_);
                    crate::leanh::lean_dec(v_ref_5019_);
                    v___x_5027_ = crate::leanh::lean_box(0);
                    v_isShared_5028_ = v_isSharedCheck_5036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5029_ = 1;
                if v_isShared_5028_ == 0 {
                    v___x_5031_ = v___x_5027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_gate_5025_);
                    v___x_5031_ = v_reuseFailAlloc_5035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5031_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5029_,
                );
                if v_isShared_5024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5023_, 1, v___x_5031_);
                    v___x_5033_ = v___x_5023_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_aig_5021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5031_);
                    v___x_5033_ = v_reuseFailAlloc_5034_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5033_;
            }
            6 => {
                v_gate_5043_ = crate::leanh::lean_ctor_get(v_ref_5019_, 0);
                v_isSharedCheck_5054_ = (!crate::leanh::lean_is_exclusive(v_ref_5019_)) as u8;
                if v_isSharedCheck_5054_ == 0 {
                    v___x_5045_ = v_ref_5019_;
                    v_isShared_5046_ = v_isSharedCheck_5054_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5043_);
                    crate::leanh::lean_dec(v_ref_5019_);
                    v___x_5045_ = crate::leanh::lean_box(0);
                    v_isShared_5046_ = v_isSharedCheck_5054_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5047_ = 0;
                if v_isShared_5046_ == 0 {
                    v___x_5049_ = v___x_5045_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5053_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_gate_5043_);
                    v___x_5049_ = v_reuseFailAlloc_5053_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5047_,
                );
                if v_isShared_5042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5041_, 1, v___x_5049_);
                    v___x_5051_ = v___x_5041_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_aig_5039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 1, v___x_5049_);
                    v___x_5051_ = v_reuseFailAlloc_5052_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5051_;
            }
            10 => {
                v_invert_5089_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_5057_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5089_ == 0 {
                    v_gate_5090_ = crate::leanh::lean_ctor_get(v_lhs_5057_, 0);
                    v_isSharedCheck_5098_ = (!crate::leanh::lean_is_exclusive(v_lhs_5057_)) as u8;
                    if v_isSharedCheck_5098_ == 0 {
                        v___x_5092_ = v_lhs_5057_;
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5090_);
                        crate::leanh::lean_dec(v_lhs_5057_);
                        v___x_5092_ = crate::leanh::lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_gate_5099_ = crate::leanh::lean_ctor_get(v_lhs_5057_, 0);
                    v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v_lhs_5057_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5101_ = v_lhs_5057_;
                        v_isShared_5102_ = v_isSharedCheck_5107_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5099_);
                        crate::leanh::lean_dec(v_lhs_5057_);
                        v___x_5101_ = crate::leanh::lean_box(0);
                        v_isShared_5102_ = v_isSharedCheck_5107_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                v_invert_5064_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_5058_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5064_ == 0 {
                    v_gate_5065_ = crate::leanh::lean_ctor_get(v_rhs_5058_, 0);
                    v_isSharedCheck_5076_ = (!crate::leanh::lean_is_exclusive(v_rhs_5058_)) as u8;
                    if v_isSharedCheck_5076_ == 0 {
                        v___x_5067_ = v_rhs_5058_;
                        v_isShared_5068_ = v_isSharedCheck_5076_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5065_);
                        crate::leanh::lean_dec(v_rhs_5058_);
                        v___x_5067_ = crate::leanh::lean_box(0);
                        v_isShared_5068_ = v_isSharedCheck_5076_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_gate_5077_ = crate::leanh::lean_ctor_get(v_rhs_5058_, 0);
                    v_isSharedCheck_5088_ = (!crate::leanh::lean_is_exclusive(v_rhs_5058_)) as u8;
                    if v_isSharedCheck_5088_ == 0 {
                        v___x_5079_ = v_rhs_5058_;
                        v_isShared_5080_ = v_isSharedCheck_5088_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5077_);
                        crate::leanh::lean_dec(v_rhs_5058_);
                        v___x_5079_ = crate::leanh::lean_box(0);
                        v_isShared_5080_ = v_isSharedCheck_5088_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5069_ = 1;
                if v_isShared_5068_ == 0 {
                    v___x_5071_ = v___x_5067_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_gate_5065_);
                    v___x_5071_ = v_reuseFailAlloc_5075_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5071_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5069_,
                );
                if v_isShared_5061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5060_, 1, v___x_5071_);
                    crate::leanh::lean_ctor_set(v___x_5060_, 0, v___y_5063_);
                    v___x_5073_ = v___x_5060_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___y_5063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 1, v___x_5071_);
                    v___x_5073_ = v_reuseFailAlloc_5074_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_5017_ = v___x_5073_;
                state = 1;
                continue;
            }
            15 => {
                v___x_5081_ = 0;
                if v_isShared_5080_ == 0 {
                    v___x_5083_ = v___x_5079_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5087_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_gate_5077_);
                    v___x_5083_ = v_reuseFailAlloc_5087_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5081_,
                );
                if v_isShared_5061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5060_, 1, v___x_5083_);
                    crate::leanh::lean_ctor_set(v___x_5060_, 0, v___y_5063_);
                    v___x_5085_ = v___x_5060_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___y_5063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5083_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_5017_ = v___x_5085_;
                state = 1;
                continue;
            }
            18 => {
                v___x_5094_ = 1;
                if v_isShared_5093_ == 0 {
                    v___x_5096_ = v___x_5092_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_gate_5090_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5096_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5094_,
                );
                v___y_5063_ = v___x_5096_;
                state = 11;
                continue;
            }
            20 => {
                v___x_5103_ = 0;
                if v_isShared_5102_ == 0 {
                    v___x_5105_ = v___x_5101_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_gate_5099_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5103_,
                );
                v___y_5063_ = v___x_5105_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkIfCached___at___00Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44_spec__70(
    mut v_aig_5109_: *mut crate::leanh::LeanObject,
    mut v_input_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_discr_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v_gate_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5122_: u8 = 0;
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v_gate_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5127_: u8 = 0;
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v_aig_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v_gate_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5145_: u8 = 0;
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5148_: u8 = 0;
    let mut v_lhsRef_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_isSharedCheck_5157_: u8 = 0;
    let mut v_reuseFailAlloc_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: u8 = 0;
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_discr_5111_ = crate::leanh::lean_ctor_get(v_input_5110_, 0);
                crate::leanh::lean_inc_ref_n(v_discr_5111_, 2);
                v_lhs_5112_ = crate::leanh::lean_ctor_get(v_input_5110_, 1);
                crate::leanh::lean_inc_ref(v_lhs_5112_);
                v_rhs_5113_ = crate::leanh::lean_ctor_get(v_input_5110_, 2);
                crate::leanh::lean_inc_ref(v_rhs_5113_);
                crate::leanh::lean_dec_ref(v_input_5110_);
                v___x_5114_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5114_, 0, v_discr_5111_);
                crate::leanh::lean_ctor_set(v___x_5114_, 1, v_lhs_5112_);
                v_res_5115_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5109_, v___x_5114_);
                v_aig_5116_ = crate::leanh::lean_ctor_get(v_res_5115_, 0);
                v_ref_5117_ = crate::leanh::lean_ctor_get(v_res_5115_, 1);
                v_isSharedCheck_5170_ = (!crate::leanh::lean_is_exclusive(v_res_5115_)) as u8;
                if v_isSharedCheck_5170_ == 0 {
                    v___x_5119_ = v_res_5115_;
                    v_isShared_5120_ = v_isSharedCheck_5170_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5117_);
                    crate::leanh::lean_inc(v_aig_5116_);
                    crate::leanh::lean_dec(v_res_5115_);
                    v___x_5119_ = crate::leanh::lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5170_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_5121_ = crate::leanh::lean_ctor_get(v_discr_5111_, 0);
                v_invert_5122_ = crate::leanh::lean_ctor_get_uint8(
                    v_discr_5111_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5169_ = (!crate::leanh::lean_is_exclusive(v_discr_5111_)) as u8;
                if v_isSharedCheck_5169_ == 0 {
                    v___x_5124_ = v_discr_5111_;
                    v_isShared_5125_ = v_isSharedCheck_5169_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5121_);
                    crate::leanh::lean_dec(v_discr_5111_);
                    v___x_5124_ = crate::leanh::lean_box(0);
                    v_isShared_5125_ = v_isSharedCheck_5169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_5126_ = crate::leanh::lean_ctor_get(v_rhs_5113_, 0);
                v_invert_5127_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_5113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5168_ = (!crate::leanh::lean_is_exclusive(v_rhs_5113_)) as u8;
                if v_isSharedCheck_5168_ == 0 {
                    v___x_5129_ = v_rhs_5113_;
                    v_isShared_5130_ = v_isSharedCheck_5168_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5126_);
                    crate::leanh::lean_dec(v_rhs_5113_);
                    v___x_5129_ = crate::leanh::lean_box(0);
                    v_isShared_5130_ = v_isSharedCheck_5168_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_invert_5122_ == 0 {
                    v___x_5160_ = 1;
                    if v_isShared_5125_ == 0 {
                        v___x_5162_ = v___x_5124_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_gate_5121_);
                        v___x_5162_ = v_reuseFailAlloc_5163_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_5164_ = 0;
                    if v_isShared_5125_ == 0 {
                        v___x_5166_ = v___x_5124_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5167_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_gate_5121_);
                        v___x_5166_ = v_reuseFailAlloc_5167_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5130_ == 0 {
                    v___x_5135_ = v___x_5129_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5159_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_gate_5126_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5159_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5127_,
                    );
                    v___x_5135_ = v_reuseFailAlloc_5159_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5119_, 1, v___x_5135_);
                    crate::leanh::lean_ctor_set(v___x_5119_, 0, v_ref_5133_);
                    v___x_5137_ = v___x_5119_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_ref_5133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 1, v___x_5135_);
                    v___x_5137_ = v_reuseFailAlloc_5158_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_res_5138_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5132_, v___x_5137_);
                v_aig_5139_ = crate::leanh::lean_ctor_get(v_res_5138_, 0);
                v_ref_5140_ = crate::leanh::lean_ctor_get(v_res_5138_, 1);
                v_isSharedCheck_5157_ = (!crate::leanh::lean_is_exclusive(v_res_5138_)) as u8;
                if v_isSharedCheck_5157_ == 0 {
                    v___x_5142_ = v_res_5138_;
                    v_isShared_5143_ = v_isSharedCheck_5157_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5140_);
                    crate::leanh::lean_inc(v_aig_5139_);
                    crate::leanh::lean_dec(v_res_5138_);
                    v___x_5142_ = crate::leanh::lean_box(0);
                    v_isShared_5143_ = v_isSharedCheck_5157_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_gate_5144_ = crate::leanh::lean_ctor_get(v_ref_5117_, 0);
                v_invert_5145_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5117_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5156_ = (!crate::leanh::lean_is_exclusive(v_ref_5117_)) as u8;
                if v_isSharedCheck_5156_ == 0 {
                    v___x_5147_ = v_ref_5117_;
                    v_isShared_5148_ = v_isSharedCheck_5156_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5144_);
                    crate::leanh::lean_dec(v_ref_5117_);
                    v___x_5147_ = crate::leanh::lean_box(0);
                    v_isShared_5148_ = v_isSharedCheck_5156_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5148_ == 0 {
                    v_lhsRef_5150_ = v___x_5147_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_gate_5144_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5155_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5145_,
                    );
                    v_lhsRef_5150_ = v_reuseFailAlloc_5155_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5142_, 0, v_lhsRef_5150_);
                    v___x_5152_ = v___x_5142_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_lhsRef_5150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 1, v_ref_5140_);
                    v___x_5152_ = v_reuseFailAlloc_5154_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5153_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__7(v_aig_5139_, v___x_5152_);
                return v___x_5153_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5160_,
                );
                v_aig_5132_ = v_aig_5116_;
                v_ref_5133_ = v___x_5162_;
                state = 4;
                continue;
            }
            12 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5166_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5164_,
                );
                v_aig_5132_ = v_aig_5116_;
                v_ref_5133_ = v___x_5166_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___redArg(
    mut v_w_5171_: *mut crate::leanh::LeanObject,
    mut v_aig_5172_: *mut crate::leanh::LeanObject,
    mut v_curr_5173_: *mut crate::leanh::LeanObject,
    mut v_discr_5174_: *mut crate::leanh::LeanObject,
    mut v_lhs_5175_: *mut crate::leanh::LeanObject,
    mut v_rhs_5176_: *mut crate::leanh::LeanObject,
    mut v_s_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5186_: u8 = 0;
    let mut v_gate_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5188_: u8 = 0;
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5191_: u8 = 0;
    let mut v_discr_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut v___x_5204_: u8 = 0;
    let mut v___y_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: u8 = 0;
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: u8 = 0;
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5204_ = lean_nat_dec_lt(v_curr_5173_, v_w_5171_);
                if v___x_5204_ == 0 {
                    crate::leanh::lean_dec_ref(v_discr_5174_);
                    crate::leanh::lean_dec(v_curr_5173_);
                    v___x_5216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5216_, 0, v_aig_5172_);
                    crate::leanh::lean_ctor_set(v___x_5216_, 1, v_s_5177_);
                    return v___x_5216_;
                } else {
                    v_ref_5217_ = lean_array_fget_borrowed(v_lhs_5175_, v_curr_5173_);
                    v___x_5218_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5219_ = lean_nat_shiftr(v_ref_5217_, v___x_5218_);
                    v___x_5220_ = lean_nat_land(v___x_5218_, v_ref_5217_);
                    v___x_5221_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5222_ = lean_nat_dec_eq(v___x_5220_, v___x_5221_);
                    crate::leanh::lean_dec(v___x_5220_);
                    if v___x_5222_ == 0 {
                        v___x_5223_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5223_, 0, v___x_5219_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5223_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5204_,
                        );
                        v___y_5206_ = v___x_5223_;
                        state = 4;
                        continue;
                    } else {
                        v___x_5224_ = 0;
                        v___x_5225_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5225_, 0, v___x_5219_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5225_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5224_,
                        );
                        v___y_5206_ = v___x_5225_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_discr_5174_);
                v_input_5181_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_input_5181_, 0, v_discr_5174_);
                crate::leanh::lean_ctor_set(v_input_5181_, 1, v___y_5179_);
                crate::leanh::lean_ctor_set(v_input_5181_, 2, v___y_5180_);
                v_res_5182_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44_spec__70(v_aig_5172_, v_input_5181_);
                v_ref_5183_ = crate::leanh::lean_ctor_get(v_res_5182_, 1);
                crate::leanh::lean_inc_ref(v_ref_5183_);
                v_aig_5184_ = crate::leanh::lean_ctor_get(v_res_5182_, 0);
                crate::leanh::lean_inc_ref(v_aig_5184_);
                crate::leanh::lean_dec_ref(v_res_5182_);
                v_gate_5185_ = crate::leanh::lean_ctor_get(v_discr_5174_, 0);
                crate::leanh::lean_inc(v_gate_5185_);
                v_invert_5186_ = crate::leanh::lean_ctor_get_uint8(
                    v_discr_5174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_discr_5174_);
                v_gate_5187_ = crate::leanh::lean_ctor_get(v_ref_5183_, 0);
                v_invert_5188_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5203_ = (!crate::leanh::lean_is_exclusive(v_ref_5183_)) as u8;
                if v_isSharedCheck_5203_ == 0 {
                    v___x_5190_ = v_ref_5183_;
                    v_isShared_5191_ = v_isSharedCheck_5203_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5187_);
                    crate::leanh::lean_dec(v_ref_5183_);
                    v___x_5190_ = crate::leanh::lean_box(0);
                    v_isShared_5191_ = v_isSharedCheck_5203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5190_, 0, v_gate_5185_);
                    v_discr_5193_ = v___x_5190_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_gate_5185_);
                    v_discr_5193_ = v_reuseFailAlloc_5202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_discr_5193_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_5186_,
                );
                v___x_5194_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5195_ = lean_nat_add(v_curr_5173_, v___x_5194_);
                crate::leanh::lean_dec(v_curr_5173_);
                v___x_5196_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5197_ = lean_nat_mul(v_gate_5187_, v___x_5196_);
                crate::leanh::lean_dec(v_gate_5187_);
                v___x_5198_ = l_Bool_toNat(v_invert_5188_);
                v___x_5199_ = lean_nat_lor(v___x_5197_, v___x_5198_);
                crate::leanh::lean_dec(v___x_5198_);
                crate::leanh::lean_dec(v___x_5197_);
                v_s_5200_ = lean_array_push(v_s_5177_, v___x_5199_);
                v_aig_5172_ = v_aig_5184_;
                v_curr_5173_ = v___x_5195_;
                v_discr_5174_ = v_discr_5193_;
                v_s_5177_ = v_s_5200_;
                state = 0;
                continue;
            }
            4 => {
                v_ref_5207_ = lean_array_fget_borrowed(v_rhs_5176_, v_curr_5173_);
                v___x_5208_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5209_ = lean_nat_shiftr(v_ref_5207_, v___x_5208_);
                v___x_5210_ = lean_nat_land(v___x_5208_, v_ref_5207_);
                v___x_5211_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5212_ = lean_nat_dec_eq(v___x_5210_, v___x_5211_);
                crate::leanh::lean_dec(v___x_5210_);
                if v___x_5212_ == 0 {
                    v___x_5213_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5213_, 0, v___x_5209_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5213_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5204_,
                    );
                    v___y_5179_ = v___y_5206_;
                    v___y_5180_ = v___x_5213_;
                    state = 1;
                    continue;
                } else {
                    v___x_5214_ = 0;
                    v___x_5215_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5215_, 0, v___x_5209_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5215_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5214_,
                    );
                    v___y_5179_ = v___y_5206_;
                    v___y_5180_ = v___x_5215_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___redArg___boxed(
    mut v_w_5226_: *mut crate::leanh::LeanObject,
    mut v_aig_5227_: *mut crate::leanh::LeanObject,
    mut v_curr_5228_: *mut crate::leanh::LeanObject,
    mut v_discr_5229_: *mut crate::leanh::LeanObject,
    mut v_lhs_5230_: *mut crate::leanh::LeanObject,
    mut v_rhs_5231_: *mut crate::leanh::LeanObject,
    mut v_s_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5233_ = l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___redArg(v_w_5226_, v_aig_5227_, v_curr_5228_, v_discr_5229_, v_lhs_5230_, v_rhs_5231_, v_s_5232_);
    crate::leanh::lean_dec_ref(v_rhs_5231_);
    crate::leanh::lean_dec_ref(v_lhs_5230_);
    crate::leanh::lean_dec(v_w_5226_);
    return v_res_5233_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(
    mut v_w_5234_: *mut crate::leanh::LeanObject,
    mut v_aig_5235_: *mut crate::leanh::LeanObject,
    mut v_input_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_discr_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_discr_5237_ = crate::leanh::lean_ctor_get(v_input_5236_, 0);
    crate::leanh::lean_inc_ref(v_discr_5237_);
    v_lhs_5238_ = crate::leanh::lean_ctor_get(v_input_5236_, 1);
    crate::leanh::lean_inc_ref(v_lhs_5238_);
    v_rhs_5239_ = crate::leanh::lean_ctor_get(v_input_5236_, 2);
    crate::leanh::lean_inc_ref(v_rhs_5239_);
    crate::leanh::lean_dec_ref(v_input_5236_);
    v___x_5240_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5241_ = lean_mk_empty_array_with_capacity(v_w_5234_);
    v___x_5242_ = l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___redArg(v_w_5234_, v_aig_5235_, v___x_5240_, v_discr_5237_, v_lhs_5238_, v_rhs_5239_, v___x_5241_);
    crate::leanh::lean_dec_ref(v_rhs_5239_);
    crate::leanh::lean_dec_ref(v_lhs_5238_);
    return v___x_5242_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29___boxed(
    mut v_w_5243_: *mut crate::leanh::LeanObject,
    mut v_aig_5244_: *mut crate::leanh::LeanObject,
    mut v_input_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5246_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_5243_, v_aig_5244_, v_input_5245_);
    crate::leanh::lean_dec(v_w_5243_);
    return v_res_5246_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___redArg(
    mut v_w_5247_: *mut crate::leanh::LeanObject,
    mut v_input_5248_: *mut crate::leanh::LeanObject,
    mut v_distance_5249_: *mut crate::leanh::LeanObject,
    mut v_curr_5250_: *mut crate::leanh::LeanObject,
    mut v_s_5251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5269_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: u8 = 0;
    let mut v_ref_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: u8 = 0;
    let mut v___x_5289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5263_ = lean_nat_dec_lt(v_curr_5250_, v_w_5247_);
                if v___x_5263_ == 0 {
                    crate::leanh::lean_dec(v_curr_5250_);
                    return v_s_5251_;
                } else {
                    v___x_5264_ = lean_nat_add(v_distance_5249_, v_curr_5250_);
                    v___x_5265_ = lean_nat_dec_lt(v___x_5264_, v_w_5247_);
                    if v___x_5265_ == 0 {
                        crate::leanh::lean_dec(v___x_5264_);
                        v___x_5266_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5277_ = lean_nat_sub(v_w_5247_, v___x_5266_);
                        v_ref_5278_ = lean_array_fget_borrowed(v_input_5248_, v___x_5277_);
                        crate::leanh::lean_dec(v___x_5277_);
                        v___x_5279_ = lean_nat_shiftr(v_ref_5278_, v___x_5266_);
                        v___x_5280_ = lean_nat_land(v___x_5266_, v_ref_5278_);
                        v___x_5281_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5282_ = lean_nat_dec_eq(v___x_5280_, v___x_5281_);
                        crate::leanh::lean_dec(v___x_5280_);
                        if v___x_5282_ == 0 {
                            v_gate_5268_ = v___x_5279_;
                            v_invert_5269_ = v___x_5263_;
                            state = 2;
                            continue;
                        } else {
                            v_gate_5268_ = v___x_5279_;
                            v_invert_5269_ = v___x_5265_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_ref_5283_ = lean_array_fget_borrowed(v_input_5248_, v___x_5264_);
                        crate::leanh::lean_dec(v___x_5264_);
                        v___x_5284_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5285_ = lean_nat_shiftr(v_ref_5283_, v___x_5284_);
                        v___x_5286_ = lean_nat_land(v___x_5284_, v_ref_5283_);
                        v___x_5287_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5288_ = lean_nat_dec_eq(v___x_5286_, v___x_5287_);
                        crate::leanh::lean_dec(v___x_5286_);
                        if v___x_5288_ == 0 {
                            v_gate_5253_ = v___x_5285_;
                            v_invert_5254_ = v___x_5265_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5289_ = 0;
                            v_gate_5253_ = v___x_5285_;
                            v_invert_5254_ = v___x_5289_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5255_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5256_ = lean_nat_add(v_curr_5250_, v___x_5255_);
                crate::leanh::lean_dec(v_curr_5250_);
                v___x_5257_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5258_ = lean_nat_mul(v_gate_5253_, v___x_5257_);
                crate::leanh::lean_dec(v_gate_5253_);
                v___x_5259_ = l_Bool_toNat(v_invert_5254_);
                v___x_5260_ = lean_nat_lor(v___x_5258_, v___x_5259_);
                crate::leanh::lean_dec(v___x_5259_);
                crate::leanh::lean_dec(v___x_5258_);
                v_s_5261_ = lean_array_push(v_s_5251_, v___x_5260_);
                v_curr_5250_ = v___x_5256_;
                v_s_5251_ = v_s_5261_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5270_ = lean_nat_add(v_curr_5250_, v___x_5266_);
                crate::leanh::lean_dec(v_curr_5250_);
                v___x_5271_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5272_ = lean_nat_mul(v_gate_5268_, v___x_5271_);
                crate::leanh::lean_dec(v_gate_5268_);
                v___x_5273_ = l_Bool_toNat(v_invert_5269_);
                v___x_5274_ = lean_nat_lor(v___x_5272_, v___x_5273_);
                crate::leanh::lean_dec(v___x_5273_);
                crate::leanh::lean_dec(v___x_5272_);
                v_s_5275_ = lean_array_push(v_s_5251_, v___x_5274_);
                v_curr_5250_ = v___x_5270_;
                v_s_5251_ = v_s_5275_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___redArg___boxed(
    mut v_w_5290_: *mut crate::leanh::LeanObject,
    mut v_input_5291_: *mut crate::leanh::LeanObject,
    mut v_distance_5292_: *mut crate::leanh::LeanObject,
    mut v_curr_5293_: *mut crate::leanh::LeanObject,
    mut v_s_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5295_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___redArg(v_w_5290_, v_input_5291_, v_distance_5292_, v_curr_5293_, v_s_5294_);
    crate::leanh::lean_dec(v_distance_5292_);
    crate::leanh::lean_dec_ref(v_input_5291_);
    crate::leanh::lean_dec(v_w_5290_);
    return v_res_5295_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18(
    mut v_w_5296_: *mut crate::leanh::LeanObject,
    mut v_aig_5297_: *mut crate::leanh::LeanObject,
    mut v_target_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vec_5299_ = crate::leanh::lean_ctor_get(v_target_5298_, 0);
                v_distance_5300_ = crate::leanh::lean_ctor_get(v_target_5298_, 1);
                v_isSharedCheck_5310_ = (!crate::leanh::lean_is_exclusive(v_target_5298_)) as u8;
                if v_isSharedCheck_5310_ == 0 {
                    v___x_5302_ = v_target_5298_;
                    v_isShared_5303_ = v_isSharedCheck_5310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_distance_5300_);
                    crate::leanh::lean_inc(v_vec_5299_);
                    crate::leanh::lean_dec(v_target_5298_);
                    v___x_5302_ = crate::leanh::lean_box(0);
                    v_isShared_5303_ = v_isSharedCheck_5310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5304_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5305_ = lean_mk_empty_array_with_capacity(v_w_5296_);
                v___x_5306_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___redArg(v_w_5296_, v_vec_5299_, v_distance_5300_, v___x_5304_, v___x_5305_);
                crate::leanh::lean_dec(v_distance_5300_);
                crate::leanh::lean_dec_ref(v_vec_5299_);
                if v_isShared_5303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5302_, 1, v___x_5306_);
                    crate::leanh::lean_ctor_set(v___x_5302_, 0, v_aig_5297_);
                    v___x_5308_ = v___x_5302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_aig_5297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 1, v___x_5306_);
                    v___x_5308_ = v_reuseFailAlloc_5309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18___boxed(
    mut v_w_5311_: *mut crate::leanh::LeanObject,
    mut v_aig_5312_: *mut crate::leanh::LeanObject,
    mut v_target_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18(v_w_5311_, v_aig_5312_, v_target_5313_);
    crate::leanh::lean_dec(v_w_5311_);
    return v_res_5314_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__56(
    mut v_w_5315_: *mut crate::leanh::LeanObject,
    mut v_aig_5316_: *mut crate::leanh::LeanObject,
    mut v_target_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: u8 = 0;
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_5318_ = crate::leanh::lean_ctor_get(v_target_5317_, 0);
                v_lhs_5319_ = crate::leanh::lean_ctor_get(v_target_5317_, 1);
                v_rhs_5320_ = crate::leanh::lean_ctor_get(v_target_5317_, 2);
                v_pow_5321_ = crate::leanh::lean_ctor_get(v_target_5317_, 3);
                v___x_5322_ = lean_nat_dec_lt(v_pow_5321_, v_n_5318_);
                if v___x_5322_ == 0 {
                    crate::leanh::lean_inc_ref(v_lhs_5319_);
                    v___x_5323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5323_, 0, v_aig_5316_);
                    crate::leanh::lean_ctor_set(v___x_5323_, 1, v_lhs_5319_);
                    return v___x_5323_;
                } else {
                    v___x_5324_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_5325_ = lean_nat_pow(v___x_5324_, v_pow_5321_);
                    crate::leanh::lean_inc_ref(v_lhs_5319_);
                    v___x_5326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5326_, 0, v_lhs_5319_);
                    crate::leanh::lean_ctor_set(v___x_5326_, 1, v___x_5325_);
                    v_res_5327_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18(v_w_5315_, v_aig_5316_, v___x_5326_);
                    v_aig_5328_ = crate::leanh::lean_ctor_get(v_res_5327_, 0);
                    crate::leanh::lean_inc_ref(v_aig_5328_);
                    v_vec_5329_ = crate::leanh::lean_ctor_get(v_res_5327_, 1);
                    crate::leanh::lean_inc_ref(v_vec_5329_);
                    crate::leanh::lean_dec_ref(v_res_5327_);
                    v_ref_5334_ = lean_array_fget_borrowed(v_rhs_5320_, v_pow_5321_);
                    v___x_5335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5336_ = lean_nat_shiftr(v_ref_5334_, v___x_5335_);
                    v___x_5337_ = lean_nat_land(v___x_5335_, v_ref_5334_);
                    v___x_5338_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5339_ = lean_nat_dec_eq(v___x_5337_, v___x_5338_);
                    crate::leanh::lean_dec(v___x_5337_);
                    if v___x_5339_ == 0 {
                        v___x_5340_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5340_, 0, v___x_5336_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5340_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5322_,
                        );
                        v___y_5331_ = v___x_5340_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5341_ = 0;
                        v___x_5342_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5342_, 0, v___x_5336_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5342_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5341_,
                        );
                        v___y_5331_ = v___x_5342_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_5319_);
                v___x_5332_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5332_, 0, v___y_5331_);
                crate::leanh::lean_ctor_set(v___x_5332_, 1, v_vec_5329_);
                crate::leanh::lean_ctor_set(v___x_5332_, 2, v_lhs_5319_);
                v___x_5333_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_5315_, v_aig_5328_, v___x_5332_);
                return v___x_5333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__56___boxed(
    mut v_w_5343_: *mut crate::leanh::LeanObject,
    mut v_aig_5344_: *mut crate::leanh::LeanObject,
    mut v_target_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5346_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__56(v_w_5343_, v_aig_5344_, v_target_5345_);
    crate::leanh::lean_dec_ref(v_target_5345_);
    crate::leanh::lean_dec(v_w_5343_);
    return v_res_5346_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__57(
    mut v_w_5347_: *mut crate::leanh::LeanObject,
    mut v_n_5348_: *mut crate::leanh::LeanObject,
    mut v_aig_5349_: *mut crate::leanh::LeanObject,
    mut v_distance_5350_: *mut crate::leanh::LeanObject,
    mut v_curr_5351_: *mut crate::leanh::LeanObject,
    mut v_acc_5352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5353_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5354_ = lean_nat_sub(v_n_5348_, v___x_5353_);
                v___x_5355_ = lean_nat_dec_lt(v_curr_5351_, v___x_5354_);
                crate::leanh::lean_dec(v___x_5354_);
                if v___x_5355_ == 0 {
                    crate::leanh::lean_dec(v_curr_5351_);
                    crate::leanh::lean_dec_ref(v_distance_5350_);
                    crate::leanh::lean_dec(v_n_5348_);
                    v___x_5356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5356_, 0, v_aig_5349_);
                    crate::leanh::lean_ctor_set(v___x_5356_, 1, v_acc_5352_);
                    return v___x_5356_;
                } else {
                    v___x_5357_ = lean_nat_add(v_curr_5351_, v___x_5353_);
                    crate::leanh::lean_dec(v_curr_5351_);
                    crate::leanh::lean_inc(v___x_5357_);
                    crate::leanh::lean_inc_ref(v_distance_5350_);
                    crate::leanh::lean_inc(v_n_5348_);
                    v___x_5358_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5358_, 0, v_n_5348_);
                    crate::leanh::lean_ctor_set(v___x_5358_, 1, v_acc_5352_);
                    crate::leanh::lean_ctor_set(v___x_5358_, 2, v_distance_5350_);
                    crate::leanh::lean_ctor_set(v___x_5358_, 3, v___x_5357_);
                    v_res_5359_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__56(v_w_5347_, v_aig_5349_, v___x_5358_);
                    crate::leanh::lean_dec_ref_known(v___x_5358_, 4);
                    v_aig_5360_ = crate::leanh::lean_ctor_get(v_res_5359_, 0);
                    crate::leanh::lean_inc_ref(v_aig_5360_);
                    v_vec_5361_ = crate::leanh::lean_ctor_get(v_res_5359_, 1);
                    crate::leanh::lean_inc_ref(v_vec_5361_);
                    crate::leanh::lean_dec_ref(v_res_5359_);
                    v_aig_5349_ = v_aig_5360_;
                    v_curr_5351_ = v___x_5357_;
                    v_acc_5352_ = v_vec_5361_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__57___boxed(
    mut v_w_5363_: *mut crate::leanh::LeanObject,
    mut v_n_5364_: *mut crate::leanh::LeanObject,
    mut v_aig_5365_: *mut crate::leanh::LeanObject,
    mut v_distance_5366_: *mut crate::leanh::LeanObject,
    mut v_curr_5367_: *mut crate::leanh::LeanObject,
    mut v_acc_5368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5369_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__57(v_w_5363_, v_n_5364_, v_aig_5365_, v_distance_5366_, v_curr_5367_, v_acc_5368_);
    crate::leanh::lean_dec(v_w_5363_);
    return v_res_5369_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26(
    mut v_w_5370_: *mut crate::leanh::LeanObject,
    mut v_aig_5371_: *mut crate::leanh::LeanObject,
    mut v_target_5372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    v_n_5373_ = crate::leanh::lean_ctor_get(v_target_5372_, 0);
    crate::leanh::lean_inc(v_n_5373_);
    v_target_5374_ = crate::leanh::lean_ctor_get(v_target_5372_, 1);
    crate::leanh::lean_inc_ref(v_target_5374_);
    v_distance_5375_ = crate::leanh::lean_ctor_get(v_target_5372_, 2);
    crate::leanh::lean_inc_ref(v_distance_5375_);
    crate::leanh::lean_dec_ref(v_target_5372_);
    v___x_5376_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5377_ = lean_nat_dec_eq(v_n_5373_, v___x_5376_);
    if v___x_5377_ == 0 {
        let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_5375_);
        crate::leanh::lean_inc(v_n_5373_);
        v___x_5378_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5378_, 0, v_n_5373_);
        crate::leanh::lean_ctor_set(v___x_5378_, 1, v_target_5374_);
        crate::leanh::lean_ctor_set(v___x_5378_, 2, v_distance_5375_);
        crate::leanh::lean_ctor_set(v___x_5378_, 3, v___x_5376_);
        v_res_5379_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__56(v_w_5370_, v_aig_5371_, v___x_5378_);
        crate::leanh::lean_dec_ref_known(v___x_5378_, 4);
        v_aig_5380_ = crate::leanh::lean_ctor_get(v_res_5379_, 0);
        crate::leanh::lean_inc_ref(v_aig_5380_);
        v_vec_5381_ = crate::leanh::lean_ctor_get(v_res_5379_, 1);
        crate::leanh::lean_inc_ref(v_vec_5381_);
        crate::leanh::lean_dec_ref(v_res_5379_);
        v___x_5382_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26_spec__57(v_w_5370_, v_n_5373_, v_aig_5380_, v_distance_5375_, v___x_5376_, v_vec_5381_);
        return v___x_5382_;
    } else {
        let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_5375_);
        crate::leanh::lean_dec(v_n_5373_);
        v___x_5383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5383_, 0, v_aig_5371_);
        crate::leanh::lean_ctor_set(v___x_5383_, 1, v_target_5374_);
        return v___x_5383_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26___boxed(
    mut v_w_5384_: *mut crate::leanh::LeanObject,
    mut v_aig_5385_: *mut crate::leanh::LeanObject,
    mut v_target_5386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5387_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26(v_w_5384_, v_aig_5385_, v_target_5386_);
    crate::leanh::lean_dec(v_w_5384_);
    return v_res_5387_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___redArg(
    mut v_w_5388_: *mut crate::leanh::LeanObject,
    mut v_val_5389_: *mut crate::leanh::LeanObject,
    mut v_curr_5390_: *mut crate::leanh::LeanObject,
    mut v_s_5391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: u8 = 0;
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5392_ = lean_nat_dec_lt(v_curr_5390_, v_w_5388_);
                if v___x_5392_ == 0 {
                    crate::leanh::lean_dec(v_curr_5390_);
                    return v_s_5391_;
                } else {
                    v___x_5393_ = l_Nat_testBit(v_val_5389_, v_curr_5390_);
                    v___x_5394_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5395_ = lean_nat_add(v_curr_5390_, v___x_5394_);
                    crate::leanh::lean_dec(v_curr_5390_);
                    v___x_5396_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5397_ = l_Bool_toNat(v___x_5393_);
                    v___x_5398_ = lean_nat_lor(v___x_5396_, v___x_5397_);
                    crate::leanh::lean_dec(v___x_5397_);
                    v_s_5399_ = lean_array_push(v_s_5391_, v___x_5398_);
                    v_curr_5390_ = v___x_5395_;
                    v_s_5391_ = v_s_5399_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___redArg___boxed(
    mut v_w_5401_: *mut crate::leanh::LeanObject,
    mut v_val_5402_: *mut crate::leanh::LeanObject,
    mut v_curr_5403_: *mut crate::leanh::LeanObject,
    mut v_s_5404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5405_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___redArg(v_w_5401_, v_val_5402_, v_curr_5403_, v_s_5404_);
    crate::leanh::lean_dec(v_val_5402_);
    crate::leanh::lean_dec(v_w_5401_);
    return v_res_5405_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(
    mut v_w_5406_: *mut crate::leanh::LeanObject,
    mut v_aig_5407_: *mut crate::leanh::LeanObject,
    mut v_val_5408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5409_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5410_ = lean_mk_empty_array_with_capacity(v_w_5406_);
    v___x_5411_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___redArg(v_w_5406_, v_val_5408_, v___x_5409_, v___x_5410_);
    return v___x_5411_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3___boxed(
    mut v_w_5412_: *mut crate::leanh::LeanObject,
    mut v_aig_5413_: *mut crate::leanh::LeanObject,
    mut v_val_5414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5415_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_5412_, v_aig_5413_, v_val_5414_);
    crate::leanh::lean_dec(v_val_5414_);
    crate::leanh::lean_dec_ref(v_aig_5413_);
    crate::leanh::lean_dec(v_w_5412_);
    return v_res_5415_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___redArg(
    mut v___x_5416_: *mut crate::leanh::LeanObject,
    mut v_len_5417_: *mut crate::leanh::LeanObject,
    mut v_aig_5418_: *mut crate::leanh::LeanObject,
    mut v_idx_5419_: *mut crate::leanh::LeanObject,
    mut v_s_5420_: *mut crate::leanh::LeanObject,
    mut v_input_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5428_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: u8 = 0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5437_ = lean_nat_dec_lt(v_idx_5419_, v_len_5417_);
                if v___x_5437_ == 0 {
                    crate::leanh::lean_dec(v_idx_5419_);
                    crate::leanh::lean_dec_ref(v___x_5416_);
                    v___x_5438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5438_, 0, v_aig_5418_);
                    crate::leanh::lean_ctor_set(v___x_5438_, 1, v_s_5420_);
                    return v___x_5438_;
                } else {
                    v_ref_5439_ = lean_array_fget_borrowed(v_input_5421_, v_idx_5419_);
                    v___x_5440_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5441_ = lean_nat_shiftr(v_ref_5439_, v___x_5440_);
                    v___x_5442_ = lean_nat_land(v___x_5440_, v_ref_5439_);
                    v___x_5443_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5444_ = lean_nat_dec_eq(v___x_5442_, v___x_5443_);
                    crate::leanh::lean_dec(v___x_5442_);
                    if v___x_5444_ == 0 {
                        v___x_5445_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5441_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5445_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5437_,
                        );
                        v___y_5423_ = v___x_5445_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5446_ = 0;
                        v___x_5447_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5447_, 0, v___x_5441_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5447_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5446_,
                        );
                        v___y_5423_ = v___x_5447_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_5416_);
                v_res_5424_ = crate::leanh::lean_apply_2(v___x_5416_, v_aig_5418_, v___y_5423_);
                v_ref_5425_ = crate::leanh::lean_ctor_get(v_res_5424_, 1);
                crate::leanh::lean_inc_ref(v_ref_5425_);
                v_aig_5426_ = crate::leanh::lean_ctor_get(v_res_5424_, 0);
                crate::leanh::lean_inc_ref(v_aig_5426_);
                crate::leanh::lean_dec_ref(v_res_5424_);
                v_gate_5427_ = crate::leanh::lean_ctor_get(v_ref_5425_, 0);
                crate::leanh::lean_inc(v_gate_5427_);
                v_invert_5428_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5425_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_5425_);
                v___x_5429_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5430_ = lean_nat_add(v_idx_5419_, v___x_5429_);
                crate::leanh::lean_dec(v_idx_5419_);
                v___x_5431_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5432_ = lean_nat_mul(v_gate_5427_, v___x_5431_);
                crate::leanh::lean_dec(v_gate_5427_);
                v___x_5433_ = l_Bool_toNat(v_invert_5428_);
                v___x_5434_ = lean_nat_lor(v___x_5432_, v___x_5433_);
                crate::leanh::lean_dec(v___x_5433_);
                crate::leanh::lean_dec(v___x_5432_);
                v_s_5435_ = lean_array_push(v_s_5420_, v___x_5434_);
                v_aig_5418_ = v_aig_5426_;
                v_idx_5419_ = v___x_5430_;
                v_s_5420_ = v_s_5435_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___redArg___boxed(
    mut v___x_5448_: *mut crate::leanh::LeanObject,
    mut v_len_5449_: *mut crate::leanh::LeanObject,
    mut v_aig_5450_: *mut crate::leanh::LeanObject,
    mut v_idx_5451_: *mut crate::leanh::LeanObject,
    mut v_s_5452_: *mut crate::leanh::LeanObject,
    mut v_input_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___redArg(v___x_5448_, v_len_5449_, v_aig_5450_, v_idx_5451_, v_s_5452_, v_input_5453_);
    crate::leanh::lean_dec_ref(v_input_5453_);
    crate::leanh::lean_dec(v_len_5449_);
    return v_res_5454_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32(
    mut v_len_5455_: *mut crate::leanh::LeanObject,
    mut v_aig_5456_: *mut crate::leanh::LeanObject,
    mut v_target_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_func_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_5458_ = crate::leanh::lean_ctor_get(v_target_5457_, 0);
    crate::leanh::lean_inc_ref(v_vec_5458_);
    v_func_5459_ = crate::leanh::lean_ctor_get(v_target_5457_, 1);
    crate::leanh::lean_inc_ref(v_func_5459_);
    crate::leanh::lean_dec_ref(v_target_5457_);
    v___x_5460_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5461_ = lean_mk_empty_array_with_capacity(v_len_5455_);
    v___x_5462_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___redArg(v_func_5459_, v_len_5455_, v_aig_5456_, v___x_5460_, v___x_5461_, v_vec_5458_);
    crate::leanh::lean_dec_ref(v_vec_5458_);
    return v___x_5462_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32___boxed(
    mut v_len_5463_: *mut crate::leanh::LeanObject,
    mut v_aig_5464_: *mut crate::leanh::LeanObject,
    mut v_target_5465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5466_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32(v_len_5463_, v_aig_5464_, v_target_5465_);
    crate::leanh::lean_dec(v_len_5463_);
    return v_res_5466_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___lam__0(
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_invert_5469_: u8 = 0;
    let mut v_gate_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5473_: u8 = 0;
    let mut v___x_5474_: u8 = 0;
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v_gate_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5484_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_5469_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5468_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5469_ == 0 {
                    v_gate_5470_ = crate::leanh::lean_ctor_get(v___y_5468_, 0);
                    v_isSharedCheck_5479_ = (!crate::leanh::lean_is_exclusive(v___y_5468_)) as u8;
                    if v_isSharedCheck_5479_ == 0 {
                        v___x_5472_ = v___y_5468_;
                        v_isShared_5473_ = v_isSharedCheck_5479_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5470_);
                        crate::leanh::lean_dec(v___y_5468_);
                        v___x_5472_ = crate::leanh::lean_box(0);
                        v_isShared_5473_ = v_isSharedCheck_5479_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_5480_ = crate::leanh::lean_ctor_get(v___y_5468_, 0);
                    v_isSharedCheck_5489_ = (!crate::leanh::lean_is_exclusive(v___y_5468_)) as u8;
                    if v_isSharedCheck_5489_ == 0 {
                        v___x_5482_ = v___y_5468_;
                        v_isShared_5483_ = v_isSharedCheck_5489_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5480_);
                        crate::leanh::lean_dec(v___y_5468_);
                        v___x_5482_ = crate::leanh::lean_box(0);
                        v_isShared_5483_ = v_isSharedCheck_5489_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5474_ = 1;
                if v_isShared_5473_ == 0 {
                    v___x_5476_ = v___x_5472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5478_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_gate_5470_);
                    v___x_5476_ = v_reuseFailAlloc_5478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5476_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5474_,
                );
                v___x_5477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5477_, 0, v___y_5467_);
                crate::leanh::lean_ctor_set(v___x_5477_, 1, v___x_5476_);
                return v___x_5477_;
            }
            3 => {
                v___x_5484_ = 0;
                if v_isShared_5483_ == 0 {
                    v___x_5486_ = v___x_5482_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5488_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_gate_5480_);
                    v___x_5486_ = v_reuseFailAlloc_5488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5486_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5484_,
                );
                v___x_5487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5487_, 0, v___y_5467_);
                crate::leanh::lean_ctor_set(v___x_5487_, 1, v___x_5486_);
                return v___x_5487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15(
    mut v_w_5491_: *mut crate::leanh::LeanObject,
    mut v_aig_5492_: *mut crate::leanh::LeanObject,
    mut v_s_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5494_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___closed__0;
    v___x_5495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5495_, 0, v_s_5493_);
    crate::leanh::lean_ctor_set(v___x_5495_, 1, v___f_5494_);
    v___x_5496_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32(v_w_5491_, v_aig_5492_, v___x_5495_);
    return v___x_5496_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15___boxed(
    mut v_w_5497_: *mut crate::leanh::LeanObject,
    mut v_aig_5498_: *mut crate::leanh::LeanObject,
    mut v_s_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15(v_w_5497_, v_aig_5498_, v_s_5499_);
    crate::leanh::lean_dec(v_w_5497_);
    return v_res_5500_;
}
pub unsafe fn l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(
    mut v_aig_5501_: *mut crate::leanh::LeanObject,
    mut v_input_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5513_: u8 = 0;
    let mut v_gate_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5517_: u8 = 0;
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_gate_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5527_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_res_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5538_: u8 = 0;
    let mut v_aig_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5545_: u8 = 0;
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5549_: u8 = 0;
    let mut v_aig_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5555_: u8 = 0;
    let mut v___x_5556_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_lhs_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5565_: u8 = 0;
    let mut v_gate_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5567_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v_gate_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5572_: u8 = 0;
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___y_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: u8 = 0;
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: u8 = 0;
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: u8 = 0;
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5600_: u8 = 0;
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_input_5502_);
                v_res_5532_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5501_, v_input_5502_);
                v_aig_5533_ = crate::leanh::lean_ctor_get(v_res_5532_, 0);
                crate::leanh::lean_inc_ref(v_aig_5533_);
                v_ref_5534_ = crate::leanh::lean_ctor_get(v_res_5532_, 1);
                crate::leanh::lean_inc_ref(v_ref_5534_);
                crate::leanh::lean_dec_ref(v_res_5532_);
                v_lhs_5561_ = crate::leanh::lean_ctor_get(v_input_5502_, 0);
                v_rhs_5562_ = crate::leanh::lean_ctor_get(v_input_5502_, 1);
                v_isSharedCheck_5602_ = (!crate::leanh::lean_is_exclusive(v_input_5502_)) as u8;
                if v_isSharedCheck_5602_ == 0 {
                    v___x_5564_ = v_input_5502_;
                    v_isShared_5565_ = v_isSharedCheck_5602_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_5562_);
                    crate::leanh::lean_inc(v_lhs_5561_);
                    crate::leanh::lean_dec(v_input_5502_);
                    v___x_5564_ = crate::leanh::lean_box(0);
                    v_isShared_5565_ = v_isSharedCheck_5602_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_5507_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5507_, 0, v___y_5505_);
                crate::leanh::lean_ctor_set(v___x_5507_, 1, v___y_5506_);
                v___x_5508_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v___y_5504_, v___x_5507_);
                return v___x_5508_;
            }
            2 => {
                v_invert_5513_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5511_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5513_ == 0 {
                    v_gate_5514_ = crate::leanh::lean_ctor_get(v___y_5511_, 0);
                    v_isSharedCheck_5522_ = (!crate::leanh::lean_is_exclusive(v___y_5511_)) as u8;
                    if v_isSharedCheck_5522_ == 0 {
                        v___x_5516_ = v___y_5511_;
                        v_isShared_5517_ = v_isSharedCheck_5522_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5514_);
                        crate::leanh::lean_dec(v___y_5511_);
                        v___x_5516_ = crate::leanh::lean_box(0);
                        v_isShared_5517_ = v_isSharedCheck_5522_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_5523_ = crate::leanh::lean_ctor_get(v___y_5511_, 0);
                    v_isSharedCheck_5531_ = (!crate::leanh::lean_is_exclusive(v___y_5511_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v___x_5525_ = v___y_5511_;
                        v_isShared_5526_ = v_isSharedCheck_5531_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5523_);
                        crate::leanh::lean_dec(v___y_5511_);
                        v___x_5525_ = crate::leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5531_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5518_ = 1;
                if v_isShared_5517_ == 0 {
                    v___x_5520_ = v___x_5516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5521_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_gate_5514_);
                    v___x_5520_ = v_reuseFailAlloc_5521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5518_,
                );
                v___y_5504_ = v___y_5510_;
                v___y_5505_ = v___y_5512_;
                v___y_5506_ = v___x_5520_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5527_ = 0;
                if v_isShared_5526_ == 0 {
                    v___x_5529_ = v___x_5525_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_gate_5523_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5529_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5527_,
                );
                v___y_5504_ = v___y_5510_;
                v___y_5505_ = v___y_5512_;
                v___y_5506_ = v___x_5529_;
                state = 1;
                continue;
            }
            7 => {
                v_res_5537_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5533_, v___y_5536_);
                v_invert_5538_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5534_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5538_ == 0 {
                    v_aig_5539_ = crate::leanh::lean_ctor_get(v_res_5537_, 0);
                    crate::leanh::lean_inc_ref(v_aig_5539_);
                    v_ref_5540_ = crate::leanh::lean_ctor_get(v_res_5537_, 1);
                    crate::leanh::lean_inc_ref(v_ref_5540_);
                    crate::leanh::lean_dec_ref(v_res_5537_);
                    v_gate_5541_ = crate::leanh::lean_ctor_get(v_ref_5534_, 0);
                    v_isSharedCheck_5549_ = (!crate::leanh::lean_is_exclusive(v_ref_5534_)) as u8;
                    if v_isSharedCheck_5549_ == 0 {
                        v___x_5543_ = v_ref_5534_;
                        v_isShared_5544_ = v_isSharedCheck_5549_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5541_);
                        crate::leanh::lean_dec(v_ref_5534_);
                        v___x_5543_ = crate::leanh::lean_box(0);
                        v_isShared_5544_ = v_isSharedCheck_5549_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_5550_ = crate::leanh::lean_ctor_get(v_res_5537_, 0);
                    crate::leanh::lean_inc_ref(v_aig_5550_);
                    v_ref_5551_ = crate::leanh::lean_ctor_get(v_res_5537_, 1);
                    crate::leanh::lean_inc_ref(v_ref_5551_);
                    crate::leanh::lean_dec_ref(v_res_5537_);
                    v_gate_5552_ = crate::leanh::lean_ctor_get(v_ref_5534_, 0);
                    v_isSharedCheck_5560_ = (!crate::leanh::lean_is_exclusive(v_ref_5534_)) as u8;
                    if v_isSharedCheck_5560_ == 0 {
                        v___x_5554_ = v_ref_5534_;
                        v_isShared_5555_ = v_isSharedCheck_5560_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_5552_);
                        crate::leanh::lean_dec(v_ref_5534_);
                        v___x_5554_ = crate::leanh::lean_box(0);
                        v_isShared_5555_ = v_isSharedCheck_5560_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_5545_ = 1;
                if v_isShared_5544_ == 0 {
                    v___x_5547_ = v___x_5543_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5548_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_gate_5541_);
                    v___x_5547_ = v_reuseFailAlloc_5548_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5545_,
                );
                v___y_5510_ = v_aig_5539_;
                v___y_5511_ = v_ref_5540_;
                v___y_5512_ = v___x_5547_;
                state = 2;
                continue;
            }
            10 => {
                v___x_5556_ = 0;
                if v_isShared_5555_ == 0 {
                    v___x_5558_ = v___x_5554_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_gate_5552_);
                    v___x_5558_ = v_reuseFailAlloc_5559_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5556_,
                );
                v___y_5510_ = v_aig_5550_;
                v___y_5511_ = v_ref_5551_;
                v___y_5512_ = v___x_5558_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_5566_ = crate::leanh::lean_ctor_get(v_lhs_5561_, 0);
                v_invert_5567_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_5561_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5601_ = (!crate::leanh::lean_is_exclusive(v_lhs_5561_)) as u8;
                if v_isSharedCheck_5601_ == 0 {
                    v___x_5569_ = v_lhs_5561_;
                    v_isShared_5570_ = v_isSharedCheck_5601_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5566_);
                    crate::leanh::lean_dec(v_lhs_5561_);
                    v___x_5569_ = crate::leanh::lean_box(0);
                    v_isShared_5570_ = v_isSharedCheck_5601_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_5571_ = crate::leanh::lean_ctor_get(v_rhs_5562_, 0);
                v_invert_5572_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_5562_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5600_ = (!crate::leanh::lean_is_exclusive(v_rhs_5562_)) as u8;
                if v_isSharedCheck_5600_ == 0 {
                    v___x_5574_ = v_rhs_5562_;
                    v_isShared_5575_ = v_isSharedCheck_5600_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5571_);
                    crate::leanh::lean_dec(v_rhs_5562_);
                    v___x_5574_ = crate::leanh::lean_box(0);
                    v_isShared_5575_ = v_isSharedCheck_5600_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_invert_5567_ == 0 {
                    v___x_5592_ = 1;
                    if v_isShared_5570_ == 0 {
                        v___x_5594_ = v___x_5569_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5595_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_gate_5566_);
                        v___x_5594_ = v_reuseFailAlloc_5595_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_5596_ = 0;
                    if v_isShared_5570_ == 0 {
                        v___x_5598_ = v___x_5569_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_5599_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_gate_5566_);
                        v___x_5598_ = v_reuseFailAlloc_5599_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                if v_invert_5572_ == 0 {
                    v___x_5578_ = 1;
                    if v_isShared_5575_ == 0 {
                        v___x_5580_ = v___x_5574_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5584_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_gate_5571_);
                        v___x_5580_ = v_reuseFailAlloc_5584_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_5585_ = 0;
                    if v_isShared_5575_ == 0 {
                        v___x_5587_ = v___x_5574_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5591_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_gate_5571_);
                        v___x_5587_ = v_reuseFailAlloc_5591_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5578_,
                );
                if v_isShared_5565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5564_, 1, v___x_5580_);
                    crate::leanh::lean_ctor_set(v___x_5564_, 0, v___y_5577_);
                    v___x_5582_ = v___x_5564_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___y_5577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5580_);
                    v___x_5582_ = v_reuseFailAlloc_5583_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_5536_ = v___x_5582_;
                state = 7;
                continue;
            }
            18 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5585_,
                );
                if v_isShared_5565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5564_, 1, v___x_5587_);
                    crate::leanh::lean_ctor_set(v___x_5564_, 0, v___y_5577_);
                    v___x_5589_ = v___x_5564_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___y_5577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5587_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_5536_ = v___x_5589_;
                state = 7;
                continue;
            }
            20 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5592_,
                );
                v___y_5577_ = v___x_5594_;
                state = 15;
                continue;
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5596_,
                );
                v___y_5577_ = v___x_5598_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__75(
    mut v_aig_5603_: *mut crate::leanh::LeanObject,
    mut v_input_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v_gate_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5616_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5619_: u8 = 0;
    let mut v_gate_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5621_: u8 = 0;
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_gate_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5626_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5629_: u8 = 0;
    let mut v_cin_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v_lhs_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5651_: u8 = 0;
    let mut v_gate_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5653_: u8 = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v_lorRef_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut v_reuseFailAlloc_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5669_: u8 = 0;
    let mut v_reuseFailAlloc_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_isSharedCheck_5673_: u8 = 0;
    let mut v_isSharedCheck_5674_: u8 = 0;
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5605_ = crate::leanh::lean_ctor_get(v_input_5604_, 0);
                crate::leanh::lean_inc_ref_n(v_lhs_5605_, 2);
                v_rhs_5606_ = crate::leanh::lean_ctor_get(v_input_5604_, 1);
                crate::leanh::lean_inc_ref_n(v_rhs_5606_, 2);
                v_cin_5607_ = crate::leanh::lean_ctor_get(v_input_5604_, 2);
                crate::leanh::lean_inc_ref(v_cin_5607_);
                crate::leanh::lean_dec_ref(v_input_5604_);
                v___x_5608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5608_, 0, v_lhs_5605_);
                crate::leanh::lean_ctor_set(v___x_5608_, 1, v_rhs_5606_);
                v_res_5609_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(v_aig_5603_, v___x_5608_);
                v_aig_5610_ = crate::leanh::lean_ctor_get(v_res_5609_, 0);
                v_ref_5611_ = crate::leanh::lean_ctor_get(v_res_5609_, 1);
                v_isSharedCheck_5675_ = (!crate::leanh::lean_is_exclusive(v_res_5609_)) as u8;
                if v_isSharedCheck_5675_ == 0 {
                    v___x_5613_ = v_res_5609_;
                    v_isShared_5614_ = v_isSharedCheck_5675_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5611_);
                    crate::leanh::lean_inc(v_aig_5610_);
                    crate::leanh::lean_dec(v_res_5609_);
                    v___x_5613_ = crate::leanh::lean_box(0);
                    v_isShared_5614_ = v_isSharedCheck_5675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_5615_ = crate::leanh::lean_ctor_get(v_lhs_5605_, 0);
                v_invert_5616_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_5605_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5674_ = (!crate::leanh::lean_is_exclusive(v_lhs_5605_)) as u8;
                if v_isSharedCheck_5674_ == 0 {
                    v___x_5618_ = v_lhs_5605_;
                    v_isShared_5619_ = v_isSharedCheck_5674_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5615_);
                    crate::leanh::lean_dec(v_lhs_5605_);
                    v___x_5618_ = crate::leanh::lean_box(0);
                    v_isShared_5619_ = v_isSharedCheck_5674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_5620_ = crate::leanh::lean_ctor_get(v_rhs_5606_, 0);
                v_invert_5621_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_5606_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5673_ = (!crate::leanh::lean_is_exclusive(v_rhs_5606_)) as u8;
                if v_isSharedCheck_5673_ == 0 {
                    v___x_5623_ = v_rhs_5606_;
                    v_isShared_5624_ = v_isSharedCheck_5673_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5620_);
                    crate::leanh::lean_dec(v_rhs_5606_);
                    v___x_5623_ = crate::leanh::lean_box(0);
                    v_isShared_5624_ = v_isSharedCheck_5673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_5625_ = crate::leanh::lean_ctor_get(v_cin_5607_, 0);
                v_invert_5626_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_5607_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5672_ = (!crate::leanh::lean_is_exclusive(v_cin_5607_)) as u8;
                if v_isSharedCheck_5672_ == 0 {
                    v___x_5628_ = v_cin_5607_;
                    v_isShared_5629_ = v_isSharedCheck_5672_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5625_);
                    crate::leanh::lean_dec(v_cin_5607_);
                    v___x_5628_ = crate::leanh::lean_box(0);
                    v_isShared_5629_ = v_isSharedCheck_5672_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5629_ == 0 {
                    v_cin_5631_ = v___x_5628_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5671_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_gate_5625_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5671_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5626_,
                    );
                    v_cin_5631_ = v_reuseFailAlloc_5671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5613_, 1, v_cin_5631_);
                    crate::leanh::lean_ctor_set(v___x_5613_, 0, v_ref_5611_);
                    v___x_5633_ = v___x_5613_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_ref_5611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 1, v_cin_5631_);
                    v___x_5633_ = v_reuseFailAlloc_5670_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_res_5634_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5610_, v___x_5633_);
                v_aig_5635_ = crate::leanh::lean_ctor_get(v_res_5634_, 0);
                v_ref_5636_ = crate::leanh::lean_ctor_get(v_res_5634_, 1);
                v_isSharedCheck_5669_ = (!crate::leanh::lean_is_exclusive(v_res_5634_)) as u8;
                if v_isSharedCheck_5669_ == 0 {
                    v___x_5638_ = v_res_5634_;
                    v_isShared_5639_ = v_isSharedCheck_5669_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5636_);
                    crate::leanh::lean_inc(v_aig_5635_);
                    crate::leanh::lean_dec(v_res_5634_);
                    v___x_5638_ = crate::leanh::lean_box(0);
                    v_isShared_5639_ = v_isSharedCheck_5669_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5623_, 0, v_gate_5615_);
                    v_lhs_5641_ = v___x_5623_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5668_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_gate_5615_);
                    v_lhs_5641_ = v_reuseFailAlloc_5668_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_lhs_5641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_5616_,
                );
                if v_isShared_5619_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5618_, 0, v_gate_5620_);
                    v_rhs_5643_ = v___x_5618_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5667_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_gate_5620_);
                    v_rhs_5643_ = v_reuseFailAlloc_5667_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_rhs_5643_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_5621_,
                );
                if v_isShared_5639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5638_, 1, v_rhs_5643_);
                    crate::leanh::lean_ctor_set(v___x_5638_, 0, v_lhs_5641_);
                    v___x_5645_ = v___x_5638_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_lhs_5641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_rhs_5643_);
                    v___x_5645_ = v_reuseFailAlloc_5666_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_res_5646_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_5635_, v___x_5645_);
                v_aig_5647_ = crate::leanh::lean_ctor_get(v_res_5646_, 0);
                v_ref_5648_ = crate::leanh::lean_ctor_get(v_res_5646_, 1);
                v_isSharedCheck_5665_ = (!crate::leanh::lean_is_exclusive(v_res_5646_)) as u8;
                if v_isSharedCheck_5665_ == 0 {
                    v___x_5650_ = v_res_5646_;
                    v_isShared_5651_ = v_isSharedCheck_5665_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5648_);
                    crate::leanh::lean_inc(v_aig_5647_);
                    crate::leanh::lean_dec(v_res_5646_);
                    v___x_5650_ = crate::leanh::lean_box(0);
                    v_isShared_5651_ = v_isSharedCheck_5665_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_5652_ = crate::leanh::lean_ctor_get(v_ref_5636_, 0);
                v_invert_5653_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5636_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5664_ = (!crate::leanh::lean_is_exclusive(v_ref_5636_)) as u8;
                if v_isSharedCheck_5664_ == 0 {
                    v___x_5655_ = v_ref_5636_;
                    v_isShared_5656_ = v_isSharedCheck_5664_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5652_);
                    crate::leanh::lean_dec(v_ref_5636_);
                    v___x_5655_ = crate::leanh::lean_box(0);
                    v_isShared_5656_ = v_isSharedCheck_5664_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5656_ == 0 {
                    v_lorRef_5658_ = v___x_5655_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5663_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_gate_5652_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5663_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5653_,
                    );
                    v_lorRef_5658_ = v_reuseFailAlloc_5663_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5650_, 0, v_lorRef_5658_);
                    v___x_5660_ = v___x_5650_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_lorRef_5658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_ref_5648_);
                    v___x_5660_ = v_reuseFailAlloc_5662_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5661_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__7(v_aig_5647_, v___x_5660_);
                return v___x_5661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89_spec__98(
    mut v_w_5676_: *mut crate::leanh::LeanObject,
    mut v_aig_5677_: *mut crate::leanh::LeanObject,
    mut v_lhs_5678_: *mut crate::leanh::LeanObject,
    mut v_rhs_5679_: *mut crate::leanh::LeanObject,
    mut v_curr_5680_: *mut crate::leanh::LeanObject,
    mut v_cin_5681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: u8 = 0;
    let mut v___y_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: u8 = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: u8 = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5692_ = lean_nat_dec_lt(v_curr_5680_, v_w_5676_);
                if v___x_5692_ == 0 {
                    crate::leanh::lean_dec(v_curr_5680_);
                    v___x_5704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5704_, 0, v_aig_5677_);
                    crate::leanh::lean_ctor_set(v___x_5704_, 1, v_cin_5681_);
                    return v___x_5704_;
                } else {
                    v_ref_5705_ = lean_array_fget_borrowed(v_lhs_5678_, v_curr_5680_);
                    v___x_5706_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5707_ = lean_nat_shiftr(v_ref_5705_, v___x_5706_);
                    v___x_5708_ = lean_nat_land(v___x_5706_, v_ref_5705_);
                    v___x_5709_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5710_ = lean_nat_dec_eq(v___x_5708_, v___x_5709_);
                    crate::leanh::lean_dec(v___x_5708_);
                    if v___x_5710_ == 0 {
                        v___x_5711_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5711_, 0, v___x_5707_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5711_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5692_,
                        );
                        v___y_5694_ = v___x_5711_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5712_ = 0;
                        v___x_5713_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5713_, 0, v___x_5707_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5713_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5712_,
                        );
                        v___y_5694_ = v___x_5713_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5685_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5685_, 0, v___y_5683_);
                crate::leanh::lean_ctor_set(v___x_5685_, 1, v___y_5684_);
                crate::leanh::lean_ctor_set(v___x_5685_, 2, v_cin_5681_);
                v_res_5686_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__75(v_aig_5677_, v___x_5685_);
                v_aig_5687_ = crate::leanh::lean_ctor_get(v_res_5686_, 0);
                crate::leanh::lean_inc_ref(v_aig_5687_);
                v_ref_5688_ = crate::leanh::lean_ctor_get(v_res_5686_, 1);
                crate::leanh::lean_inc_ref(v_ref_5688_);
                crate::leanh::lean_dec_ref(v_res_5686_);
                v___x_5689_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5690_ = lean_nat_add(v_curr_5680_, v___x_5689_);
                crate::leanh::lean_dec(v_curr_5680_);
                v_aig_5677_ = v_aig_5687_;
                v_curr_5680_ = v___x_5690_;
                v_cin_5681_ = v_ref_5688_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_5695_ = lean_array_fget_borrowed(v_rhs_5679_, v_curr_5680_);
                v___x_5696_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5697_ = lean_nat_shiftr(v_ref_5695_, v___x_5696_);
                v___x_5698_ = lean_nat_land(v___x_5696_, v_ref_5695_);
                v___x_5699_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5700_ = lean_nat_dec_eq(v___x_5698_, v___x_5699_);
                crate::leanh::lean_dec(v___x_5698_);
                if v___x_5700_ == 0 {
                    v___x_5701_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5701_, 0, v___x_5697_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5701_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5692_,
                    );
                    v___y_5683_ = v___y_5694_;
                    v___y_5684_ = v___x_5701_;
                    state = 1;
                    continue;
                } else {
                    v___x_5702_ = 0;
                    v___x_5703_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5703_, 0, v___x_5697_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5703_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5702_,
                    );
                    v___y_5683_ = v___y_5694_;
                    v___y_5684_ = v___x_5703_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89_spec__98___boxed(
    mut v_w_5714_: *mut crate::leanh::LeanObject,
    mut v_aig_5715_: *mut crate::leanh::LeanObject,
    mut v_lhs_5716_: *mut crate::leanh::LeanObject,
    mut v_rhs_5717_: *mut crate::leanh::LeanObject,
    mut v_curr_5718_: *mut crate::leanh::LeanObject,
    mut v_cin_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89_spec__98(v_w_5714_, v_aig_5715_, v_lhs_5716_, v_rhs_5717_, v_curr_5718_, v_cin_5719_);
    crate::leanh::lean_dec_ref(v_rhs_5717_);
    crate::leanh::lean_dec_ref(v_lhs_5716_);
    crate::leanh::lean_dec(v_w_5714_);
    return v_res_5720_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89(
    mut v_aig_5721_: *mut crate::leanh::LeanObject,
    mut v_input_5722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_5723_ = crate::leanh::lean_ctor_get(v_input_5722_, 1);
    crate::leanh::lean_inc_ref(v_vec_5723_);
    v_w_5724_ = crate::leanh::lean_ctor_get(v_input_5722_, 0);
    crate::leanh::lean_inc(v_w_5724_);
    v_cin_5725_ = crate::leanh::lean_ctor_get(v_input_5722_, 2);
    crate::leanh::lean_inc_ref(v_cin_5725_);
    crate::leanh::lean_dec_ref(v_input_5722_);
    v_lhs_5726_ = crate::leanh::lean_ctor_get(v_vec_5723_, 0);
    crate::leanh::lean_inc_ref(v_lhs_5726_);
    v_rhs_5727_ = crate::leanh::lean_ctor_get(v_vec_5723_, 1);
    crate::leanh::lean_inc_ref(v_rhs_5727_);
    crate::leanh::lean_dec_ref(v_vec_5723_);
    v___x_5728_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5729_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89_spec__98(v_w_5724_, v_aig_5721_, v_lhs_5726_, v_rhs_5727_, v___x_5728_, v_cin_5725_);
    crate::leanh::lean_dec_ref(v_rhs_5727_);
    crate::leanh::lean_dec_ref(v_lhs_5726_);
    crate::leanh::lean_dec(v_w_5724_);
    return v___x_5729_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67(
    mut v_w_5733_: *mut crate::leanh::LeanObject,
    mut v_aig_5734_: *mut crate::leanh::LeanObject,
    mut v_pair_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v_res_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: u8 = 0;
    let mut v_trueRef_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5751_: u8 = 0;
    let mut v_aig_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5755_: u8 = 0;
    let mut v_gate_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_unused_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5772_: u8 = 0;
    let mut v_gate_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5776_: u8 = 0;
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5784_: u8 = 0;
    let mut v_isSharedCheck_5785_: u8 = 0;
    let mut v_unused_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5736_ = crate::leanh::lean_ctor_get(v_pair_5735_, 0);
                v_rhs_5737_ = crate::leanh::lean_ctor_get(v_pair_5735_, 1);
                v_isSharedCheck_5788_ = (!crate::leanh::lean_is_exclusive(v_pair_5735_)) as u8;
                if v_isSharedCheck_5788_ == 0 {
                    v___x_5739_ = v_pair_5735_;
                    v_isShared_5740_ = v_isSharedCheck_5788_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_5737_);
                    crate::leanh::lean_inc(v_lhs_5736_);
                    crate::leanh::lean_dec(v_pair_5735_);
                    v___x_5739_ = crate::leanh::lean_box(0);
                    v_isShared_5740_ = v_isSharedCheck_5788_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_res_5741_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15(v_w_5733_, v_aig_5734_, v_rhs_5737_);
                v_aig_5742_ = crate::leanh::lean_ctor_get(v_res_5741_, 0);
                crate::leanh::lean_inc_ref(v_aig_5742_);
                v_vec_5743_ = crate::leanh::lean_ctor_get(v_res_5741_, 1);
                crate::leanh::lean_inc_ref(v_vec_5743_);
                crate::leanh::lean_dec_ref(v_res_5741_);
                v___x_5744_ = 1;
                v_trueRef_5745_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0;
                if v_isShared_5740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5739_, 1, v_vec_5743_);
                    v___x_5747_ = v___x_5739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_lhs_5736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 1, v_vec_5743_);
                    v___x_5747_ = v_reuseFailAlloc_5787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5748_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5748_, 0, v_w_5733_);
                crate::leanh::lean_ctor_set(v___x_5748_, 1, v___x_5747_);
                crate::leanh::lean_ctor_set(v___x_5748_, 2, v_trueRef_5745_);
                v_res_5749_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67_spec__89(v_aig_5742_, v___x_5748_);
                v_ref_5750_ = crate::leanh::lean_ctor_get(v_res_5749_, 1);
                crate::leanh::lean_inc_ref(v_ref_5750_);
                v_invert_5751_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5750_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_5751_ == 0 {
                    v_aig_5752_ = crate::leanh::lean_ctor_get(v_res_5749_, 0);
                    v_isSharedCheck_5767_ = (!crate::leanh::lean_is_exclusive(v_res_5749_)) as u8;
                    if v_isSharedCheck_5767_ == 0 {
                        v_unused_5768_ = crate::leanh::lean_ctor_get(v_res_5749_, 1);
                        crate::leanh::lean_dec(v_unused_5768_);
                        v___x_5754_ = v_res_5749_;
                        v_isShared_5755_ = v_isSharedCheck_5767_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_5752_);
                        crate::leanh::lean_dec(v_res_5749_);
                        v___x_5754_ = crate::leanh::lean_box(0);
                        v_isShared_5755_ = v_isSharedCheck_5767_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_aig_5769_ = crate::leanh::lean_ctor_get(v_res_5749_, 0);
                    v_isSharedCheck_5785_ = (!crate::leanh::lean_is_exclusive(v_res_5749_)) as u8;
                    if v_isSharedCheck_5785_ == 0 {
                        v_unused_5786_ = crate::leanh::lean_ctor_get(v_res_5749_, 1);
                        crate::leanh::lean_dec(v_unused_5786_);
                        v___x_5771_ = v_res_5749_;
                        v_isShared_5772_ = v_isSharedCheck_5785_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_5769_);
                        crate::leanh::lean_dec(v_res_5749_);
                        v___x_5771_ = crate::leanh::lean_box(0);
                        v_isShared_5772_ = v_isSharedCheck_5785_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_gate_5756_ = crate::leanh::lean_ctor_get(v_ref_5750_, 0);
                v_isSharedCheck_5766_ = (!crate::leanh::lean_is_exclusive(v_ref_5750_)) as u8;
                if v_isSharedCheck_5766_ == 0 {
                    v___x_5758_ = v_ref_5750_;
                    v_isShared_5759_ = v_isSharedCheck_5766_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5756_);
                    crate::leanh::lean_dec(v_ref_5750_);
                    v___x_5758_ = crate::leanh::lean_box(0);
                    v_isShared_5759_ = v_isSharedCheck_5766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5759_ == 0 {
                    v___x_5761_ = v___x_5758_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_gate_5756_);
                    v___x_5761_ = v_reuseFailAlloc_5765_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5744_,
                );
                if v_isShared_5755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5754_, 1, v___x_5761_);
                    v___x_5763_ = v___x_5754_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_aig_5752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 1, v___x_5761_);
                    v___x_5763_ = v_reuseFailAlloc_5764_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5763_;
            }
            7 => {
                v_gate_5773_ = crate::leanh::lean_ctor_get(v_ref_5750_, 0);
                v_isSharedCheck_5784_ = (!crate::leanh::lean_is_exclusive(v_ref_5750_)) as u8;
                if v_isSharedCheck_5784_ == 0 {
                    v___x_5775_ = v_ref_5750_;
                    v_isShared_5776_ = v_isSharedCheck_5784_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5773_);
                    crate::leanh::lean_dec(v_ref_5750_);
                    v___x_5775_ = crate::leanh::lean_box(0);
                    v_isShared_5776_ = v_isSharedCheck_5784_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5777_ = 0;
                if v_isShared_5776_ == 0 {
                    v___x_5779_ = v___x_5775_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5783_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_gate_5773_);
                    v___x_5779_ = v_reuseFailAlloc_5783_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5779_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5777_,
                );
                if v_isShared_5772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5771_, 1, v___x_5779_);
                    v___x_5781_ = v___x_5771_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_aig_5769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5779_);
                    v___x_5781_ = v_reuseFailAlloc_5782_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go___at___00Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22_spec__29(
    mut v_len_5789_: *mut crate::leanh::LeanObject,
    mut v_aig_5790_: *mut crate::leanh::LeanObject,
    mut v_s_5791_: *mut crate::leanh::LeanObject,
    mut v_idx_5792_: *mut crate::leanh::LeanObject,
    mut v_acc_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5794_: u8 = 0;
    let mut v_decls_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5794_ = lean_nat_dec_lt(v_idx_5792_, v_len_5789_);
                if v___x_5794_ == 0 {
                    crate::leanh::lean_dec(v_idx_5792_);
                    return v_acc_5793_;
                } else {
                    v_decls_5795_ = crate::leanh::lean_ctor_get(v_aig_5790_, 0);
                    v_ref_5796_ = lean_array_fget_borrowed(v_s_5791_, v_idx_5792_);
                    v___x_5797_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5798_ = lean_nat_shiftr(v_ref_5796_, v___x_5797_);
                    v_decl_5799_ = lean_array_fget_borrowed(v_decls_5795_, v___x_5798_);
                    crate::leanh::lean_dec(v___x_5798_);
                    if crate::leanh::lean_obj_tag(v_decl_5799_) == 0 {
                        v___x_5800_ = lean_nat_add(v_idx_5792_, v___x_5797_);
                        crate::leanh::lean_dec(v_idx_5792_);
                        v___x_5801_ = lean_nat_add(v_acc_5793_, v___x_5797_);
                        crate::leanh::lean_dec(v_acc_5793_);
                        v_idx_5792_ = v___x_5800_;
                        v_acc_5793_ = v___x_5801_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5803_ = lean_nat_add(v_idx_5792_, v___x_5797_);
                        crate::leanh::lean_dec(v_idx_5792_);
                        v_idx_5792_ = v___x_5803_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go___at___00Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22_spec__29___boxed(
    mut v_len_5805_: *mut crate::leanh::LeanObject,
    mut v_aig_5806_: *mut crate::leanh::LeanObject,
    mut v_s_5807_: *mut crate::leanh::LeanObject,
    mut v_idx_5808_: *mut crate::leanh::LeanObject,
    mut v_acc_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5810_ = l_Std_Sat_AIG_RefVec_countKnown_go___at___00Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22_spec__29(v_len_5805_, v_aig_5806_, v_s_5807_, v_idx_5808_, v_acc_5809_);
    crate::leanh::lean_dec_ref(v_s_5807_);
    crate::leanh::lean_dec_ref(v_aig_5806_);
    crate::leanh::lean_dec(v_len_5805_);
    return v_res_5810_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(
    mut v_len_5811_: *mut crate::leanh::LeanObject,
    mut v_aig_5812_: *mut crate::leanh::LeanObject,
    mut v_s_5813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5814_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5815_ = l_Std_Sat_AIG_RefVec_countKnown_go___at___00Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22_spec__29(v_len_5811_, v_aig_5812_, v_s_5813_, v___x_5814_, v___x_5814_);
    return v___x_5815_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22___boxed(
    mut v_len_5816_: *mut crate::leanh::LeanObject,
    mut v_aig_5817_: *mut crate::leanh::LeanObject,
    mut v_s_5818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5819_ = l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(v_len_5816_, v_aig_5817_, v_s_5818_);
    crate::leanh::lean_dec_ref(v_s_5818_);
    crate::leanh::lean_dec_ref(v_aig_5817_);
    crate::leanh::lean_dec(v_len_5816_);
    return v_res_5819_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74___redArg(
    mut v_val_5820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5826_: u8 = 0;
    let mut v_gate_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5828_: u8 = 0;
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v_gate_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5833_: u8 = 0;
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5836_: u8 = 0;
    let mut v_gate_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5838_: u8 = 0;
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5841_: u8 = 0;
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5854_: u8 = 0;
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5821_ = crate::leanh::lean_ctor_get(v_val_5820_, 0);
                v_rhs_5822_ = crate::leanh::lean_ctor_get(v_val_5820_, 1);
                v_cin_5823_ = crate::leanh::lean_ctor_get(v_val_5820_, 2);
                v_isSharedCheck_5857_ = (!crate::leanh::lean_is_exclusive(v_val_5820_)) as u8;
                if v_isSharedCheck_5857_ == 0 {
                    v___x_5825_ = v_val_5820_;
                    v_isShared_5826_ = v_isSharedCheck_5857_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cin_5823_);
                    crate::leanh::lean_inc(v_rhs_5822_);
                    crate::leanh::lean_inc(v_lhs_5821_);
                    crate::leanh::lean_dec(v_val_5820_);
                    v___x_5825_ = crate::leanh::lean_box(0);
                    v_isShared_5826_ = v_isSharedCheck_5857_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_5827_ = crate::leanh::lean_ctor_get(v_lhs_5821_, 0);
                v_invert_5828_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_5821_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5856_ = (!crate::leanh::lean_is_exclusive(v_lhs_5821_)) as u8;
                if v_isSharedCheck_5856_ == 0 {
                    v___x_5830_ = v_lhs_5821_;
                    v_isShared_5831_ = v_isSharedCheck_5856_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5827_);
                    crate::leanh::lean_dec(v_lhs_5821_);
                    v___x_5830_ = crate::leanh::lean_box(0);
                    v_isShared_5831_ = v_isSharedCheck_5856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_5832_ = crate::leanh::lean_ctor_get(v_rhs_5822_, 0);
                v_invert_5833_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_5822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5855_ = (!crate::leanh::lean_is_exclusive(v_rhs_5822_)) as u8;
                if v_isSharedCheck_5855_ == 0 {
                    v___x_5835_ = v_rhs_5822_;
                    v_isShared_5836_ = v_isSharedCheck_5855_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5832_);
                    crate::leanh::lean_dec(v_rhs_5822_);
                    v___x_5835_ = crate::leanh::lean_box(0);
                    v_isShared_5836_ = v_isSharedCheck_5855_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_5837_ = crate::leanh::lean_ctor_get(v_cin_5823_, 0);
                v_invert_5838_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_5823_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5854_ = (!crate::leanh::lean_is_exclusive(v_cin_5823_)) as u8;
                if v_isSharedCheck_5854_ == 0 {
                    v___x_5840_ = v_cin_5823_;
                    v_isShared_5841_ = v_isSharedCheck_5854_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5837_);
                    crate::leanh::lean_dec(v_cin_5823_);
                    v___x_5840_ = crate::leanh::lean_box(0);
                    v_isShared_5841_ = v_isSharedCheck_5854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5840_, 0, v_gate_5827_);
                    v___x_5843_ = v___x_5840_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5853_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_gate_5827_);
                    v___x_5843_ = v_reuseFailAlloc_5853_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5843_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_5828_,
                );
                if v_isShared_5836_ == 0 {
                    v___x_5845_ = v___x_5835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_gate_5832_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5852_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5833_,
                    );
                    v___x_5845_ = v_reuseFailAlloc_5852_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5830_, 0, v_gate_5837_);
                    v___x_5847_ = v___x_5830_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_gate_5837_);
                    v___x_5847_ = v_reuseFailAlloc_5851_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_5838_,
                );
                if v_isShared_5826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5825_, 2, v___x_5847_);
                    crate::leanh::lean_ctor_set(v___x_5825_, 1, v___x_5845_);
                    crate::leanh::lean_ctor_set(v___x_5825_, 0, v___x_5843_);
                    v___x_5849_ = v___x_5825_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 1, v___x_5845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 2, v___x_5847_);
                    v___x_5849_ = v_reuseFailAlloc_5850_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__73(
    mut v_aig_5858_: *mut crate::leanh::LeanObject,
    mut v_input_5859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5869_: u8 = 0;
    let mut v_gate_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5871_: u8 = 0;
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v_cin_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_isSharedCheck_5883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5860_ = crate::leanh::lean_ctor_get(v_input_5859_, 0);
                crate::leanh::lean_inc_ref(v_lhs_5860_);
                v_rhs_5861_ = crate::leanh::lean_ctor_get(v_input_5859_, 1);
                crate::leanh::lean_inc_ref(v_rhs_5861_);
                v_cin_5862_ = crate::leanh::lean_ctor_get(v_input_5859_, 2);
                crate::leanh::lean_inc_ref(v_cin_5862_);
                crate::leanh::lean_dec_ref(v_input_5859_);
                v___x_5863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5863_, 0, v_lhs_5860_);
                crate::leanh::lean_ctor_set(v___x_5863_, 1, v_rhs_5861_);
                v_res_5864_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(v_aig_5858_, v___x_5863_);
                v_aig_5865_ = crate::leanh::lean_ctor_get(v_res_5864_, 0);
                v_ref_5866_ = crate::leanh::lean_ctor_get(v_res_5864_, 1);
                v_isSharedCheck_5883_ = (!crate::leanh::lean_is_exclusive(v_res_5864_)) as u8;
                if v_isSharedCheck_5883_ == 0 {
                    v___x_5868_ = v_res_5864_;
                    v_isShared_5869_ = v_isSharedCheck_5883_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_5866_);
                    crate::leanh::lean_inc(v_aig_5865_);
                    crate::leanh::lean_dec(v_res_5864_);
                    v___x_5868_ = crate::leanh::lean_box(0);
                    v_isShared_5869_ = v_isSharedCheck_5883_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_5870_ = crate::leanh::lean_ctor_get(v_cin_5862_, 0);
                v_invert_5871_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_5862_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5882_ = (!crate::leanh::lean_is_exclusive(v_cin_5862_)) as u8;
                if v_isSharedCheck_5882_ == 0 {
                    v___x_5873_ = v_cin_5862_;
                    v_isShared_5874_ = v_isSharedCheck_5882_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5870_);
                    crate::leanh::lean_dec(v_cin_5862_);
                    v___x_5873_ = crate::leanh::lean_box(0);
                    v_isShared_5874_ = v_isSharedCheck_5882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5874_ == 0 {
                    v_cin_5876_ = v___x_5873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_gate_5870_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5881_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5871_,
                    );
                    v_cin_5876_ = v_reuseFailAlloc_5881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5868_, 1, v_cin_5876_);
                    crate::leanh::lean_ctor_set(v___x_5868_, 0, v_ref_5866_);
                    v___x_5878_ = v___x_5868_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5880_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_ref_5866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5880_, 1, v_cin_5876_);
                    v___x_5878_ = v_reuseFailAlloc_5880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5879_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(v_aig_5865_, v___x_5878_);
                return v___x_5879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52(
    mut v_aig_5884_: *mut crate::leanh::LeanObject,
    mut v_input_5885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5894_: u8 = 0;
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5897_: u8 = 0;
    let mut v_outRef_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_input_5885_);
                v_res_5886_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__73(v_aig_5884_, v_input_5885_);
                v_aig_5887_ = crate::leanh::lean_ctor_get(v_res_5886_, 0);
                crate::leanh::lean_inc_ref(v_aig_5887_);
                v_ref_5888_ = crate::leanh::lean_ctor_get(v_res_5886_, 1);
                crate::leanh::lean_inc_ref(v_ref_5888_);
                crate::leanh::lean_dec_ref(v_res_5886_);
                v_input_5889_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74___redArg(v_input_5885_);
                v_res_5890_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__75(v_aig_5887_, v_input_5889_);
                v_aig_5891_ = crate::leanh::lean_ctor_get(v_res_5890_, 0);
                crate::leanh::lean_inc_ref(v_aig_5891_);
                v_ref_5892_ = crate::leanh::lean_ctor_get(v_res_5890_, 1);
                crate::leanh::lean_inc_ref(v_ref_5892_);
                crate::leanh::lean_dec_ref(v_res_5890_);
                v_gate_5893_ = crate::leanh::lean_ctor_get(v_ref_5888_, 0);
                v_invert_5894_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_5888_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5902_ = (!crate::leanh::lean_is_exclusive(v_ref_5888_)) as u8;
                if v_isSharedCheck_5902_ == 0 {
                    v___x_5896_ = v_ref_5888_;
                    v_isShared_5897_ = v_isSharedCheck_5902_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_5893_);
                    crate::leanh::lean_dec(v_ref_5888_);
                    v___x_5896_ = crate::leanh::lean_box(0);
                    v_isShared_5897_ = v_isSharedCheck_5902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5897_ == 0 {
                    v_outRef_5899_ = v___x_5896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_gate_5893_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5901_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_5894_,
                    );
                    v_outRef_5899_ = v_reuseFailAlloc_5901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5900_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5900_, 0, v_aig_5891_);
                crate::leanh::lean_ctor_set(v___x_5900_, 1, v_outRef_5899_);
                crate::leanh::lean_ctor_set(v___x_5900_, 2, v_ref_5892_);
                return v___x_5900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___redArg(
    mut v_w_5903_: *mut crate::leanh::LeanObject,
    mut v_aig_5904_: *mut crate::leanh::LeanObject,
    mut v_lhs_5905_: *mut crate::leanh::LeanObject,
    mut v_rhs_5906_: *mut crate::leanh::LeanObject,
    mut v_curr_5907_: *mut crate::leanh::LeanObject,
    mut v_cin_5908_: *mut crate::leanh::LeanObject,
    mut v_s_5909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cout_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_5919_: u8 = 0;
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: u8 = 0;
    let mut v___y_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: u8 = 0;
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: u8 = 0;
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: u8 = 0;
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5928_ = lean_nat_dec_lt(v_curr_5907_, v_w_5903_);
                if v___x_5928_ == 0 {
                    crate::leanh::lean_dec_ref(v_cin_5908_);
                    crate::leanh::lean_dec(v_curr_5907_);
                    v___x_5940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5940_, 0, v_aig_5904_);
                    crate::leanh::lean_ctor_set(v___x_5940_, 1, v_s_5909_);
                    return v___x_5940_;
                } else {
                    v_ref_5941_ = lean_array_fget_borrowed(v_lhs_5905_, v_curr_5907_);
                    v___x_5942_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5943_ = lean_nat_shiftr(v_ref_5941_, v___x_5942_);
                    v___x_5944_ = lean_nat_land(v___x_5942_, v_ref_5941_);
                    v___x_5945_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5946_ = lean_nat_dec_eq(v___x_5944_, v___x_5945_);
                    crate::leanh::lean_dec(v___x_5944_);
                    if v___x_5946_ == 0 {
                        v___x_5947_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5947_, 0, v___x_5943_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5947_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5928_,
                        );
                        v___y_5930_ = v___x_5947_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5948_ = 0;
                        v___x_5949_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5943_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5949_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5948_,
                        );
                        v___y_5930_ = v___x_5949_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5913_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5913_, 0, v___y_5911_);
                crate::leanh::lean_ctor_set(v___x_5913_, 1, v___y_5912_);
                crate::leanh::lean_ctor_set(v___x_5913_, 2, v_cin_5908_);
                v_res_5914_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52(v_aig_5904_, v___x_5913_);
                v_out_5915_ = crate::leanh::lean_ctor_get(v_res_5914_, 1);
                crate::leanh::lean_inc_ref(v_out_5915_);
                v_aig_5916_ = crate::leanh::lean_ctor_get(v_res_5914_, 0);
                crate::leanh::lean_inc_ref(v_aig_5916_);
                v_cout_5917_ = crate::leanh::lean_ctor_get(v_res_5914_, 2);
                crate::leanh::lean_inc_ref(v_cout_5917_);
                crate::leanh::lean_dec_ref(v_res_5914_);
                v_gate_5918_ = crate::leanh::lean_ctor_get(v_out_5915_, 0);
                crate::leanh::lean_inc(v_gate_5918_);
                v_invert_5919_ = crate::leanh::lean_ctor_get_uint8(
                    v_out_5915_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_out_5915_);
                v___x_5920_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5921_ = lean_nat_add(v_curr_5907_, v___x_5920_);
                crate::leanh::lean_dec(v_curr_5907_);
                v___x_5922_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5923_ = lean_nat_mul(v_gate_5918_, v___x_5922_);
                crate::leanh::lean_dec(v_gate_5918_);
                v___x_5924_ = l_Bool_toNat(v_invert_5919_);
                v___x_5925_ = lean_nat_lor(v___x_5923_, v___x_5924_);
                crate::leanh::lean_dec(v___x_5924_);
                crate::leanh::lean_dec(v___x_5923_);
                v_s_5926_ = lean_array_push(v_s_5909_, v___x_5925_);
                v_aig_5904_ = v_aig_5916_;
                v_curr_5907_ = v___x_5921_;
                v_cin_5908_ = v_cout_5917_;
                v_s_5909_ = v_s_5926_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_5931_ = lean_array_fget_borrowed(v_rhs_5906_, v_curr_5907_);
                v___x_5932_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5933_ = lean_nat_shiftr(v_ref_5931_, v___x_5932_);
                v___x_5934_ = lean_nat_land(v___x_5932_, v_ref_5931_);
                v___x_5935_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5936_ = lean_nat_dec_eq(v___x_5934_, v___x_5935_);
                crate::leanh::lean_dec(v___x_5934_);
                if v___x_5936_ == 0 {
                    v___x_5937_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5937_, 0, v___x_5933_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5937_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5928_,
                    );
                    v___y_5911_ = v___y_5930_;
                    v___y_5912_ = v___x_5937_;
                    state = 1;
                    continue;
                } else {
                    v___x_5938_ = 0;
                    v___x_5939_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5939_, 0, v___x_5933_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5938_,
                    );
                    v___y_5911_ = v___y_5930_;
                    v___y_5912_ = v___x_5939_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___redArg___boxed(
    mut v_w_5950_: *mut crate::leanh::LeanObject,
    mut v_aig_5951_: *mut crate::leanh::LeanObject,
    mut v_lhs_5952_: *mut crate::leanh::LeanObject,
    mut v_rhs_5953_: *mut crate::leanh::LeanObject,
    mut v_curr_5954_: *mut crate::leanh::LeanObject,
    mut v_cin_5955_: *mut crate::leanh::LeanObject,
    mut v_s_5956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5957_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___redArg(v_w_5950_, v_aig_5951_, v_lhs_5952_, v_rhs_5953_, v_curr_5954_, v_cin_5955_, v_s_5956_);
    crate::leanh::lean_dec_ref(v_rhs_5953_);
    crate::leanh::lean_dec_ref(v_lhs_5952_);
    crate::leanh::lean_dec(v_w_5950_);
    return v_res_5957_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23(
    mut v_w_5958_: *mut crate::leanh::LeanObject,
    mut v_aig_5959_: *mut crate::leanh::LeanObject,
    mut v_input_5960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_5961_ = crate::leanh::lean_ctor_get(v_input_5960_, 0);
    v_rhs_5962_ = crate::leanh::lean_ctor_get(v_input_5960_, 1);
    v___x_5963_ = crate::leanh::lean_unsigned_to_nat(0);
    v_cin_5964_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0;
    v___x_5965_ = lean_mk_empty_array_with_capacity(v_w_5958_);
    v___x_5966_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___redArg(v_w_5958_, v_aig_5959_, v_lhs_5961_, v_rhs_5962_, v___x_5963_, v_cin_5964_, v___x_5965_);
    return v___x_5966_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23___boxed(
    mut v_w_5967_: *mut crate::leanh::LeanObject,
    mut v_aig_5968_: *mut crate::leanh::LeanObject,
    mut v_input_5969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5970_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23(v_w_5967_, v_aig_5968_, v_input_5969_);
    crate::leanh::lean_dec_ref(v_input_5969_);
    crate::leanh::lean_dec(v_w_5967_);
    return v_res_5970_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(
    mut v_w_5971_: *mut crate::leanh::LeanObject,
    mut v_aig_5972_: *mut crate::leanh::LeanObject,
    mut v_input_5973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5981_: u8 = 0;
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5986_: u8 = 0;
    let mut v_unused_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_5974_ = crate::leanh::lean_ctor_get(v_input_5973_, 0);
                v_rhs_5975_ = crate::leanh::lean_ctor_get(v_input_5973_, 1);
                v___x_5976_ = l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(v_w_5971_, v_aig_5972_, v_lhs_5974_);
                v___x_5977_ = l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(v_w_5971_, v_aig_5972_, v_rhs_5975_);
                v___x_5978_ = lean_nat_dec_lt(v___x_5976_, v___x_5977_);
                crate::leanh::lean_dec(v___x_5977_);
                crate::leanh::lean_dec(v___x_5976_);
                if v___x_5978_ == 0 {
                    crate::leanh::lean_inc_ref(v_rhs_5975_);
                    crate::leanh::lean_inc_ref(v_lhs_5974_);
                    v_isSharedCheck_5986_ = (!crate::leanh::lean_is_exclusive(v_input_5973_)) as u8;
                    if v_isSharedCheck_5986_ == 0 {
                        v_unused_5987_ = crate::leanh::lean_ctor_get(v_input_5973_, 1);
                        crate::leanh::lean_dec(v_unused_5987_);
                        v_unused_5988_ = crate::leanh::lean_ctor_get(v_input_5973_, 0);
                        crate::leanh::lean_dec(v_unused_5988_);
                        v___x_5980_ = v_input_5973_;
                        v_isShared_5981_ = v_isSharedCheck_5986_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_input_5973_);
                        v___x_5980_ = crate::leanh::lean_box(0);
                        v_isShared_5981_ = v_isSharedCheck_5986_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5989_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23(v_w_5971_, v_aig_5972_, v_input_5973_);
                    crate::leanh::lean_dec_ref(v_input_5973_);
                    return v___x_5989_;
                }
            }
            1 => {
                if v_isShared_5981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5980_, 1, v_lhs_5974_);
                    crate::leanh::lean_ctor_set(v___x_5980_, 0, v_rhs_5975_);
                    v___x_5983_ = v___x_5980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5985_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_rhs_5975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_lhs_5974_);
                    v___x_5983_ = v_reuseFailAlloc_5985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5984_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23(v_w_5971_, v_aig_5972_, v___x_5983_);
                crate::leanh::lean_dec_ref(v___x_5983_);
                return v___x_5984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11___boxed(
    mut v_w_5990_: *mut crate::leanh::LeanObject,
    mut v_aig_5991_: *mut crate::leanh::LeanObject,
    mut v_input_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5993_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_5990_, v_aig_5991_, v_input_5992_);
    crate::leanh::lean_dec(v_w_5990_);
    return v_res_5993_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66_spec__87(
    mut v_w_5994_: *mut crate::leanh::LeanObject,
    mut v_aig_5995_: *mut crate::leanh::LeanObject,
    mut v_input_5996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_res_5997_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15(v_w_5994_, v_aig_5995_, v_input_5996_);
                v_aig_5998_ = crate::leanh::lean_ctor_get(v_res_5997_, 0);
                v_vec_5999_ = crate::leanh::lean_ctor_get(v_res_5997_, 1);
                v_isSharedCheck_6010_ = (!crate::leanh::lean_is_exclusive(v_res_5997_)) as u8;
                if v_isSharedCheck_6010_ == 0 {
                    v___x_6001_ = v_res_5997_;
                    v_isShared_6002_ = v_isSharedCheck_6010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_5999_);
                    crate::leanh::lean_inc(v_aig_5998_);
                    crate::leanh::lean_dec(v_res_5997_);
                    v___x_6001_ = crate::leanh::lean_box(0);
                    v_isShared_6002_ = v_isSharedCheck_6010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6003_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6004_ = l_BitVec_ofNat(v_w_5994_, v___x_6003_);
                v_one_6005_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_5994_, v_aig_5998_, v___x_6004_);
                crate::leanh::lean_dec(v___x_6004_);
                if v_isShared_6002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6001_, 1, v_one_6005_);
                    crate::leanh::lean_ctor_set(v___x_6001_, 0, v_vec_5999_);
                    v___x_6007_ = v___x_6001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_vec_5999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6009_, 1, v_one_6005_);
                    v___x_6007_ = v_reuseFailAlloc_6009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6008_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_5994_, v_aig_5998_, v___x_6007_);
                return v___x_6008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66_spec__87___boxed(
    mut v_w_6011_: *mut crate::leanh::LeanObject,
    mut v_aig_6012_: *mut crate::leanh::LeanObject,
    mut v_input_6013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6014_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66_spec__87(v_w_6011_, v_aig_6012_, v_input_6013_);
    crate::leanh::lean_dec(v_w_6011_);
    return v_res_6014_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66(
    mut v_w_6015_: *mut crate::leanh::LeanObject,
    mut v_aig_6016_: *mut crate::leanh::LeanObject,
    mut v_input_6017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v_res_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_6018_ = crate::leanh::lean_ctor_get(v_input_6017_, 0);
                v_rhs_6019_ = crate::leanh::lean_ctor_get(v_input_6017_, 1);
                v_isSharedCheck_6030_ = (!crate::leanh::lean_is_exclusive(v_input_6017_)) as u8;
                if v_isSharedCheck_6030_ == 0 {
                    v___x_6021_ = v_input_6017_;
                    v_isShared_6022_ = v_isSharedCheck_6030_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_6019_);
                    crate::leanh::lean_inc(v_lhs_6018_);
                    crate::leanh::lean_dec(v_input_6017_);
                    v___x_6021_ = crate::leanh::lean_box(0);
                    v_isShared_6022_ = v_isSharedCheck_6030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_res_6023_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66_spec__87(v_w_6015_, v_aig_6016_, v_rhs_6019_);
                v_aig_6024_ = crate::leanh::lean_ctor_get(v_res_6023_, 0);
                crate::leanh::lean_inc_ref(v_aig_6024_);
                v_vec_6025_ = crate::leanh::lean_ctor_get(v_res_6023_, 1);
                crate::leanh::lean_inc_ref(v_vec_6025_);
                crate::leanh::lean_dec_ref(v_res_6023_);
                if v_isShared_6022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6021_, 1, v_vec_6025_);
                    v___x_6027_ = v___x_6021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v_lhs_6018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 1, v_vec_6025_);
                    v___x_6027_ = v_reuseFailAlloc_6029_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6028_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_6015_, v_aig_6024_, v___x_6027_);
                return v___x_6028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66___boxed(
    mut v_w_6031_: *mut crate::leanh::LeanObject,
    mut v_aig_6032_: *mut crate::leanh::LeanObject,
    mut v_input_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66(v_w_6031_, v_aig_6032_, v_input_6033_);
    crate::leanh::lean_dec(v_w_6031_);
    return v_res_6034_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___redArg(
    mut v_aig_6035_: *mut crate::leanh::LeanObject,
    mut v_w_6036_: *mut crate::leanh::LeanObject,
    mut v_input_6037_: *mut crate::leanh::LeanObject,
    mut v_newWidth_6038_: *mut crate::leanh::LeanObject,
    mut v_curr_6039_: *mut crate::leanh::LeanObject,
    mut v_s_6040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6043_: u8 = 0;
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: u8 = 0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: u8 = 0;
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: u8 = 0;
    let mut v___x_6068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6052_ = lean_nat_dec_lt(v_curr_6039_, v_newWidth_6038_);
                if v___x_6052_ == 0 {
                    crate::leanh::lean_dec(v_curr_6039_);
                    v___x_6053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6053_, 0, v_aig_6035_);
                    crate::leanh::lean_ctor_set(v___x_6053_, 1, v_s_6040_);
                    return v___x_6053_;
                } else {
                    v___x_6054_ = lean_nat_dec_lt(v_curr_6039_, v_w_6036_);
                    if v___x_6054_ == 0 {
                        v___x_6055_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6056_ = lean_nat_add(v_curr_6039_, v___x_6055_);
                        crate::leanh::lean_dec(v_curr_6039_);
                        v___x_6057_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6058_ = l_Bool_toNat(v___x_6054_);
                        v___x_6059_ = lean_nat_lor(v___x_6057_, v___x_6058_);
                        crate::leanh::lean_dec(v___x_6058_);
                        v_s_6060_ = lean_array_push(v_s_6040_, v___x_6059_);
                        v_curr_6039_ = v___x_6056_;
                        v_s_6040_ = v_s_6060_;
                        state = 0;
                        continue;
                    } else {
                        v_ref_6062_ = lean_array_fget_borrowed(v_input_6037_, v_curr_6039_);
                        v___x_6063_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6064_ = lean_nat_shiftr(v_ref_6062_, v___x_6063_);
                        v___x_6065_ = lean_nat_land(v___x_6063_, v_ref_6062_);
                        v___x_6066_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6067_ = lean_nat_dec_eq(v___x_6065_, v___x_6066_);
                        crate::leanh::lean_dec(v___x_6065_);
                        if v___x_6067_ == 0 {
                            v_gate_6042_ = v___x_6064_;
                            v_invert_6043_ = v___x_6054_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6068_ = 0;
                            v_gate_6042_ = v___x_6064_;
                            v_invert_6043_ = v___x_6068_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6044_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6045_ = lean_nat_add(v_curr_6039_, v___x_6044_);
                crate::leanh::lean_dec(v_curr_6039_);
                v___x_6046_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6047_ = lean_nat_mul(v_gate_6042_, v___x_6046_);
                crate::leanh::lean_dec(v_gate_6042_);
                v___x_6048_ = l_Bool_toNat(v_invert_6043_);
                v___x_6049_ = lean_nat_lor(v___x_6047_, v___x_6048_);
                crate::leanh::lean_dec(v___x_6048_);
                crate::leanh::lean_dec(v___x_6047_);
                v_s_6050_ = lean_array_push(v_s_6040_, v___x_6049_);
                v_curr_6039_ = v___x_6045_;
                v_s_6040_ = v_s_6050_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___redArg___boxed(
    mut v_aig_6069_: *mut crate::leanh::LeanObject,
    mut v_w_6070_: *mut crate::leanh::LeanObject,
    mut v_input_6071_: *mut crate::leanh::LeanObject,
    mut v_newWidth_6072_: *mut crate::leanh::LeanObject,
    mut v_curr_6073_: *mut crate::leanh::LeanObject,
    mut v_s_6074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6075_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___redArg(v_aig_6069_, v_w_6070_, v_input_6071_, v_newWidth_6072_, v_curr_6073_, v_s_6074_);
    crate::leanh::lean_dec(v_newWidth_6072_);
    crate::leanh::lean_dec_ref(v_input_6071_);
    crate::leanh::lean_dec(v_w_6070_);
    return v_res_6075_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85(
    mut v_newWidth_6076_: *mut crate::leanh::LeanObject,
    mut v_aig_6077_: *mut crate::leanh::LeanObject,
    mut v_target_6078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_6079_ = crate::leanh::lean_ctor_get(v_target_6078_, 0);
    v_vec_6080_ = crate::leanh::lean_ctor_get(v_target_6078_, 1);
    v___x_6081_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6082_ = lean_mk_empty_array_with_capacity(v_newWidth_6076_);
    v___x_6083_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___redArg(v_aig_6077_, v_w_6079_, v_vec_6080_, v_newWidth_6076_, v___x_6081_, v___x_6082_);
    return v___x_6083_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85___boxed(
    mut v_newWidth_6084_: *mut crate::leanh::LeanObject,
    mut v_aig_6085_: *mut crate::leanh::LeanObject,
    mut v_target_6086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6087_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85(v_newWidth_6084_, v_aig_6085_, v_target_6086_);
    crate::leanh::lean_dec_ref(v_target_6086_);
    crate::leanh::lean_dec(v_newWidth_6084_);
    return v_res_6087_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65(
    mut v_w_6088_: *mut crate::leanh::LeanObject,
    mut v_aig_6089_: *mut crate::leanh::LeanObject,
    mut v_input_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bit_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v_gate_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6097_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_refs_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bit_6091_ = crate::leanh::lean_ctor_get(v_input_6090_, 1);
                v_lhs_6092_ = crate::leanh::lean_ctor_get(v_input_6090_, 0);
                v_isSharedCheck_6112_ = (!crate::leanh::lean_is_exclusive(v_input_6090_)) as u8;
                if v_isSharedCheck_6112_ == 0 {
                    v___x_6094_ = v_input_6090_;
                    v_isShared_6095_ = v_isSharedCheck_6112_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bit_6091_);
                    crate::leanh::lean_inc(v_lhs_6092_);
                    crate::leanh::lean_dec(v_input_6090_);
                    v___x_6094_ = crate::leanh::lean_box(0);
                    v_isShared_6095_ = v_isSharedCheck_6112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_6096_ = crate::leanh::lean_ctor_get(v_bit_6091_, 0);
                crate::leanh::lean_inc(v_gate_6096_);
                v_invert_6097_ = crate::leanh::lean_ctor_get_uint8(
                    v_bit_6091_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_bit_6091_);
                v___x_6098_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6099_ = lean_nat_add(v_w_6088_, v___x_6098_);
                v_refs_6100_ = lean_mk_empty_array_with_capacity(v___x_6099_);
                crate::leanh::lean_dec(v___x_6099_);
                v___x_6101_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6102_ = lean_nat_mul(v_gate_6096_, v___x_6101_);
                crate::leanh::lean_dec(v_gate_6096_);
                v___x_6103_ = l_Bool_toNat(v_invert_6097_);
                v___x_6104_ = lean_nat_lor(v___x_6102_, v___x_6103_);
                crate::leanh::lean_dec(v___x_6103_);
                crate::leanh::lean_dec(v___x_6102_);
                v___x_6105_ = lean_array_push(v_refs_6100_, v___x_6104_);
                v___x_6106_ = lean_nat_add(v___x_6098_, v_w_6088_);
                v_new_6107_ = l_Array_append___redArg(v___x_6105_, v_lhs_6092_);
                crate::leanh::lean_dec_ref(v_lhs_6092_);
                if v_isShared_6095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6094_, 1, v_new_6107_);
                    crate::leanh::lean_ctor_set(v___x_6094_, 0, v___x_6106_);
                    v___x_6109_ = v___x_6094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6111_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6111_, 0, v___x_6106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6111_, 1, v_new_6107_);
                    v___x_6109_ = v_reuseFailAlloc_6111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6110_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85(v_w_6088_, v_aig_6089_, v___x_6109_);
                crate::leanh::lean_dec_ref(v___x_6109_);
                return v___x_6110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65___boxed(
    mut v_w_6113_: *mut crate::leanh::LeanObject,
    mut v_aig_6114_: *mut crate::leanh::LeanObject,
    mut v_input_6115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6116_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65(v_w_6113_, v_aig_6114_, v_input_6115_);
    crate::leanh::lean_dec(v_w_6113_);
    return v_res_6116_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42(
    mut v_w_6117_: *mut crate::leanh::LeanObject,
    mut v_aig_6118_: *mut crate::leanh::LeanObject,
    mut v_n_6119_: *mut crate::leanh::LeanObject,
    mut v_d_6120_: *mut crate::leanh::LeanObject,
    mut v_wn_6121_: *mut crate::leanh::LeanObject,
    mut v_wr_6122_: *mut crate::leanh::LeanObject,
    mut v_q_6123_: *mut crate::leanh::LeanObject,
    mut v_r_6124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wn_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wr_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: u8 = 0;
    let mut v___y_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6137_: u8 = 0;
    let mut v_falseRef_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v_trueRef_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6155_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6169_: u8 = 0;
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6172_: u8 = 0;
    let mut v_discr_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut v_reuseFailAlloc_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6183_: u8 = 0;
    let mut v_reuseFailAlloc_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_reuseFailAlloc_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6187_: u8 = 0;
    let mut v___x_6188_: u8 = 0;
    let mut v_falseRef_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6125_ = crate::leanh::lean_unsigned_to_nat(1);
                v_wn_6126_ = lean_nat_sub(v_wn_6121_, v___x_6125_);
                v_wr_6127_ = lean_nat_add(v_wr_6122_, v___x_6125_);
                v___x_6128_ = 0;
                v___x_6188_ = lean_nat_dec_lt(v_wn_6126_, v_w_6117_);
                if v___x_6188_ == 0 {
                    v_falseRef_6189_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0;
                    v___y_6130_ = v_falseRef_6189_;
                    state = 1;
                    continue;
                } else {
                    v_ref_6190_ = lean_array_fget_borrowed(v_n_6119_, v_wn_6126_);
                    v___x_6191_ = lean_nat_shiftr(v_ref_6190_, v___x_6125_);
                    v___x_6192_ = lean_nat_land(v___x_6125_, v_ref_6190_);
                    v___x_6193_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6194_ = lean_nat_dec_eq(v___x_6192_, v___x_6193_);
                    crate::leanh::lean_dec(v___x_6192_);
                    if v___x_6194_ == 0 {
                        v___x_6195_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6195_, 0, v___x_6191_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6195_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6188_,
                        );
                        v___y_6130_ = v___x_6195_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6196_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6196_, 0, v___x_6191_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6196_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6128_,
                        );
                        v___y_6130_ = v___x_6196_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6131_, 0, v_r_6124_);
                crate::leanh::lean_ctor_set(v___x_6131_, 1, v___y_6130_);
                v_res_6132_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65(v_w_6117_, v_aig_6118_, v___x_6131_);
                v_aig_6133_ = crate::leanh::lean_ctor_get(v_res_6132_, 0);
                v_vec_6134_ = crate::leanh::lean_ctor_get(v_res_6132_, 1);
                v_isSharedCheck_6187_ = (!crate::leanh::lean_is_exclusive(v_res_6132_)) as u8;
                if v_isSharedCheck_6187_ == 0 {
                    v___x_6136_ = v_res_6132_;
                    v_isShared_6137_ = v_isSharedCheck_6187_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_6134_);
                    crate::leanh::lean_inc(v_aig_6133_);
                    crate::leanh::lean_dec(v_res_6132_);
                    v___x_6136_ = crate::leanh::lean_box(0);
                    v_isShared_6137_ = v_isSharedCheck_6187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_falseRef_6138_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12___closed__0;
                crate::leanh::lean_inc_ref(v_q_6123_);
                if v_isShared_6137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6136_, 1, v_falseRef_6138_);
                    crate::leanh::lean_ctor_set(v___x_6136_, 0, v_q_6123_);
                    v___x_6140_ = v___x_6136_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_q_6123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_falseRef_6138_);
                    v___x_6140_ = v_reuseFailAlloc_6186_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_res_6141_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65(v_w_6117_, v_aig_6133_, v___x_6140_);
                v_aig_6142_ = crate::leanh::lean_ctor_get(v_res_6141_, 0);
                v_vec_6143_ = crate::leanh::lean_ctor_get(v_res_6141_, 1);
                v_isSharedCheck_6185_ = (!crate::leanh::lean_is_exclusive(v_res_6141_)) as u8;
                if v_isSharedCheck_6185_ == 0 {
                    v___x_6145_ = v_res_6141_;
                    v_isShared_6146_ = v_isSharedCheck_6185_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_6143_);
                    crate::leanh::lean_inc(v_aig_6142_);
                    crate::leanh::lean_dec(v_res_6141_);
                    v___x_6145_ = crate::leanh::lean_box(0);
                    v_isShared_6146_ = v_isSharedCheck_6185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_trueRef_6147_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0;
                if v_isShared_6146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6145_, 1, v_trueRef_6147_);
                    crate::leanh::lean_ctor_set(v___x_6145_, 0, v_q_6123_);
                    v___x_6149_ = v___x_6145_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_q_6123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 1, v_trueRef_6147_);
                    v___x_6149_ = v_reuseFailAlloc_6184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_res_6150_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65(v_w_6117_, v_aig_6142_, v___x_6149_);
                v_aig_6151_ = crate::leanh::lean_ctor_get(v_res_6150_, 0);
                v_vec_6152_ = crate::leanh::lean_ctor_get(v_res_6150_, 1);
                v_isSharedCheck_6183_ = (!crate::leanh::lean_is_exclusive(v_res_6150_)) as u8;
                if v_isSharedCheck_6183_ == 0 {
                    v___x_6154_ = v_res_6150_;
                    v_isShared_6155_ = v_isSharedCheck_6183_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_6152_);
                    crate::leanh::lean_inc(v_aig_6151_);
                    crate::leanh::lean_dec(v_res_6150_);
                    v___x_6154_ = crate::leanh::lean_box(0);
                    v_isShared_6155_ = v_isSharedCheck_6183_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_vec_6134_);
                if v_isShared_6155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6154_, 1, v_d_6120_);
                    crate::leanh::lean_ctor_set(v___x_6154_, 0, v_vec_6134_);
                    v___x_6157_ = v___x_6154_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_vec_6134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6182_, 1, v_d_6120_);
                    v___x_6157_ = v_reuseFailAlloc_6182_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___x_6157_);
                v_res_6158_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__66(v_w_6117_, v_aig_6151_, v___x_6157_);
                v_aig_6159_ = crate::leanh::lean_ctor_get(v_res_6158_, 0);
                crate::leanh::lean_inc_ref(v_aig_6159_);
                v_vec_6160_ = crate::leanh::lean_ctor_get(v_res_6158_, 1);
                crate::leanh::lean_inc_ref(v_vec_6160_);
                crate::leanh::lean_dec_ref(v_res_6158_);
                crate::leanh::lean_inc(v_w_6117_);
                v_res_6161_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67(v_w_6117_, v_aig_6159_, v___x_6157_);
                v_aig_6162_ = crate::leanh::lean_ctor_get(v_res_6161_, 0);
                crate::leanh::lean_inc_ref(v_aig_6162_);
                v_ref_6163_ = crate::leanh::lean_ctor_get(v_res_6161_, 1);
                crate::leanh::lean_inc_ref_n(v_ref_6163_, 2);
                crate::leanh::lean_dec_ref(v_res_6161_);
                v___x_6164_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6164_, 0, v_ref_6163_);
                crate::leanh::lean_ctor_set(v___x_6164_, 1, v_vec_6143_);
                crate::leanh::lean_ctor_set(v___x_6164_, 2, v_vec_6152_);
                v_res_6165_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6117_, v_aig_6162_, v___x_6164_);
                v_aig_6166_ = crate::leanh::lean_ctor_get(v_res_6165_, 0);
                crate::leanh::lean_inc_ref(v_aig_6166_);
                v_vec_6167_ = crate::leanh::lean_ctor_get(v_res_6165_, 1);
                crate::leanh::lean_inc_ref(v_vec_6167_);
                crate::leanh::lean_dec_ref(v_res_6165_);
                v_gate_6168_ = crate::leanh::lean_ctor_get(v_ref_6163_, 0);
                v_invert_6169_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_6163_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6181_ = (!crate::leanh::lean_is_exclusive(v_ref_6163_)) as u8;
                if v_isSharedCheck_6181_ == 0 {
                    v___x_6171_ = v_ref_6163_;
                    v_isShared_6172_ = v_isSharedCheck_6181_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_6168_);
                    crate::leanh::lean_dec(v_ref_6163_);
                    v___x_6171_ = crate::leanh::lean_box(0);
                    v_isShared_6172_ = v_isSharedCheck_6181_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6172_ == 0 {
                    v_discr_6174_ = v___x_6171_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6180_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_gate_6168_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6180_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_6169_,
                    );
                    v_discr_6174_ = v_reuseFailAlloc_6180_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6175_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6175_, 0, v_discr_6174_);
                crate::leanh::lean_ctor_set(v___x_6175_, 1, v_vec_6134_);
                crate::leanh::lean_ctor_set(v___x_6175_, 2, v_vec_6160_);
                v_res_6176_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6117_, v_aig_6166_, v___x_6175_);
                crate::leanh::lean_dec(v_w_6117_);
                v_aig_6177_ = crate::leanh::lean_ctor_get(v_res_6176_, 0);
                crate::leanh::lean_inc_ref(v_aig_6177_);
                v_vec_6178_ = crate::leanh::lean_ctor_get(v_res_6176_, 1);
                crate::leanh::lean_inc_ref(v_vec_6178_);
                crate::leanh::lean_dec_ref(v_res_6176_);
                v___x_6179_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6179_, 0, v_aig_6177_);
                crate::leanh::lean_ctor_set(v___x_6179_, 1, v_wn_6126_);
                crate::leanh::lean_ctor_set(v___x_6179_, 2, v_wr_6127_);
                crate::leanh::lean_ctor_set(v___x_6179_, 3, v_vec_6167_);
                crate::leanh::lean_ctor_set(v___x_6179_, 4, v_vec_6178_);
                return v___x_6179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42___boxed(
    mut v_w_6197_: *mut crate::leanh::LeanObject,
    mut v_aig_6198_: *mut crate::leanh::LeanObject,
    mut v_n_6199_: *mut crate::leanh::LeanObject,
    mut v_d_6200_: *mut crate::leanh::LeanObject,
    mut v_wn_6201_: *mut crate::leanh::LeanObject,
    mut v_wr_6202_: *mut crate::leanh::LeanObject,
    mut v_q_6203_: *mut crate::leanh::LeanObject,
    mut v_r_6204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6205_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42(v_w_6197_, v_aig_6198_, v_n_6199_, v_d_6200_, v_wn_6201_, v_wr_6202_, v_q_6203_, v_r_6204_);
    crate::leanh::lean_dec(v_wr_6202_);
    crate::leanh::lean_dec(v_wn_6201_);
    crate::leanh::lean_dec_ref(v_n_6199_);
    return v_res_6205_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28(
    mut v_w_6206_: *mut crate::leanh::LeanObject,
    mut v_aig_6207_: *mut crate::leanh::LeanObject,
    mut v_curr_6208_: *mut crate::leanh::LeanObject,
    mut v_n_6209_: *mut crate::leanh::LeanObject,
    mut v_d_6210_: *mut crate::leanh::LeanObject,
    mut v_wn_6211_: *mut crate::leanh::LeanObject,
    mut v_wr_6212_: *mut crate::leanh::LeanObject,
    mut v_q_6213_: *mut crate::leanh::LeanObject,
    mut v_r_6214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6216_: u8 = 0;
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wn_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wr_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6232_: u8 = 0;
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6215_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_6216_ = lean_nat_dec_eq(v_curr_6208_, v_zero_6215_);
                if v_isZero_6216_ == 1 {
                    crate::leanh::lean_dec_ref(v_d_6210_);
                    crate::leanh::lean_dec(v_w_6206_);
                    v___x_6217_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6217_, 0, v_aig_6207_);
                    crate::leanh::lean_ctor_set(v___x_6217_, 1, v_q_6213_);
                    crate::leanh::lean_ctor_set(v___x_6217_, 2, v_r_6214_);
                    return v___x_6217_;
                } else {
                    crate::leanh::lean_inc_ref(v_d_6210_);
                    crate::leanh::lean_inc(v_w_6206_);
                    v_res_6218_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42(v_w_6206_, v_aig_6207_, v_n_6209_, v_d_6210_, v_wn_6211_, v_wr_6212_, v_q_6213_, v_r_6214_);
                    v_aig_6219_ = crate::leanh::lean_ctor_get(v_res_6218_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6219_);
                    v_wn_6220_ = crate::leanh::lean_ctor_get(v_res_6218_, 1);
                    crate::leanh::lean_inc(v_wn_6220_);
                    v_wr_6221_ = crate::leanh::lean_ctor_get(v_res_6218_, 2);
                    crate::leanh::lean_inc(v_wr_6221_);
                    v_q_6222_ = crate::leanh::lean_ctor_get(v_res_6218_, 3);
                    crate::leanh::lean_inc_ref(v_q_6222_);
                    v_r_6223_ = crate::leanh::lean_ctor_get(v_res_6218_, 4);
                    crate::leanh::lean_inc_ref(v_r_6223_);
                    crate::leanh::lean_dec_ref(v_res_6218_);
                    v_one_6224_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_6225_ = lean_nat_sub(v_curr_6208_, v_one_6224_);
                    v_res_6226_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28(v_w_6206_, v_aig_6219_, v_n_6225_, v_n_6209_, v_d_6210_, v_wn_6220_, v_wr_6221_, v_q_6222_, v_r_6223_);
                    crate::leanh::lean_dec(v_wr_6221_);
                    crate::leanh::lean_dec(v_wn_6220_);
                    crate::leanh::lean_dec(v_n_6225_);
                    v_aig_6227_ = crate::leanh::lean_ctor_get(v_res_6226_, 0);
                    v_q_6228_ = crate::leanh::lean_ctor_get(v_res_6226_, 1);
                    v_r_6229_ = crate::leanh::lean_ctor_get(v_res_6226_, 2);
                    v_isSharedCheck_6236_ = (!crate::leanh::lean_is_exclusive(v_res_6226_)) as u8;
                    if v_isSharedCheck_6236_ == 0 {
                        v___x_6231_ = v_res_6226_;
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_6229_);
                        crate::leanh::lean_inc(v_q_6228_);
                        crate::leanh::lean_inc(v_aig_6227_);
                        crate::leanh::lean_dec(v_res_6226_);
                        v___x_6231_ = crate::leanh::lean_box(0);
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6232_ == 0 {
                    v___x_6234_ = v___x_6231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6235_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6235_, 0, v_aig_6227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6235_, 1, v_q_6228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6235_, 2, v_r_6229_);
                    v___x_6234_ = v_reuseFailAlloc_6235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28___boxed(
    mut v_w_6237_: *mut crate::leanh::LeanObject,
    mut v_aig_6238_: *mut crate::leanh::LeanObject,
    mut v_curr_6239_: *mut crate::leanh::LeanObject,
    mut v_n_6240_: *mut crate::leanh::LeanObject,
    mut v_d_6241_: *mut crate::leanh::LeanObject,
    mut v_wn_6242_: *mut crate::leanh::LeanObject,
    mut v_wr_6243_: *mut crate::leanh::LeanObject,
    mut v_q_6244_: *mut crate::leanh::LeanObject,
    mut v_r_6245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6246_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28(v_w_6237_, v_aig_6238_, v_curr_6239_, v_n_6240_, v_d_6241_, v_wn_6242_, v_wr_6243_, v_q_6244_, v_r_6245_);
    crate::leanh::lean_dec(v_wr_6243_);
    crate::leanh::lean_dec(v_wn_6242_);
    crate::leanh::lean_dec_ref(v_n_6240_);
    crate::leanh::lean_dec(v_curr_6239_);
    return v_res_6246_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___redArg(
    mut v_aig_6247_: *mut crate::leanh::LeanObject,
    mut v_acc_6248_: *mut crate::leanh::LeanObject,
    mut v_idx_6249_: *mut crate::leanh::LeanObject,
    mut v_len_6250_: *mut crate::leanh::LeanObject,
    mut v_input_6251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: u8 = 0;
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: u8 = 0;
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: u8 = 0;
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6261_ = lean_nat_dec_lt(v_idx_6249_, v_len_6250_);
                if v___x_6261_ == 0 {
                    crate::leanh::lean_dec(v_idx_6249_);
                    v___x_6262_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6262_, 0, v_aig_6247_);
                    crate::leanh::lean_ctor_set(v___x_6262_, 1, v_acc_6248_);
                    return v___x_6262_;
                } else {
                    v_ref_6263_ = lean_array_fget_borrowed(v_input_6251_, v_idx_6249_);
                    v___x_6264_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6265_ = lean_nat_shiftr(v_ref_6263_, v___x_6264_);
                    v___x_6266_ = lean_nat_land(v___x_6264_, v_ref_6263_);
                    v___x_6267_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6268_ = lean_nat_dec_eq(v___x_6266_, v___x_6267_);
                    crate::leanh::lean_dec(v___x_6266_);
                    if v___x_6268_ == 0 {
                        v___x_6269_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6269_, 0, v___x_6265_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6269_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6261_,
                        );
                        v___y_6253_ = v___x_6269_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6270_ = 0;
                        v___x_6271_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6271_, 0, v___x_6265_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6271_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6270_,
                        );
                        v___y_6253_ = v___x_6271_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6254_, 0, v_acc_6248_);
                crate::leanh::lean_ctor_set(v___x_6254_, 1, v___y_6253_);
                v_res_6255_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_6247_, v___x_6254_);
                v_aig_6256_ = crate::leanh::lean_ctor_get(v_res_6255_, 0);
                crate::leanh::lean_inc_ref(v_aig_6256_);
                v_ref_6257_ = crate::leanh::lean_ctor_get(v_res_6255_, 1);
                crate::leanh::lean_inc_ref(v_ref_6257_);
                crate::leanh::lean_dec_ref(v_res_6255_);
                v___x_6258_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6259_ = lean_nat_add(v_idx_6249_, v___x_6258_);
                crate::leanh::lean_dec(v_idx_6249_);
                v_aig_6247_ = v_aig_6256_;
                v_acc_6248_ = v_ref_6257_;
                v_idx_6249_ = v___x_6259_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___redArg___boxed(
    mut v_aig_6272_: *mut crate::leanh::LeanObject,
    mut v_acc_6273_: *mut crate::leanh::LeanObject,
    mut v_idx_6274_: *mut crate::leanh::LeanObject,
    mut v_len_6275_: *mut crate::leanh::LeanObject,
    mut v_input_6276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6277_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___redArg(v_aig_6272_, v_acc_6273_, v_idx_6274_, v_len_6275_, v_input_6276_);
    crate::leanh::lean_dec_ref(v_input_6276_);
    crate::leanh::lean_dec(v_len_6275_);
    return v_res_6277_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___redArg(
    mut v_len_6278_: *mut crate::leanh::LeanObject,
    mut v_aig_6279_: *mut crate::leanh::LeanObject,
    mut v_vec_6280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6281_ = crate::leanh::lean_unsigned_to_nat(0);
    v_acc_6282_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__67___closed__0;
    v___x_6283_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___redArg(v_aig_6279_, v_acc_6282_, v___x_6281_, v_len_6278_, v_vec_6280_);
    return v___x_6283_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___redArg___boxed(
    mut v_len_6284_: *mut crate::leanh::LeanObject,
    mut v_aig_6285_: *mut crate::leanh::LeanObject,
    mut v_vec_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6287_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___redArg(v_len_6284_, v_aig_6285_, v_vec_6286_);
    crate::leanh::lean_dec_ref(v_vec_6286_);
    crate::leanh::lean_dec(v_len_6284_);
    return v_res_6287_;
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__38(
    mut v_aig_6288_: *mut crate::leanh::LeanObject,
    mut v_input_6289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6300_: u8 = 0;
    let mut v_gate_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6305_: u8 = 0;
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6309_: u8 = 0;
    let mut v_gate_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6313_: u8 = 0;
    let mut v___x_6314_: u8 = 0;
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut v___y_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6321_: u8 = 0;
    let mut v___y_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6328_: u8 = 0;
    let mut v_aig_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6334_: u8 = 0;
    let mut v___x_6335_: u8 = 0;
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6339_: u8 = 0;
    let mut v_aig_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6345_: u8 = 0;
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v_lhs_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6355_: u8 = 0;
    let mut v_gate_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6357_: u8 = 0;
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6360_: u8 = 0;
    let mut v_gate_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6362_: u8 = 0;
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___y_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: u8 = 0;
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: u8 = 0;
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: u8 = 0;
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: u8 = 0;
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6394_: u8 = 0;
    let mut v_isSharedCheck_6395_: u8 = 0;
    let mut v_isSharedCheck_6396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_6351_ = crate::leanh::lean_ctor_get(v_input_6289_, 0);
                v_rhs_6352_ = crate::leanh::lean_ctor_get(v_input_6289_, 1);
                v_isSharedCheck_6396_ = (!crate::leanh::lean_is_exclusive(v_input_6289_)) as u8;
                if v_isSharedCheck_6396_ == 0 {
                    v___x_6354_ = v_input_6289_;
                    v_isShared_6355_ = v_isSharedCheck_6396_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_6352_);
                    crate::leanh::lean_inc(v_lhs_6351_);
                    crate::leanh::lean_dec(v_input_6289_);
                    v___x_6354_ = crate::leanh::lean_box(0);
                    v_isShared_6355_ = v_isSharedCheck_6396_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_6294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6294_, 0, v___y_6292_);
                crate::leanh::lean_ctor_set(v___x_6294_, 1, v___y_6293_);
                v___x_6295_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v___y_6291_, v___x_6294_);
                return v___x_6295_;
            }
            2 => {
                v_invert_6300_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6298_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_6300_ == 0 {
                    v_gate_6301_ = crate::leanh::lean_ctor_get(v___y_6298_, 0);
                    v_isSharedCheck_6309_ = (!crate::leanh::lean_is_exclusive(v___y_6298_)) as u8;
                    if v_isSharedCheck_6309_ == 0 {
                        v___x_6303_ = v___y_6298_;
                        v_isShared_6304_ = v_isSharedCheck_6309_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_6301_);
                        crate::leanh::lean_dec(v___y_6298_);
                        v___x_6303_ = crate::leanh::lean_box(0);
                        v_isShared_6304_ = v_isSharedCheck_6309_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_6310_ = crate::leanh::lean_ctor_get(v___y_6298_, 0);
                    v_isSharedCheck_6318_ = (!crate::leanh::lean_is_exclusive(v___y_6298_)) as u8;
                    if v_isSharedCheck_6318_ == 0 {
                        v___x_6312_ = v___y_6298_;
                        v_isShared_6313_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_6310_);
                        crate::leanh::lean_dec(v___y_6298_);
                        v___x_6312_ = crate::leanh::lean_box(0);
                        v_isShared_6313_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6305_ = 1;
                if v_isShared_6304_ == 0 {
                    v___x_6307_ = v___x_6303_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6308_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6308_, 0, v_gate_6301_);
                    v___x_6307_ = v_reuseFailAlloc_6308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6307_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6305_,
                );
                v___y_6291_ = v___y_6297_;
                v___y_6292_ = v___y_6299_;
                v___y_6293_ = v___x_6307_;
                state = 1;
                continue;
            }
            5 => {
                v___x_6314_ = 0;
                if v_isShared_6313_ == 0 {
                    v___x_6316_ = v___x_6312_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6317_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_gate_6310_);
                    v___x_6316_ = v_reuseFailAlloc_6317_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6314_,
                );
                v___y_6291_ = v___y_6297_;
                v___y_6292_ = v___y_6299_;
                v___y_6293_ = v___x_6316_;
                state = 1;
                continue;
            }
            7 => {
                v___x_6325_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6325_, 0, v___y_6320_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6325_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_6321_,
                );
                v___x_6326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6326_, 0, v___y_6324_);
                crate::leanh::lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                v_res_6327_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v___y_6322_, v___x_6326_);
                v_invert_6328_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6323_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_6328_ == 0 {
                    v_aig_6329_ = crate::leanh::lean_ctor_get(v_res_6327_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6329_);
                    v_ref_6330_ = crate::leanh::lean_ctor_get(v_res_6327_, 1);
                    crate::leanh::lean_inc_ref(v_ref_6330_);
                    crate::leanh::lean_dec_ref(v_res_6327_);
                    v_gate_6331_ = crate::leanh::lean_ctor_get(v___y_6323_, 0);
                    v_isSharedCheck_6339_ = (!crate::leanh::lean_is_exclusive(v___y_6323_)) as u8;
                    if v_isSharedCheck_6339_ == 0 {
                        v___x_6333_ = v___y_6323_;
                        v_isShared_6334_ = v_isSharedCheck_6339_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_6331_);
                        crate::leanh::lean_dec(v___y_6323_);
                        v___x_6333_ = crate::leanh::lean_box(0);
                        v_isShared_6334_ = v_isSharedCheck_6339_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_6340_ = crate::leanh::lean_ctor_get(v_res_6327_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6340_);
                    v_ref_6341_ = crate::leanh::lean_ctor_get(v_res_6327_, 1);
                    crate::leanh::lean_inc_ref(v_ref_6341_);
                    crate::leanh::lean_dec_ref(v_res_6327_);
                    v_gate_6342_ = crate::leanh::lean_ctor_get(v___y_6323_, 0);
                    v_isSharedCheck_6350_ = (!crate::leanh::lean_is_exclusive(v___y_6323_)) as u8;
                    if v_isSharedCheck_6350_ == 0 {
                        v___x_6344_ = v___y_6323_;
                        v_isShared_6345_ = v_isSharedCheck_6350_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_6342_);
                        crate::leanh::lean_dec(v___y_6323_);
                        v___x_6344_ = crate::leanh::lean_box(0);
                        v_isShared_6345_ = v_isSharedCheck_6350_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6335_ = 1;
                if v_isShared_6334_ == 0 {
                    v___x_6337_ = v___x_6333_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6338_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_gate_6331_);
                    v___x_6337_ = v_reuseFailAlloc_6338_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6335_,
                );
                v___y_6297_ = v_aig_6329_;
                v___y_6298_ = v_ref_6330_;
                v___y_6299_ = v___x_6337_;
                state = 2;
                continue;
            }
            10 => {
                v___x_6346_ = 0;
                if v_isShared_6345_ == 0 {
                    v___x_6348_ = v___x_6344_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6349_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6349_, 0, v_gate_6342_);
                    v___x_6348_ = v_reuseFailAlloc_6349_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6348_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6346_,
                );
                v___y_6297_ = v_aig_6340_;
                v___y_6298_ = v_ref_6341_;
                v___y_6299_ = v___x_6348_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_6356_ = crate::leanh::lean_ctor_get(v_lhs_6351_, 0);
                v_invert_6357_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_6351_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6395_ = (!crate::leanh::lean_is_exclusive(v_lhs_6351_)) as u8;
                if v_isSharedCheck_6395_ == 0 {
                    v___x_6359_ = v_lhs_6351_;
                    v_isShared_6360_ = v_isSharedCheck_6395_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_6356_);
                    crate::leanh::lean_dec(v_lhs_6351_);
                    v___x_6359_ = crate::leanh::lean_box(0);
                    v_isShared_6360_ = v_isSharedCheck_6395_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_6361_ = crate::leanh::lean_ctor_get(v_rhs_6352_, 0);
                v_invert_6362_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_6352_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6394_ = (!crate::leanh::lean_is_exclusive(v_rhs_6352_)) as u8;
                if v_isSharedCheck_6394_ == 0 {
                    v___x_6364_ = v_rhs_6352_;
                    v_isShared_6365_ = v_isSharedCheck_6394_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_6361_);
                    crate::leanh::lean_dec(v_rhs_6352_);
                    v___x_6364_ = crate::leanh::lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6394_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_inc(v_gate_6356_);
                if v_isShared_6360_ == 0 {
                    v___x_6382_ = v___x_6359_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6393_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_gate_6356_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6393_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_6357_,
                    );
                    v___x_6382_ = v_reuseFailAlloc_6393_;
                    state = 18;
                    continue;
                }
            }
            15 => {
                v_res_6368_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_6288_, v___y_6367_);
                if v_invert_6357_ == 0 {
                    v_aig_6369_ = crate::leanh::lean_ctor_get(v_res_6368_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6369_);
                    v_ref_6370_ = crate::leanh::lean_ctor_get(v_res_6368_, 1);
                    crate::leanh::lean_inc_ref(v_ref_6370_);
                    crate::leanh::lean_dec_ref(v_res_6368_);
                    v___x_6371_ = 1;
                    if v_isShared_6365_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6364_, 0, v_gate_6356_);
                        v___x_6373_ = v___x_6364_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6374_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_gate_6356_);
                        v___x_6373_ = v_reuseFailAlloc_6374_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_aig_6375_ = crate::leanh::lean_ctor_get(v_res_6368_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6375_);
                    v_ref_6376_ = crate::leanh::lean_ctor_get(v_res_6368_, 1);
                    crate::leanh::lean_inc_ref(v_ref_6376_);
                    crate::leanh::lean_dec_ref(v_res_6368_);
                    v___x_6377_ = 0;
                    if v_isShared_6365_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6364_, 0, v_gate_6356_);
                        v___x_6379_ = v___x_6364_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_6380_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_gate_6356_);
                        v___x_6379_ = v_reuseFailAlloc_6380_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6371_,
                );
                v___y_6320_ = v_gate_6361_;
                v___y_6321_ = v_invert_6362_;
                v___y_6322_ = v_aig_6369_;
                v___y_6323_ = v_ref_6370_;
                v___y_6324_ = v___x_6373_;
                state = 7;
                continue;
            }
            17 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6379_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6377_,
                );
                v___y_6320_ = v_gate_6361_;
                v___y_6321_ = v_invert_6362_;
                v___y_6322_ = v_aig_6375_;
                v___y_6323_ = v_ref_6376_;
                v___y_6324_ = v___x_6379_;
                state = 7;
                continue;
            }
            18 => {
                if v_invert_6362_ == 0 {
                    v___x_6383_ = 1;
                    crate::leanh::lean_inc(v_gate_6361_);
                    v___x_6384_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6384_, 0, v_gate_6361_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6384_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6383_,
                    );
                    if v_isShared_6355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6354_, 1, v___x_6384_);
                        crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6382_);
                        v___x_6386_ = v___x_6354_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_6387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 0, v___x_6382_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 1, v___x_6384_);
                        v___x_6386_ = v_reuseFailAlloc_6387_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_6388_ = 0;
                    crate::leanh::lean_inc(v_gate_6361_);
                    v___x_6389_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6389_, 0, v_gate_6361_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6389_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6388_,
                    );
                    if v_isShared_6355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6354_, 1, v___x_6389_);
                        crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6382_);
                        v___x_6391_ = v___x_6354_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_6392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6392_, 0, v___x_6382_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6392_, 1, v___x_6389_);
                        v___x_6391_ = v_reuseFailAlloc_6392_;
                        state = 20;
                        continue;
                    }
                }
            }
            19 => {
                v___y_6367_ = v___x_6386_;
                state = 15;
                continue;
            }
            20 => {
                v___y_6367_ = v___x_6391_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___redArg(
    mut v_len_6397_: *mut crate::leanh::LeanObject,
    mut v_aig_6398_: *mut crate::leanh::LeanObject,
    mut v_idx_6399_: *mut crate::leanh::LeanObject,
    mut v_s_6400_: *mut crate::leanh::LeanObject,
    mut v_lhs_6401_: *mut crate::leanh::LeanObject,
    mut v_rhs_6402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6411_: u8 = 0;
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___y_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: u8 = 0;
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: u8 = 0;
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: u8 = 0;
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: u8 = 0;
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6420_ = lean_nat_dec_lt(v_idx_6399_, v_len_6397_);
                if v___x_6420_ == 0 {
                    crate::leanh::lean_dec(v_idx_6399_);
                    v___x_6432_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6432_, 0, v_aig_6398_);
                    crate::leanh::lean_ctor_set(v___x_6432_, 1, v_s_6400_);
                    return v___x_6432_;
                } else {
                    v_ref_6433_ = lean_array_fget_borrowed(v_lhs_6401_, v_idx_6399_);
                    v___x_6434_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6435_ = lean_nat_shiftr(v_ref_6433_, v___x_6434_);
                    v___x_6436_ = lean_nat_land(v___x_6434_, v_ref_6433_);
                    v___x_6437_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6438_ = lean_nat_dec_eq(v___x_6436_, v___x_6437_);
                    crate::leanh::lean_dec(v___x_6436_);
                    if v___x_6438_ == 0 {
                        v___x_6439_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6439_, 0, v___x_6435_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6439_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6420_,
                        );
                        v___y_6422_ = v___x_6439_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6440_ = 0;
                        v___x_6441_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6441_, 0, v___x_6435_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6441_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6440_,
                        );
                        v___y_6422_ = v___x_6441_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6406_, 0, v___y_6404_);
                crate::leanh::lean_ctor_set(v___x_6406_, 1, v___y_6405_);
                v_res_6407_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__38(v_aig_6398_, v___x_6406_);
                v_ref_6408_ = crate::leanh::lean_ctor_get(v_res_6407_, 1);
                crate::leanh::lean_inc_ref(v_ref_6408_);
                v_aig_6409_ = crate::leanh::lean_ctor_get(v_res_6407_, 0);
                crate::leanh::lean_inc_ref(v_aig_6409_);
                crate::leanh::lean_dec_ref(v_res_6407_);
                v_gate_6410_ = crate::leanh::lean_ctor_get(v_ref_6408_, 0);
                crate::leanh::lean_inc(v_gate_6410_);
                v_invert_6411_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_6408_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_6408_);
                v___x_6412_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6413_ = lean_nat_add(v_idx_6399_, v___x_6412_);
                crate::leanh::lean_dec(v_idx_6399_);
                v___x_6414_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6415_ = lean_nat_mul(v_gate_6410_, v___x_6414_);
                crate::leanh::lean_dec(v_gate_6410_);
                v___x_6416_ = l_Bool_toNat(v_invert_6411_);
                v___x_6417_ = lean_nat_lor(v___x_6415_, v___x_6416_);
                crate::leanh::lean_dec(v___x_6416_);
                crate::leanh::lean_dec(v___x_6415_);
                v_s_6418_ = lean_array_push(v_s_6400_, v___x_6417_);
                v_aig_6398_ = v_aig_6409_;
                v_idx_6399_ = v___x_6413_;
                v_s_6400_ = v_s_6418_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_6423_ = lean_array_fget_borrowed(v_rhs_6402_, v_idx_6399_);
                v___x_6424_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6425_ = lean_nat_shiftr(v_ref_6423_, v___x_6424_);
                v___x_6426_ = lean_nat_land(v___x_6424_, v_ref_6423_);
                v___x_6427_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6428_ = lean_nat_dec_eq(v___x_6426_, v___x_6427_);
                crate::leanh::lean_dec(v___x_6426_);
                if v___x_6428_ == 0 {
                    v___x_6429_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6429_, 0, v___x_6425_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6429_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6420_,
                    );
                    v___y_6404_ = v___y_6422_;
                    v___y_6405_ = v___x_6429_;
                    state = 1;
                    continue;
                } else {
                    v___x_6430_ = 0;
                    v___x_6431_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6431_, 0, v___x_6425_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6431_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6430_,
                    );
                    v___y_6404_ = v___y_6422_;
                    v___y_6405_ = v___x_6431_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___redArg___boxed(
    mut v_len_6442_: *mut crate::leanh::LeanObject,
    mut v_aig_6443_: *mut crate::leanh::LeanObject,
    mut v_idx_6444_: *mut crate::leanh::LeanObject,
    mut v_s_6445_: *mut crate::leanh::LeanObject,
    mut v_lhs_6446_: *mut crate::leanh::LeanObject,
    mut v_rhs_6447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6448_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___redArg(v_len_6442_, v_aig_6443_, v_idx_6444_, v_s_6445_, v_lhs_6446_, v_rhs_6447_);
    crate::leanh::lean_dec_ref(v_rhs_6447_);
    crate::leanh::lean_dec_ref(v_lhs_6446_);
    crate::leanh::lean_dec(v_len_6442_);
    return v_res_6448_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___redArg(
    mut v_len_6449_: *mut crate::leanh::LeanObject,
    mut v_aig_6450_: *mut crate::leanh::LeanObject,
    mut v_input_6451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_6452_ = crate::leanh::lean_ctor_get(v_input_6451_, 0);
    v_rhs_6453_ = crate::leanh::lean_ctor_get(v_input_6451_, 1);
    v___x_6454_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6455_ = lean_mk_empty_array_with_capacity(v_len_6449_);
    v___x_6456_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___redArg(v_len_6449_, v_aig_6450_, v___x_6454_, v___x_6455_, v_lhs_6452_, v_rhs_6453_);
    return v___x_6456_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___redArg___boxed(
    mut v_len_6457_: *mut crate::leanh::LeanObject,
    mut v_aig_6458_: *mut crate::leanh::LeanObject,
    mut v_input_6459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6460_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___redArg(v_len_6457_, v_aig_6458_, v_input_6459_);
    crate::leanh::lean_dec_ref(v_input_6459_);
    crate::leanh::lean_dec(v_len_6457_);
    return v_res_6460_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27(
    mut v_w_6461_: *mut crate::leanh::LeanObject,
    mut v_aig_6462_: *mut crate::leanh::LeanObject,
    mut v_pair_6463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6464_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___redArg(v_w_6461_, v_aig_6462_, v_pair_6463_);
    v_aig_6465_ = crate::leanh::lean_ctor_get(v_res_6464_, 0);
    crate::leanh::lean_inc_ref(v_aig_6465_);
    v_vec_6466_ = crate::leanh::lean_ctor_get(v_res_6464_, 1);
    crate::leanh::lean_inc_ref(v_vec_6466_);
    crate::leanh::lean_dec_ref(v_res_6464_);
    v___x_6467_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___redArg(v_w_6461_, v_aig_6465_, v_vec_6466_);
    crate::leanh::lean_dec_ref(v_vec_6466_);
    return v___x_6467_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27___boxed(
    mut v_w_6468_: *mut crate::leanh::LeanObject,
    mut v_aig_6469_: *mut crate::leanh::LeanObject,
    mut v_pair_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6471_ = l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27(v_w_6468_, v_aig_6469_, v_pair_6470_);
    crate::leanh::lean_dec_ref(v_pair_6470_);
    crate::leanh::lean_dec(v_w_6468_);
    return v_res_6471_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__14(
    mut v_w_6472_: *mut crate::leanh::LeanObject,
    mut v_aig_6473_: *mut crate::leanh::LeanObject,
    mut v_input_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6479_: u8 = 0;
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v_gate_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6495_: u8 = 0;
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6498_: u8 = 0;
    let mut v_discr_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6506_: u8 = 0;
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_unused_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_6475_ = crate::leanh::lean_ctor_get(v_input_6474_, 0);
                v_rhs_6476_ = crate::leanh::lean_ctor_get(v_input_6474_, 1);
                v_isSharedCheck_6510_ = (!crate::leanh::lean_is_exclusive(v_input_6474_)) as u8;
                if v_isSharedCheck_6510_ == 0 {
                    v___x_6478_ = v_input_6474_;
                    v_isShared_6479_ = v_isSharedCheck_6510_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_6476_);
                    crate::leanh::lean_inc(v_lhs_6475_);
                    crate::leanh::lean_dec(v_input_6474_);
                    v___x_6478_ = crate::leanh::lean_box(0);
                    v_isShared_6479_ = v_isSharedCheck_6510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6480_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6481_ = l_BitVec_ofNat(v_w_6472_, v___x_6480_);
                v_zero_6482_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_6472_, v_aig_6473_, v___x_6481_);
                crate::leanh::lean_dec(v___x_6481_);
                crate::leanh::lean_inc_ref(v_zero_6482_);
                crate::leanh::lean_inc_ref(v_rhs_6476_);
                if v_isShared_6479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6478_, 1, v_zero_6482_);
                    crate::leanh::lean_ctor_set(v___x_6478_, 0, v_rhs_6476_);
                    v___x_6484_ = v___x_6478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6509_, 0, v_rhs_6476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6509_, 1, v_zero_6482_);
                    v___x_6484_ = v_reuseFailAlloc_6509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_6485_ = l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27(v_w_6472_, v_aig_6473_, v___x_6484_);
                crate::leanh::lean_dec_ref(v___x_6484_);
                v_aig_6486_ = crate::leanh::lean_ctor_get(v_res_6485_, 0);
                crate::leanh::lean_inc_ref(v_aig_6486_);
                v_ref_6487_ = crate::leanh::lean_ctor_get(v_res_6485_, 1);
                crate::leanh::lean_inc_ref(v_ref_6487_);
                crate::leanh::lean_dec_ref(v_res_6485_);
                crate::leanh::lean_inc_ref(v_zero_6482_);
                crate::leanh::lean_inc(v_w_6472_);
                v_res_6488_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28(v_w_6472_, v_aig_6486_, v_w_6472_, v_lhs_6475_, v_rhs_6476_, v_w_6472_, v___x_6480_, v_zero_6482_, v_zero_6482_);
                v_aig_6489_ = crate::leanh::lean_ctor_get(v_res_6488_, 0);
                v_r_6490_ = crate::leanh::lean_ctor_get(v_res_6488_, 2);
                v_isSharedCheck_6507_ = (!crate::leanh::lean_is_exclusive(v_res_6488_)) as u8;
                if v_isSharedCheck_6507_ == 0 {
                    v_unused_6508_ = crate::leanh::lean_ctor_get(v_res_6488_, 1);
                    crate::leanh::lean_dec(v_unused_6508_);
                    v___x_6492_ = v_res_6488_;
                    v_isShared_6493_ = v_isSharedCheck_6507_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_r_6490_);
                    crate::leanh::lean_inc(v_aig_6489_);
                    crate::leanh::lean_dec(v_res_6488_);
                    v___x_6492_ = crate::leanh::lean_box(0);
                    v_isShared_6493_ = v_isSharedCheck_6507_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_6494_ = crate::leanh::lean_ctor_get(v_ref_6487_, 0);
                v_invert_6495_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_6487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6506_ = (!crate::leanh::lean_is_exclusive(v_ref_6487_)) as u8;
                if v_isSharedCheck_6506_ == 0 {
                    v___x_6497_ = v_ref_6487_;
                    v_isShared_6498_ = v_isSharedCheck_6506_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_6494_);
                    crate::leanh::lean_dec(v_ref_6487_);
                    v___x_6497_ = crate::leanh::lean_box(0);
                    v_isShared_6498_ = v_isSharedCheck_6506_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6498_ == 0 {
                    v_discr_6500_ = v___x_6497_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6505_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_gate_6494_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6505_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_6495_,
                    );
                    v_discr_6500_ = v_reuseFailAlloc_6505_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6492_, 1, v_lhs_6475_);
                    crate::leanh::lean_ctor_set(v___x_6492_, 0, v_discr_6500_);
                    v___x_6502_ = v___x_6492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_discr_6500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 1, v_lhs_6475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 2, v_r_6490_);
                    v___x_6502_ = v_reuseFailAlloc_6504_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6503_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6472_, v_aig_6489_, v___x_6502_);
                crate::leanh::lean_dec(v_w_6472_);
                return v___x_6503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___redArg(
    mut v_w_6511_: *mut crate::leanh::LeanObject,
    mut v_aig_6512_: *mut crate::leanh::LeanObject,
    mut v_input_6513_: *mut crate::leanh::LeanObject,
    mut v_distance_6514_: *mut crate::leanh::LeanObject,
    mut v_curr_6515_: *mut crate::leanh::LeanObject,
    mut v_s_6516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6519_: u8 = 0;
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: u8 = 0;
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: u8 = 0;
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: u8 = 0;
    let mut v___x_6545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6528_ = lean_nat_dec_lt(v_curr_6515_, v_w_6511_);
                if v___x_6528_ == 0 {
                    crate::leanh::lean_dec(v_curr_6515_);
                    v___x_6529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6529_, 0, v_aig_6512_);
                    crate::leanh::lean_ctor_set(v___x_6529_, 1, v_s_6516_);
                    return v___x_6529_;
                } else {
                    v___x_6530_ = lean_nat_add(v_distance_6514_, v_curr_6515_);
                    v___x_6531_ = lean_nat_dec_lt(v___x_6530_, v_w_6511_);
                    if v___x_6531_ == 0 {
                        crate::leanh::lean_dec(v___x_6530_);
                        v___x_6532_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6533_ = lean_nat_add(v_curr_6515_, v___x_6532_);
                        crate::leanh::lean_dec(v_curr_6515_);
                        v___x_6534_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6535_ = l_Bool_toNat(v___x_6531_);
                        v___x_6536_ = lean_nat_lor(v___x_6534_, v___x_6535_);
                        crate::leanh::lean_dec(v___x_6535_);
                        v_s_6537_ = lean_array_push(v_s_6516_, v___x_6536_);
                        v_curr_6515_ = v___x_6533_;
                        v_s_6516_ = v_s_6537_;
                        state = 0;
                        continue;
                    } else {
                        v_ref_6539_ = lean_array_fget_borrowed(v_input_6513_, v___x_6530_);
                        crate::leanh::lean_dec(v___x_6530_);
                        v___x_6540_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6541_ = lean_nat_shiftr(v_ref_6539_, v___x_6540_);
                        v___x_6542_ = lean_nat_land(v___x_6540_, v_ref_6539_);
                        v___x_6543_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6544_ = lean_nat_dec_eq(v___x_6542_, v___x_6543_);
                        crate::leanh::lean_dec(v___x_6542_);
                        if v___x_6544_ == 0 {
                            v_gate_6518_ = v___x_6541_;
                            v_invert_6519_ = v___x_6531_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6545_ = 0;
                            v_gate_6518_ = v___x_6541_;
                            v_invert_6519_ = v___x_6545_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6520_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6521_ = lean_nat_add(v_curr_6515_, v___x_6520_);
                crate::leanh::lean_dec(v_curr_6515_);
                v___x_6522_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6523_ = lean_nat_mul(v_gate_6518_, v___x_6522_);
                crate::leanh::lean_dec(v_gate_6518_);
                v___x_6524_ = l_Bool_toNat(v_invert_6519_);
                v___x_6525_ = lean_nat_lor(v___x_6523_, v___x_6524_);
                crate::leanh::lean_dec(v___x_6524_);
                crate::leanh::lean_dec(v___x_6523_);
                v_s_6526_ = lean_array_push(v_s_6516_, v___x_6525_);
                v_curr_6515_ = v___x_6521_;
                v_s_6516_ = v_s_6526_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___redArg___boxed(
    mut v_w_6546_: *mut crate::leanh::LeanObject,
    mut v_aig_6547_: *mut crate::leanh::LeanObject,
    mut v_input_6548_: *mut crate::leanh::LeanObject,
    mut v_distance_6549_: *mut crate::leanh::LeanObject,
    mut v_curr_6550_: *mut crate::leanh::LeanObject,
    mut v_s_6551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6552_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___redArg(v_w_6546_, v_aig_6547_, v_input_6548_, v_distance_6549_, v_curr_6550_, v_s_6551_);
    crate::leanh::lean_dec(v_distance_6549_);
    crate::leanh::lean_dec_ref(v_input_6548_);
    crate::leanh::lean_dec(v_w_6546_);
    return v_res_6552_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71(
    mut v_w_6553_: *mut crate::leanh::LeanObject,
    mut v_aig_6554_: *mut crate::leanh::LeanObject,
    mut v_target_6555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_6556_ = crate::leanh::lean_ctor_get(v_target_6555_, 0);
    v_distance_6557_ = crate::leanh::lean_ctor_get(v_target_6555_, 1);
    v___x_6558_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6559_ = lean_mk_empty_array_with_capacity(v_w_6553_);
    v___x_6560_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___redArg(v_w_6553_, v_aig_6554_, v_vec_6556_, v_distance_6557_, v___x_6558_, v___x_6559_);
    return v___x_6560_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71___boxed(
    mut v_w_6561_: *mut crate::leanh::LeanObject,
    mut v_aig_6562_: *mut crate::leanh::LeanObject,
    mut v_target_6563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6564_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71(v_w_6561_, v_aig_6562_, v_target_6563_);
    crate::leanh::lean_dec_ref(v_target_6563_);
    crate::leanh::lean_dec(v_w_6561_);
    return v_res_6564_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53(
    mut v_w_6565_: *mut crate::leanh::LeanObject,
    mut v_aig_6566_: *mut crate::leanh::LeanObject,
    mut v_target_6567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: u8 = 0;
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: u8 = 0;
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_6568_ = crate::leanh::lean_ctor_get(v_target_6567_, 0);
                v_lhs_6569_ = crate::leanh::lean_ctor_get(v_target_6567_, 1);
                v_rhs_6570_ = crate::leanh::lean_ctor_get(v_target_6567_, 2);
                v_pow_6571_ = crate::leanh::lean_ctor_get(v_target_6567_, 3);
                v___x_6572_ = lean_nat_dec_lt(v_pow_6571_, v_n_6568_);
                if v___x_6572_ == 0 {
                    crate::leanh::lean_inc_ref(v_lhs_6569_);
                    v___x_6573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6573_, 0, v_aig_6566_);
                    crate::leanh::lean_ctor_set(v___x_6573_, 1, v_lhs_6569_);
                    return v___x_6573_;
                } else {
                    v___x_6574_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_6575_ = lean_nat_pow(v___x_6574_, v_pow_6571_);
                    crate::leanh::lean_inc_ref(v_lhs_6569_);
                    v___x_6576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6576_, 0, v_lhs_6569_);
                    crate::leanh::lean_ctor_set(v___x_6576_, 1, v___x_6575_);
                    v_res_6577_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71(v_w_6565_, v_aig_6566_, v___x_6576_);
                    crate::leanh::lean_dec_ref_known(v___x_6576_, 2);
                    v_aig_6578_ = crate::leanh::lean_ctor_get(v_res_6577_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6578_);
                    v_vec_6579_ = crate::leanh::lean_ctor_get(v_res_6577_, 1);
                    crate::leanh::lean_inc_ref(v_vec_6579_);
                    crate::leanh::lean_dec_ref(v_res_6577_);
                    v_ref_6584_ = lean_array_fget_borrowed(v_rhs_6570_, v_pow_6571_);
                    v___x_6585_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6586_ = lean_nat_shiftr(v_ref_6584_, v___x_6585_);
                    v___x_6587_ = lean_nat_land(v___x_6585_, v_ref_6584_);
                    v___x_6588_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6589_ = lean_nat_dec_eq(v___x_6587_, v___x_6588_);
                    crate::leanh::lean_dec(v___x_6587_);
                    if v___x_6589_ == 0 {
                        v___x_6590_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6590_, 0, v___x_6586_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6590_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6572_,
                        );
                        v___y_6581_ = v___x_6590_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6591_ = 0;
                        v___x_6592_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6592_, 0, v___x_6586_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6592_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6591_,
                        );
                        v___y_6581_ = v___x_6592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_6569_);
                v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6582_, 0, v___y_6581_);
                crate::leanh::lean_ctor_set(v___x_6582_, 1, v_vec_6579_);
                crate::leanh::lean_ctor_set(v___x_6582_, 2, v_lhs_6569_);
                v___x_6583_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6565_, v_aig_6578_, v___x_6582_);
                return v___x_6583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53___boxed(
    mut v_w_6593_: *mut crate::leanh::LeanObject,
    mut v_aig_6594_: *mut crate::leanh::LeanObject,
    mut v_target_6595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6596_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53(v_w_6593_, v_aig_6594_, v_target_6595_);
    crate::leanh::lean_dec_ref(v_target_6595_);
    crate::leanh::lean_dec(v_w_6593_);
    return v_res_6596_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__54(
    mut v_w_6597_: *mut crate::leanh::LeanObject,
    mut v_n_6598_: *mut crate::leanh::LeanObject,
    mut v_aig_6599_: *mut crate::leanh::LeanObject,
    mut v_distance_6600_: *mut crate::leanh::LeanObject,
    mut v_curr_6601_: *mut crate::leanh::LeanObject,
    mut v_acc_6602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: u8 = 0;
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6603_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6604_ = lean_nat_sub(v_n_6598_, v___x_6603_);
                v___x_6605_ = lean_nat_dec_lt(v_curr_6601_, v___x_6604_);
                crate::leanh::lean_dec(v___x_6604_);
                if v___x_6605_ == 0 {
                    crate::leanh::lean_dec(v_curr_6601_);
                    crate::leanh::lean_dec_ref(v_distance_6600_);
                    crate::leanh::lean_dec(v_n_6598_);
                    v___x_6606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6606_, 0, v_aig_6599_);
                    crate::leanh::lean_ctor_set(v___x_6606_, 1, v_acc_6602_);
                    return v___x_6606_;
                } else {
                    v___x_6607_ = lean_nat_add(v_curr_6601_, v___x_6603_);
                    crate::leanh::lean_dec(v_curr_6601_);
                    crate::leanh::lean_inc(v___x_6607_);
                    crate::leanh::lean_inc_ref(v_distance_6600_);
                    crate::leanh::lean_inc(v_n_6598_);
                    v___x_6608_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6608_, 0, v_n_6598_);
                    crate::leanh::lean_ctor_set(v___x_6608_, 1, v_acc_6602_);
                    crate::leanh::lean_ctor_set(v___x_6608_, 2, v_distance_6600_);
                    crate::leanh::lean_ctor_set(v___x_6608_, 3, v___x_6607_);
                    v_res_6609_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53(v_w_6597_, v_aig_6599_, v___x_6608_);
                    crate::leanh::lean_dec_ref_known(v___x_6608_, 4);
                    v_aig_6610_ = crate::leanh::lean_ctor_get(v_res_6609_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6610_);
                    v_vec_6611_ = crate::leanh::lean_ctor_get(v_res_6609_, 1);
                    crate::leanh::lean_inc_ref(v_vec_6611_);
                    crate::leanh::lean_dec_ref(v_res_6609_);
                    v_aig_6599_ = v_aig_6610_;
                    v_curr_6601_ = v___x_6607_;
                    v_acc_6602_ = v_vec_6611_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__54___boxed(
    mut v_w_6613_: *mut crate::leanh::LeanObject,
    mut v_n_6614_: *mut crate::leanh::LeanObject,
    mut v_aig_6615_: *mut crate::leanh::LeanObject,
    mut v_distance_6616_: *mut crate::leanh::LeanObject,
    mut v_curr_6617_: *mut crate::leanh::LeanObject,
    mut v_acc_6618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6619_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__54(v_w_6613_, v_n_6614_, v_aig_6615_, v_distance_6616_, v_curr_6617_, v_acc_6618_);
    crate::leanh::lean_dec(v_w_6613_);
    return v_res_6619_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25(
    mut v_w_6620_: *mut crate::leanh::LeanObject,
    mut v_aig_6621_: *mut crate::leanh::LeanObject,
    mut v_target_6622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    v_n_6623_ = crate::leanh::lean_ctor_get(v_target_6622_, 0);
    crate::leanh::lean_inc(v_n_6623_);
    v_target_6624_ = crate::leanh::lean_ctor_get(v_target_6622_, 1);
    crate::leanh::lean_inc_ref(v_target_6624_);
    v_distance_6625_ = crate::leanh::lean_ctor_get(v_target_6622_, 2);
    crate::leanh::lean_inc_ref(v_distance_6625_);
    crate::leanh::lean_dec_ref(v_target_6622_);
    v___x_6626_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6627_ = lean_nat_dec_eq(v_n_6623_, v___x_6626_);
    if v___x_6627_ == 0 {
        let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_6625_);
        crate::leanh::lean_inc(v_n_6623_);
        v___x_6628_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6628_, 0, v_n_6623_);
        crate::leanh::lean_ctor_set(v___x_6628_, 1, v_target_6624_);
        crate::leanh::lean_ctor_set(v___x_6628_, 2, v_distance_6625_);
        crate::leanh::lean_ctor_set(v___x_6628_, 3, v___x_6626_);
        v_res_6629_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53(v_w_6620_, v_aig_6621_, v___x_6628_);
        crate::leanh::lean_dec_ref_known(v___x_6628_, 4);
        v_aig_6630_ = crate::leanh::lean_ctor_get(v_res_6629_, 0);
        crate::leanh::lean_inc_ref(v_aig_6630_);
        v_vec_6631_ = crate::leanh::lean_ctor_get(v_res_6629_, 1);
        crate::leanh::lean_inc_ref(v_vec_6631_);
        crate::leanh::lean_dec_ref(v_res_6629_);
        v___x_6632_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__54(v_w_6620_, v_n_6623_, v_aig_6630_, v_distance_6625_, v___x_6626_, v_vec_6631_);
        return v___x_6632_;
    } else {
        let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_6625_);
        crate::leanh::lean_dec(v_n_6623_);
        v___x_6633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6633_, 0, v_aig_6621_);
        crate::leanh::lean_ctor_set(v___x_6633_, 1, v_target_6624_);
        return v___x_6633_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25___boxed(
    mut v_w_6634_: *mut crate::leanh::LeanObject,
    mut v_aig_6635_: *mut crate::leanh::LeanObject,
    mut v_target_6636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6637_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25(v_w_6634_, v_aig_6635_, v_target_6636_);
    crate::leanh::lean_dec(v_w_6634_);
    return v_res_6637_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19___redArg(
    mut v_aig_6638_: *mut crate::leanh::LeanObject,
    mut v_s_6639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6640_ = l_Array_reverse___redArg(v_s_6639_);
    v___x_6641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6641_, 0, v_aig_6638_);
    crate::leanh::lean_ctor_set(v___x_6641_, 1, v___x_6640_);
    return v___x_6641_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35(
    mut v_aig_6644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6645_ = l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35___closed__0;
    return v___x_6645_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35___boxed(
    mut v_aig_6646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6647_ = l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35(v_aig_6646_);
    crate::leanh::lean_dec_ref(v_aig_6646_);
    return v_res_6647_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6648_: u8 = 0;
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6648_ = 0;
    v___x_6649_ = l_Bool_toNat(v___x_6648_);
    return v___x_6649_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6650_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__0);
    v___x_6651_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6652_ = lean_nat_lor(v___x_6651_, v___x_6650_);
    return v___x_6652_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg(
    mut v_w_6653_: *mut crate::leanh::LeanObject,
    mut v_aig_6654_: *mut crate::leanh::LeanObject,
    mut v_input_6655_: *mut crate::leanh::LeanObject,
    mut v_distance_6656_: *mut crate::leanh::LeanObject,
    mut v_curr_6657_: *mut crate::leanh::LeanObject,
    mut v_s_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6661_: u8 = 0;
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: u8 = 0;
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: u8 = 0;
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6670_ = lean_nat_dec_lt(v_curr_6657_, v_w_6653_);
                if v___x_6670_ == 0 {
                    crate::leanh::lean_dec(v_curr_6657_);
                    v___x_6671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6671_, 0, v_aig_6654_);
                    crate::leanh::lean_ctor_set(v___x_6671_, 1, v_s_6658_);
                    return v___x_6671_;
                } else {
                    v___x_6672_ = lean_nat_dec_lt(v_curr_6657_, v_distance_6656_);
                    if v___x_6672_ == 0 {
                        v___x_6673_ = lean_nat_sub(v_curr_6657_, v_distance_6656_);
                        v_ref_6674_ = lean_array_fget_borrowed(v_input_6655_, v___x_6673_);
                        crate::leanh::lean_dec(v___x_6673_);
                        v___x_6675_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6676_ = lean_nat_shiftr(v_ref_6674_, v___x_6675_);
                        v___x_6677_ = lean_nat_land(v___x_6675_, v_ref_6674_);
                        v___x_6678_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6679_ = lean_nat_dec_eq(v___x_6677_, v___x_6678_);
                        crate::leanh::lean_dec(v___x_6677_);
                        if v___x_6679_ == 0 {
                            v_gate_6660_ = v___x_6676_;
                            v_invert_6661_ = v___x_6670_;
                            state = 1;
                            continue;
                        } else {
                            v_gate_6660_ = v___x_6676_;
                            v_invert_6661_ = v___x_6672_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_6680_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6681_ = lean_nat_add(v_curr_6657_, v___x_6680_);
                        crate::leanh::lean_dec(v_curr_6657_);
                        v___x_6682_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___closed__1);
                        v_s_6683_ = lean_array_push(v_s_6658_, v___x_6682_);
                        v_curr_6657_ = v___x_6681_;
                        v_s_6658_ = v_s_6683_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6662_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6663_ = lean_nat_add(v_curr_6657_, v___x_6662_);
                crate::leanh::lean_dec(v_curr_6657_);
                v___x_6664_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6665_ = lean_nat_mul(v_gate_6660_, v___x_6664_);
                crate::leanh::lean_dec(v_gate_6660_);
                v___x_6666_ = l_Bool_toNat(v_invert_6661_);
                v___x_6667_ = lean_nat_lor(v___x_6665_, v___x_6666_);
                crate::leanh::lean_dec(v___x_6666_);
                crate::leanh::lean_dec(v___x_6665_);
                v_s_6668_ = lean_array_push(v_s_6658_, v___x_6667_);
                v_curr_6657_ = v___x_6663_;
                v_s_6658_ = v_s_6668_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg___boxed(
    mut v_w_6685_: *mut crate::leanh::LeanObject,
    mut v_aig_6686_: *mut crate::leanh::LeanObject,
    mut v_input_6687_: *mut crate::leanh::LeanObject,
    mut v_distance_6688_: *mut crate::leanh::LeanObject,
    mut v_curr_6689_: *mut crate::leanh::LeanObject,
    mut v_s_6690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6691_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg(v_w_6685_, v_aig_6686_, v_input_6687_, v_distance_6688_, v_curr_6689_, v_s_6690_);
    crate::leanh::lean_dec(v_distance_6688_);
    crate::leanh::lean_dec_ref(v_input_6687_);
    crate::leanh::lean_dec(v_w_6685_);
    return v_res_6691_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67(
    mut v_w_6692_: *mut crate::leanh::LeanObject,
    mut v_aig_6693_: *mut crate::leanh::LeanObject,
    mut v_target_6694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_6695_ = crate::leanh::lean_ctor_get(v_target_6694_, 0);
    v_distance_6696_ = crate::leanh::lean_ctor_get(v_target_6694_, 1);
    v___x_6697_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6698_ = lean_mk_empty_array_with_capacity(v_w_6692_);
    v___x_6699_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg(v_w_6692_, v_aig_6693_, v_vec_6695_, v_distance_6696_, v___x_6697_, v___x_6698_);
    return v___x_6699_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67___boxed(
    mut v_w_6700_: *mut crate::leanh::LeanObject,
    mut v_aig_6701_: *mut crate::leanh::LeanObject,
    mut v_target_6702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6703_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67(v_w_6700_, v_aig_6701_, v_target_6702_);
    crate::leanh::lean_dec_ref(v_target_6702_);
    crate::leanh::lean_dec(v_w_6700_);
    return v_res_6703_;
}
pub unsafe fn l_Std_Sat_AIG_isConstant___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34_spec__55(
    mut v_aig_6704_: *mut crate::leanh::LeanObject,
    mut v_ref_6705_: *mut crate::leanh::LeanObject,
    mut v_b_6706_: u8,
) -> u8 {
    let mut v_gate_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6708_: u8 = 0;
    let mut v_decls_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6712_: u8 = 0;
    let mut v___x_6713_: u8 = 0;
    let mut v___x_6714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_6707_ = crate::leanh::lean_ctor_get(v_ref_6705_, 0);
                v_invert_6708_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_6705_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_decls_6709_ = crate::leanh::lean_ctor_get(v_aig_6704_, 0);
                v_decl_6710_ = lean_array_fget_borrowed(v_decls_6709_, v_gate_6707_);
                if v_invert_6708_ == 0 {
                    if v_b_6706_ == 0 {
                        v___x_6714_ = 1;
                        v___y_6712_ = v___x_6714_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6712_ = v_invert_6708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_6712_ = v_b_6706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_decl_6710_) == 0 {
                    return v___y_6712_;
                } else {
                    v___x_6713_ = 0;
                    return v___x_6713_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_isConstant___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34_spec__55___boxed(
    mut v_aig_6715_: *mut crate::leanh::LeanObject,
    mut v_ref_6716_: *mut crate::leanh::LeanObject,
    mut v_b_6717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_6718_: u8 = 0;
    let mut v_res_6719_: u8 = 0;
    let mut v_r_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_6718_ = (crate::leanh::lean_unbox(v_b_6717_) as u8);
    v_res_6719_ = l_Std_Sat_AIG_isConstant___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34_spec__55(v_aig_6715_, v_ref_6716_, v_b_boxed_6718_);
    crate::leanh::lean_dec_ref(v_ref_6716_);
    crate::leanh::lean_dec_ref(v_aig_6715_);
    v_r_6720_ = crate::leanh::lean_box((v_res_6719_) as usize);
    return v_r_6720_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34(
    mut v_w_6721_: *mut crate::leanh::LeanObject,
    mut v_aig_6722_: *mut crate::leanh::LeanObject,
    mut v_lhs_6723_: *mut crate::leanh::LeanObject,
    mut v_rhs_6724_: *mut crate::leanh::LeanObject,
    mut v_curr_6725_: *mut crate::leanh::LeanObject,
    mut v_acc_6726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: u8 = 0;
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: u8 = 0;
    let mut v___x_6742_: u8 = 0;
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6749_: u8 = 0;
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: u8 = 0;
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6764_: u8 = 0;
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: u8 = 0;
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6738_ = lean_nat_dec_lt(v_curr_6725_, v_w_6721_);
                if v___x_6738_ == 0 {
                    crate::leanh::lean_dec(v_curr_6725_);
                    crate::leanh::lean_dec_ref(v_lhs_6723_);
                    v___x_6768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6768_, 0, v_aig_6722_);
                    crate::leanh::lean_ctor_set(v___x_6768_, 1, v_acc_6726_);
                    return v___x_6768_;
                } else {
                    v_ref_6769_ = lean_array_fget_borrowed(v_rhs_6724_, v_curr_6725_);
                    v___x_6770_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6771_ = lean_nat_shiftr(v_ref_6769_, v___x_6770_);
                    v___x_6772_ = lean_nat_land(v___x_6770_, v_ref_6769_);
                    v___x_6773_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6774_ = lean_nat_dec_eq(v___x_6772_, v___x_6773_);
                    crate::leanh::lean_dec(v___x_6772_);
                    if v___x_6774_ == 0 {
                        v___x_6775_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6775_, 0, v___x_6771_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6775_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6738_,
                        );
                        v___y_6740_ = v___x_6775_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6776_ = 0;
                        v___x_6777_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6777_, 0, v___x_6771_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6777_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6776_,
                        );
                        v___y_6740_ = v___x_6777_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6731_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6731_, 0, v___y_6730_);
                crate::leanh::lean_ctor_set(v___x_6731_, 1, v___y_6728_);
                crate::leanh::lean_ctor_set(v___x_6731_, 2, v_acc_6726_);
                v_res_6732_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6721_, v___y_6729_, v___x_6731_);
                v_aig_6733_ = crate::leanh::lean_ctor_get(v_res_6732_, 0);
                crate::leanh::lean_inc_ref(v_aig_6733_);
                v_vec_6734_ = crate::leanh::lean_ctor_get(v_res_6732_, 1);
                crate::leanh::lean_inc_ref(v_vec_6734_);
                crate::leanh::lean_dec_ref(v_res_6732_);
                v___x_6735_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6736_ = lean_nat_add(v_curr_6725_, v___x_6735_);
                crate::leanh::lean_dec(v_curr_6725_);
                v_aig_6722_ = v_aig_6733_;
                v_curr_6725_ = v___x_6736_;
                v_acc_6726_ = v_vec_6734_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6741_ = 0;
                v___x_6742_ = l_Std_Sat_AIG_isConstant___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34_spec__55(v_aig_6722_, v___y_6740_, v___x_6741_);
                crate::leanh::lean_dec_ref(v___y_6740_);
                if v___x_6742_ == 0 {
                    crate::leanh::lean_inc(v_curr_6725_);
                    crate::leanh::lean_inc_ref(v_lhs_6723_);
                    v___x_6743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6743_, 0, v_lhs_6723_);
                    crate::leanh::lean_ctor_set(v___x_6743_, 1, v_curr_6725_);
                    v_res_6744_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67(v_w_6721_, v_aig_6722_, v___x_6743_);
                    crate::leanh::lean_dec_ref_known(v___x_6743_, 2);
                    v_aig_6745_ = crate::leanh::lean_ctor_get(v_res_6744_, 0);
                    v_vec_6746_ = crate::leanh::lean_ctor_get(v_res_6744_, 1);
                    v_isSharedCheck_6764_ = (!crate::leanh::lean_is_exclusive(v_res_6744_)) as u8;
                    if v_isSharedCheck_6764_ == 0 {
                        v___x_6748_ = v_res_6744_;
                        v_isShared_6749_ = v_isSharedCheck_6764_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vec_6746_);
                        crate::leanh::lean_inc(v_aig_6745_);
                        crate::leanh::lean_dec(v_res_6744_);
                        v___x_6748_ = crate::leanh::lean_box(0);
                        v_isShared_6749_ = v_isSharedCheck_6764_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6765_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6766_ = lean_nat_add(v_curr_6725_, v___x_6765_);
                    crate::leanh::lean_dec(v_curr_6725_);
                    v_curr_6725_ = v___x_6766_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_acc_6726_);
                if v_isShared_6749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6748_, 0, v_acc_6726_);
                    v___x_6751_ = v___x_6748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6763_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6763_, 0, v_acc_6726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6763_, 1, v_vec_6746_);
                    v___x_6751_ = v_reuseFailAlloc_6763_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_res_6752_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_6721_, v_aig_6745_, v___x_6751_);
                v_aig_6753_ = crate::leanh::lean_ctor_get(v_res_6752_, 0);
                crate::leanh::lean_inc_ref(v_aig_6753_);
                v_vec_6754_ = crate::leanh::lean_ctor_get(v_res_6752_, 1);
                crate::leanh::lean_inc_ref(v_vec_6754_);
                crate::leanh::lean_dec_ref(v_res_6752_);
                v_ref_6755_ = lean_array_fget_borrowed(v_rhs_6724_, v_curr_6725_);
                v___x_6756_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6757_ = lean_nat_shiftr(v_ref_6755_, v___x_6756_);
                v___x_6758_ = lean_nat_land(v___x_6756_, v_ref_6755_);
                v___x_6759_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6760_ = lean_nat_dec_eq(v___x_6758_, v___x_6759_);
                crate::leanh::lean_dec(v___x_6758_);
                if v___x_6760_ == 0 {
                    v___x_6761_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6761_, 0, v___x_6757_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6761_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6738_,
                    );
                    v___y_6728_ = v_vec_6754_;
                    v___y_6729_ = v_aig_6753_;
                    v___y_6730_ = v___x_6761_;
                    state = 1;
                    continue;
                } else {
                    v___x_6762_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6762_, 0, v___x_6757_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6762_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6742_,
                    );
                    v___y_6728_ = v_vec_6754_;
                    v___y_6729_ = v_aig_6753_;
                    v___y_6730_ = v___x_6762_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34___boxed(
    mut v_w_6778_: *mut crate::leanh::LeanObject,
    mut v_aig_6779_: *mut crate::leanh::LeanObject,
    mut v_lhs_6780_: *mut crate::leanh::LeanObject,
    mut v_rhs_6781_: *mut crate::leanh::LeanObject,
    mut v_curr_6782_: *mut crate::leanh::LeanObject,
    mut v_acc_6783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6784_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34(v_w_6778_, v_aig_6779_, v_lhs_6780_, v_rhs_6781_, v_curr_6782_, v_acc_6783_);
    crate::leanh::lean_dec_ref(v_rhs_6781_);
    crate::leanh::lean_dec(v_w_6778_);
    return v_res_6784_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25(
    mut v_w_6785_: *mut crate::leanh::LeanObject,
    mut v_aig_6786_: *mut crate::leanh::LeanObject,
    mut v_input_6787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: u8 = 0;
    let mut v_lhs_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: u8 = 0;
    let mut v___x_6807_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6788_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6789_ = lean_nat_dec_eq(v_w_6785_, v___x_6788_);
                if v___x_6789_ == 0 {
                    v_lhs_6790_ = crate::leanh::lean_ctor_get(v_input_6787_, 0);
                    crate::leanh::lean_inc_ref(v_lhs_6790_);
                    v_rhs_6791_ = crate::leanh::lean_ctor_get(v_input_6787_, 1);
                    crate::leanh::lean_inc_ref(v_rhs_6791_);
                    crate::leanh::lean_dec_ref(v_input_6787_);
                    v___x_6792_ = l_BitVec_ofNat(v_w_6785_, v___x_6788_);
                    v_zero_6793_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_6785_, v_aig_6786_, v___x_6792_);
                    crate::leanh::lean_dec(v___x_6792_);
                    v_ref_6802_ = lean_array_fget_borrowed(v_rhs_6791_, v___x_6788_);
                    v___x_6803_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6804_ = lean_nat_shiftr(v_ref_6802_, v___x_6803_);
                    v___x_6805_ = lean_nat_land(v___x_6803_, v_ref_6802_);
                    v___x_6806_ = lean_nat_dec_eq(v___x_6805_, v___x_6788_);
                    crate::leanh::lean_dec(v___x_6805_);
                    if v___x_6806_ == 0 {
                        v___x_6807_ = 1;
                        v___x_6808_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6808_, 0, v___x_6804_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6808_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6807_,
                        );
                        v___y_6795_ = v___x_6808_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6809_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6809_, 0, v___x_6804_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6809_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6789_,
                        );
                        v___y_6795_ = v___x_6809_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_input_6787_);
                    v___x_6810_ = l_Std_Sat_AIG_RefVec_empty___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__35(v_aig_6786_);
                    v___x_6811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6811_, 0, v_aig_6786_);
                    crate::leanh::lean_ctor_set(v___x_6811_, 1, v___x_6810_);
                    return v___x_6811_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_6790_);
                v___x_6796_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6796_, 0, v___y_6795_);
                crate::leanh::lean_ctor_set(v___x_6796_, 1, v_lhs_6790_);
                crate::leanh::lean_ctor_set(v___x_6796_, 2, v_zero_6793_);
                v_res_6797_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6785_, v_aig_6786_, v___x_6796_);
                v_aig_6798_ = crate::leanh::lean_ctor_get(v_res_6797_, 0);
                crate::leanh::lean_inc_ref(v_aig_6798_);
                v_vec_6799_ = crate::leanh::lean_ctor_get(v_res_6797_, 1);
                crate::leanh::lean_inc_ref(v_vec_6799_);
                crate::leanh::lean_dec_ref(v_res_6797_);
                v___x_6800_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6801_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25_spec__34(v_w_6785_, v_aig_6798_, v_lhs_6790_, v_rhs_6791_, v___x_6800_, v_vec_6799_);
                crate::leanh::lean_dec_ref(v_rhs_6791_);
                return v___x_6801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25___boxed(
    mut v_w_6812_: *mut crate::leanh::LeanObject,
    mut v_aig_6813_: *mut crate::leanh::LeanObject,
    mut v_input_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6815_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25(v_w_6812_, v_aig_6813_, v_input_6814_);
    crate::leanh::lean_dec(v_w_6812_);
    return v_res_6815_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(
    mut v_w_6816_: *mut crate::leanh::LeanObject,
    mut v_aig_6817_: *mut crate::leanh::LeanObject,
    mut v_input_6818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: u8 = 0;
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6831_: u8 = 0;
    let mut v_unused_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_6819_ = crate::leanh::lean_ctor_get(v_input_6818_, 0);
                v_rhs_6820_ = crate::leanh::lean_ctor_get(v_input_6818_, 1);
                v___x_6821_ = l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(v_w_6816_, v_aig_6817_, v_lhs_6819_);
                v___x_6822_ = l_Std_Sat_AIG_RefVec_countKnown___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__22(v_w_6816_, v_aig_6817_, v_rhs_6820_);
                v___x_6823_ = lean_nat_dec_lt(v___x_6821_, v___x_6822_);
                crate::leanh::lean_dec(v___x_6822_);
                crate::leanh::lean_dec(v___x_6821_);
                if v___x_6823_ == 0 {
                    crate::leanh::lean_inc_ref(v_rhs_6820_);
                    crate::leanh::lean_inc_ref(v_lhs_6819_);
                    v_isSharedCheck_6831_ = (!crate::leanh::lean_is_exclusive(v_input_6818_)) as u8;
                    if v_isSharedCheck_6831_ == 0 {
                        v_unused_6832_ = crate::leanh::lean_ctor_get(v_input_6818_, 1);
                        crate::leanh::lean_dec(v_unused_6832_);
                        v_unused_6833_ = crate::leanh::lean_ctor_get(v_input_6818_, 0);
                        crate::leanh::lean_dec(v_unused_6833_);
                        v___x_6825_ = v_input_6818_;
                        v_isShared_6826_ = v_isSharedCheck_6831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_input_6818_);
                        v___x_6825_ = crate::leanh::lean_box(0);
                        v_isShared_6826_ = v_isSharedCheck_6831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6834_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25(v_w_6816_, v_aig_6817_, v_input_6818_);
                    return v___x_6834_;
                }
            }
            1 => {
                if v_isShared_6826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6825_, 1, v_lhs_6819_);
                    crate::leanh::lean_ctor_set(v___x_6825_, 0, v_rhs_6820_);
                    v___x_6828_ = v___x_6825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6830_, 0, v_rhs_6820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6830_, 1, v_lhs_6819_);
                    v___x_6828_ = v_reuseFailAlloc_6830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6829_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12_spec__25(v_w_6816_, v_aig_6817_, v___x_6828_);
                return v___x_6829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12___boxed(
    mut v_w_6835_: *mut crate::leanh::LeanObject,
    mut v_aig_6836_: *mut crate::leanh::LeanObject,
    mut v_input_6837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6838_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(v_w_6835_, v_aig_6836_, v_input_6837_);
    crate::leanh::lean_dec(v_w_6835_);
    return v_res_6838_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13(
    mut v_w_6839_: *mut crate::leanh::LeanObject,
    mut v_aig_6840_: *mut crate::leanh::LeanObject,
    mut v_input_6841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6846_: u8 = 0;
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6860_: u8 = 0;
    let mut v_gate_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6862_: u8 = 0;
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6865_: u8 = 0;
    let mut v_discr_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6873_: u8 = 0;
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_unused_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_6842_ = crate::leanh::lean_ctor_get(v_input_6841_, 0);
                v_rhs_6843_ = crate::leanh::lean_ctor_get(v_input_6841_, 1);
                v_isSharedCheck_6877_ = (!crate::leanh::lean_is_exclusive(v_input_6841_)) as u8;
                if v_isSharedCheck_6877_ == 0 {
                    v___x_6845_ = v_input_6841_;
                    v_isShared_6846_ = v_isSharedCheck_6877_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_6843_);
                    crate::leanh::lean_inc(v_lhs_6842_);
                    crate::leanh::lean_dec(v_input_6841_);
                    v___x_6845_ = crate::leanh::lean_box(0);
                    v_isShared_6846_ = v_isSharedCheck_6877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6847_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6848_ = l_BitVec_ofNat(v_w_6839_, v___x_6847_);
                v_zero_6849_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_6839_, v_aig_6840_, v___x_6848_);
                crate::leanh::lean_dec(v___x_6848_);
                crate::leanh::lean_inc_ref(v_zero_6849_);
                crate::leanh::lean_inc_ref(v_rhs_6843_);
                if v_isShared_6846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6845_, 1, v_zero_6849_);
                    crate::leanh::lean_ctor_set(v___x_6845_, 0, v_rhs_6843_);
                    v___x_6851_ = v___x_6845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6876_, 0, v_rhs_6843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6876_, 1, v_zero_6849_);
                    v___x_6851_ = v_reuseFailAlloc_6876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_6852_ = l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27(v_w_6839_, v_aig_6840_, v___x_6851_);
                crate::leanh::lean_dec_ref(v___x_6851_);
                v_aig_6853_ = crate::leanh::lean_ctor_get(v_res_6852_, 0);
                crate::leanh::lean_inc_ref(v_aig_6853_);
                v_ref_6854_ = crate::leanh::lean_ctor_get(v_res_6852_, 1);
                crate::leanh::lean_inc_ref(v_ref_6854_);
                crate::leanh::lean_dec_ref(v_res_6852_);
                crate::leanh::lean_inc_ref_n(v_zero_6849_, 2);
                crate::leanh::lean_inc(v_w_6839_);
                v_res_6855_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28(v_w_6839_, v_aig_6853_, v_w_6839_, v_lhs_6842_, v_rhs_6843_, v_w_6839_, v___x_6847_, v_zero_6849_, v_zero_6849_);
                crate::leanh::lean_dec_ref(v_lhs_6842_);
                v_aig_6856_ = crate::leanh::lean_ctor_get(v_res_6855_, 0);
                v_q_6857_ = crate::leanh::lean_ctor_get(v_res_6855_, 1);
                v_isSharedCheck_6874_ = (!crate::leanh::lean_is_exclusive(v_res_6855_)) as u8;
                if v_isSharedCheck_6874_ == 0 {
                    v_unused_6875_ = crate::leanh::lean_ctor_get(v_res_6855_, 2);
                    crate::leanh::lean_dec(v_unused_6875_);
                    v___x_6859_ = v_res_6855_;
                    v_isShared_6860_ = v_isSharedCheck_6874_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_q_6857_);
                    crate::leanh::lean_inc(v_aig_6856_);
                    crate::leanh::lean_dec(v_res_6855_);
                    v___x_6859_ = crate::leanh::lean_box(0);
                    v_isShared_6860_ = v_isSharedCheck_6874_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_6861_ = crate::leanh::lean_ctor_get(v_ref_6854_, 0);
                v_invert_6862_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_6854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6873_ = (!crate::leanh::lean_is_exclusive(v_ref_6854_)) as u8;
                if v_isSharedCheck_6873_ == 0 {
                    v___x_6864_ = v_ref_6854_;
                    v_isShared_6865_ = v_isSharedCheck_6873_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_6861_);
                    crate::leanh::lean_dec(v_ref_6854_);
                    v___x_6864_ = crate::leanh::lean_box(0);
                    v_isShared_6865_ = v_isSharedCheck_6873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6865_ == 0 {
                    v_discr_6867_ = v___x_6864_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6872_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_gate_6861_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6872_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_6862_,
                    );
                    v_discr_6867_ = v_reuseFailAlloc_6872_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6859_, 2, v_q_6857_);
                    crate::leanh::lean_ctor_set(v___x_6859_, 1, v_zero_6849_);
                    crate::leanh::lean_ctor_set(v___x_6859_, 0, v_discr_6867_);
                    v___x_6869_ = v___x_6859_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6871_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6871_, 0, v_discr_6867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6871_, 1, v_zero_6849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6871_, 2, v_q_6857_);
                    v___x_6869_ = v_reuseFailAlloc_6871_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6870_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_6839_, v_aig_6856_, v___x_6869_);
                crate::leanh::lean_dec(v_w_6839_);
                return v___x_6870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22___redArg(
    mut v_aig_6878_: *mut crate::leanh::LeanObject,
    mut v_target_6879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_combined_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_6880_ = crate::leanh::lean_ctor_get(v_target_6879_, 2);
    crate::leanh::lean_inc_ref(v_lhs_6880_);
    v_rhs_6881_ = crate::leanh::lean_ctor_get(v_target_6879_, 3);
    crate::leanh::lean_inc_ref(v_rhs_6881_);
    crate::leanh::lean_dec_ref(v_target_6879_);
    v_combined_6882_ = l_Array_append___redArg(v_rhs_6881_, v_lhs_6880_);
    crate::leanh::lean_dec_ref(v_lhs_6880_);
    v___x_6883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6883_, 0, v_aig_6878_);
    crate::leanh::lean_ctor_set(v___x_6883_, 1, v_combined_6882_);
    return v___x_6883_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___redArg(
    mut v_newWidth_6884_: *mut crate::leanh::LeanObject,
    mut v_w_6885_: *mut crate::leanh::LeanObject,
    mut v_input_6886_: *mut crate::leanh::LeanObject,
    mut v_start_6887_: *mut crate::leanh::LeanObject,
    mut v_curr_6888_: *mut crate::leanh::LeanObject,
    mut v_s_6889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_6892_: u8 = 0;
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: u8 = 0;
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: u8 = 0;
    let mut v___x_6911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6901_ = lean_nat_dec_lt(v_curr_6888_, v_newWidth_6884_);
                if v___x_6901_ == 0 {
                    crate::leanh::lean_dec(v_curr_6888_);
                    return v_s_6889_;
                } else {
                    v___x_6902_ = lean_nat_add(v_start_6887_, v_curr_6888_);
                    v___x_6903_ = lean_nat_dec_lt(v___x_6902_, v_w_6885_);
                    if v___x_6903_ == 0 {
                        crate::leanh::lean_dec(v___x_6902_);
                        v___x_6904_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_gate_6891_ = v___x_6904_;
                        v_invert_6892_ = v___x_6903_;
                        state = 1;
                        continue;
                    } else {
                        v_ref_6905_ = lean_array_fget_borrowed(v_input_6886_, v___x_6902_);
                        crate::leanh::lean_dec(v___x_6902_);
                        v___x_6906_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6907_ = lean_nat_shiftr(v_ref_6905_, v___x_6906_);
                        v___x_6908_ = lean_nat_land(v___x_6906_, v_ref_6905_);
                        v___x_6909_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6910_ = lean_nat_dec_eq(v___x_6908_, v___x_6909_);
                        crate::leanh::lean_dec(v___x_6908_);
                        if v___x_6910_ == 0 {
                            v_gate_6891_ = v___x_6907_;
                            v_invert_6892_ = v___x_6903_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6911_ = 0;
                            v_gate_6891_ = v___x_6907_;
                            v_invert_6892_ = v___x_6911_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6893_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6894_ = lean_nat_add(v_curr_6888_, v___x_6893_);
                crate::leanh::lean_dec(v_curr_6888_);
                v___x_6895_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6896_ = lean_nat_mul(v_gate_6891_, v___x_6895_);
                crate::leanh::lean_dec(v_gate_6891_);
                v___x_6897_ = l_Bool_toNat(v_invert_6892_);
                v___x_6898_ = lean_nat_lor(v___x_6896_, v___x_6897_);
                crate::leanh::lean_dec(v___x_6897_);
                crate::leanh::lean_dec(v___x_6896_);
                v_s_6899_ = lean_array_push(v_s_6889_, v___x_6898_);
                v_curr_6888_ = v___x_6894_;
                v_s_6889_ = v_s_6899_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___redArg___boxed(
    mut v_newWidth_6912_: *mut crate::leanh::LeanObject,
    mut v_w_6913_: *mut crate::leanh::LeanObject,
    mut v_input_6914_: *mut crate::leanh::LeanObject,
    mut v_start_6915_: *mut crate::leanh::LeanObject,
    mut v_curr_6916_: *mut crate::leanh::LeanObject,
    mut v_s_6917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6918_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___redArg(v_newWidth_6912_, v_w_6913_, v_input_6914_, v_start_6915_, v_curr_6916_, v_s_6917_);
    crate::leanh::lean_dec(v_start_6915_);
    crate::leanh::lean_dec_ref(v_input_6914_);
    crate::leanh::lean_dec(v_w_6913_);
    crate::leanh::lean_dec(v_newWidth_6912_);
    return v_res_6918_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(
    mut v_newWidth_6919_: *mut crate::leanh::LeanObject,
    mut v_aig_6920_: *mut crate::leanh::LeanObject,
    mut v_target_6921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_6922_ = crate::leanh::lean_ctor_get(v_target_6921_, 0);
    v_vec_6923_ = crate::leanh::lean_ctor_get(v_target_6921_, 1);
    v_start_6924_ = crate::leanh::lean_ctor_get(v_target_6921_, 2);
    v___x_6925_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6926_ = lean_mk_empty_array_with_capacity(v_newWidth_6919_);
    v___x_6927_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___redArg(v_newWidth_6919_, v_w_6922_, v_vec_6923_, v_start_6924_, v___x_6925_, v___x_6926_);
    v___x_6928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6928_, 0, v_aig_6920_);
    crate::leanh::lean_ctor_set(v___x_6928_, 1, v___x_6927_);
    return v___x_6928_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4___boxed(
    mut v_newWidth_6929_: *mut crate::leanh::LeanObject,
    mut v_aig_6930_: *mut crate::leanh::LeanObject,
    mut v_target_6931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6932_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(v_newWidth_6929_, v_aig_6930_, v_target_6931_);
    crate::leanh::lean_dec_ref(v_target_6931_);
    crate::leanh::lean_dec(v_newWidth_6929_);
    return v_res_6932_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___redArg(
    mut v_aig_6933_: *mut crate::leanh::LeanObject,
    mut v_w_6934_: *mut crate::leanh::LeanObject,
    mut v_len_6935_: *mut crate::leanh::LeanObject,
    mut v_iterNum_6936_: *mut crate::leanh::LeanObject,
    mut v_oldLayer_6937_: *mut crate::leanh::LeanObject,
    mut v_newLayer_6938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: u8 = 0;
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6962_: u8 = 0;
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6939_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6940_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6941_ = lean_nat_mul(v_iterNum_6936_, v___x_6940_);
                v___x_6942_ = lean_nat_sub(v_len_6935_, v___x_6941_);
                crate::leanh::lean_dec(v___x_6941_);
                v___x_6943_ = lean_nat_dec_lt(v___x_6939_, v___x_6942_);
                crate::leanh::lean_dec(v___x_6942_);
                if v___x_6943_ == 0 {
                    crate::leanh::lean_dec_ref(v_oldLayer_6937_);
                    crate::leanh::lean_dec(v_iterNum_6936_);
                    crate::leanh::lean_dec(v_w_6934_);
                    v___x_6944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6944_, 0, v_aig_6933_);
                    crate::leanh::lean_ctor_set(v___x_6944_, 1, v_newLayer_6938_);
                    return v___x_6944_;
                } else {
                    v___x_6945_ = lean_nat_mul(v_len_6935_, v_w_6934_);
                    v___x_6946_ = lean_nat_mul(v___x_6940_, v_iterNum_6936_);
                    v___x_6947_ = lean_nat_mul(v___x_6946_, v_w_6934_);
                    crate::leanh::lean_inc_ref_n(v_oldLayer_6937_, 2);
                    crate::leanh::lean_inc(v___x_6945_);
                    v___x_6948_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6948_, 0, v___x_6945_);
                    crate::leanh::lean_ctor_set(v___x_6948_, 1, v_oldLayer_6937_);
                    crate::leanh::lean_ctor_set(v___x_6948_, 2, v___x_6947_);
                    v_res_6949_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(v_w_6934_, v_aig_6933_, v___x_6948_);
                    crate::leanh::lean_dec_ref_known(v___x_6948_, 3);
                    v_aig_6950_ = crate::leanh::lean_ctor_get(v_res_6949_, 0);
                    crate::leanh::lean_inc_ref(v_aig_6950_);
                    v_vec_6951_ = crate::leanh::lean_ctor_get(v_res_6949_, 1);
                    crate::leanh::lean_inc_ref(v_vec_6951_);
                    crate::leanh::lean_dec_ref(v_res_6949_);
                    v___x_6952_ = lean_nat_mul(v_iterNum_6936_, v_w_6934_);
                    v___x_6953_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6954_ = lean_nat_add(v___x_6946_, v___x_6953_);
                    crate::leanh::lean_dec(v___x_6946_);
                    v___x_6955_ = lean_nat_mul(v___x_6954_, v_w_6934_);
                    crate::leanh::lean_dec(v___x_6954_);
                    v___x_6956_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6956_, 0, v___x_6945_);
                    crate::leanh::lean_ctor_set(v___x_6956_, 1, v_oldLayer_6937_);
                    crate::leanh::lean_ctor_set(v___x_6956_, 2, v___x_6955_);
                    v_res_6957_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(v_w_6934_, v_aig_6950_, v___x_6956_);
                    crate::leanh::lean_dec_ref_known(v___x_6956_, 3);
                    v_aig_6958_ = crate::leanh::lean_ctor_get(v_res_6957_, 0);
                    v_vec_6959_ = crate::leanh::lean_ctor_get(v_res_6957_, 1);
                    v_isSharedCheck_6975_ = (!crate::leanh::lean_is_exclusive(v_res_6957_)) as u8;
                    if v_isSharedCheck_6975_ == 0 {
                        v___x_6961_ = v_res_6957_;
                        v_isShared_6962_ = v_isSharedCheck_6975_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vec_6959_);
                        crate::leanh::lean_inc(v_aig_6958_);
                        crate::leanh::lean_dec(v_res_6957_);
                        v___x_6961_ = crate::leanh::lean_box(0);
                        v_isShared_6962_ = v_isSharedCheck_6975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6961_, 0, v_vec_6951_);
                    v___x_6964_ = v___x_6961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 0, v_vec_6951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_vec_6959_);
                    v___x_6964_ = v_reuseFailAlloc_6974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_6965_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_6934_, v_aig_6958_, v___x_6964_);
                v_aig_6966_ = crate::leanh::lean_ctor_get(v_res_6965_, 0);
                crate::leanh::lean_inc_ref(v_aig_6966_);
                v_vec_6967_ = crate::leanh::lean_ctor_get(v_res_6965_, 1);
                crate::leanh::lean_inc_ref(v_vec_6967_);
                crate::leanh::lean_dec_ref(v_res_6965_);
                crate::leanh::lean_inc(v_w_6934_);
                v___x_6968_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6968_, 0, v_w_6934_);
                crate::leanh::lean_ctor_set(v___x_6968_, 1, v___x_6952_);
                crate::leanh::lean_ctor_set(v___x_6968_, 2, v_vec_6967_);
                crate::leanh::lean_ctor_set(v___x_6968_, 3, v_newLayer_6938_);
                v_res_6969_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22___redArg(v_aig_6966_, v___x_6968_);
                v_aig_6970_ = crate::leanh::lean_ctor_get(v_res_6969_, 0);
                crate::leanh::lean_inc_ref(v_aig_6970_);
                v_vec_6971_ = crate::leanh::lean_ctor_get(v_res_6969_, 1);
                crate::leanh::lean_inc_ref(v_vec_6971_);
                crate::leanh::lean_dec_ref(v_res_6969_);
                v___x_6972_ = lean_nat_add(v_iterNum_6936_, v___x_6953_);
                crate::leanh::lean_dec(v_iterNum_6936_);
                v_aig_6933_ = v_aig_6970_;
                v_iterNum_6936_ = v___x_6972_;
                v_newLayer_6938_ = v_vec_6971_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___redArg___boxed(
    mut v_aig_6976_: *mut crate::leanh::LeanObject,
    mut v_w_6977_: *mut crate::leanh::LeanObject,
    mut v_len_6978_: *mut crate::leanh::LeanObject,
    mut v_iterNum_6979_: *mut crate::leanh::LeanObject,
    mut v_oldLayer_6980_: *mut crate::leanh::LeanObject,
    mut v_newLayer_6981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6982_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___redArg(v_aig_6976_, v_w_6977_, v_len_6978_, v_iterNum_6979_, v_oldLayer_6980_, v_newLayer_6981_);
    crate::leanh::lean_dec(v_len_6978_);
    return v_res_6982_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6983_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6984_ = l_BitVec_ofNat(v___x_6983_, v___x_6983_);
    return v___x_6984_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82(
    mut v_outWidth_6985_: *mut crate::leanh::LeanObject,
    mut v_aig_6986_: *mut crate::leanh::LeanObject,
    mut v_target_6987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldLayer_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initAcc_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_6988_ = crate::leanh::lean_ctor_get(v_target_6987_, 0);
    crate::leanh::lean_inc(v_w_6988_);
    v_len_6989_ = crate::leanh::lean_ctor_get(v_target_6987_, 1);
    crate::leanh::lean_inc(v_len_6989_);
    v_oldLayer_6990_ = crate::leanh::lean_ctor_get(v_target_6987_, 2);
    crate::leanh::lean_inc_ref(v_oldLayer_6990_);
    crate::leanh::lean_dec_ref(v_target_6987_);
    v___x_6991_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0);
    v_initAcc_6993_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v___x_6991_, v_aig_6986_, v___x_6992_);
    v___x_6994_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___redArg(v_aig_6986_, v_w_6988_, v_len_6989_, v___x_6991_, v_oldLayer_6990_, v_initAcc_6993_);
    crate::leanh::lean_dec(v_len_6989_);
    return v___x_6994_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___boxed(
    mut v_outWidth_6995_: *mut crate::leanh::LeanObject,
    mut v_aig_6996_: *mut crate::leanh::LeanObject,
    mut v_target_6997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6998_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82(v_outWidth_6995_, v_aig_6996_, v_target_6997_);
    crate::leanh::lean_dec(v_outWidth_6995_);
    return v_res_6998_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62___redArg(
    mut v_w_6999_: *mut crate::leanh::LeanObject,
    mut v_aig_7000_: *mut crate::leanh::LeanObject,
    mut v_len_7001_: *mut crate::leanh::LeanObject,
    mut v_x_7002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: u8 = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7003_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7004_ = lean_nat_dec_lt(v___x_7003_, v_len_7001_);
                if v___x_7004_ == 0 {
                    crate::leanh::lean_dec(v_len_7001_);
                    crate::leanh::lean_dec(v_w_6999_);
                    v___x_7005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7005_, 0, v_aig_7000_);
                    crate::leanh::lean_ctor_set(v___x_7005_, 1, v_x_7002_);
                    return v___x_7005_;
                } else {
                    v___x_7006_ = lean_nat_add(v_len_7001_, v___x_7003_);
                    v___x_7007_ = lean_nat_shiftr(v___x_7006_, v___x_7003_);
                    crate::leanh::lean_dec(v___x_7006_);
                    v___x_7008_ = lean_nat_mul(v___x_7007_, v_w_6999_);
                    crate::leanh::lean_inc(v_w_6999_);
                    v___x_7009_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7009_, 0, v_w_6999_);
                    crate::leanh::lean_ctor_set(v___x_7009_, 1, v_len_7001_);
                    crate::leanh::lean_ctor_set(v___x_7009_, 2, v_x_7002_);
                    v_res_7010_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82(v___x_7008_, v_aig_7000_, v___x_7009_);
                    crate::leanh::lean_dec(v___x_7008_);
                    v_aig_7011_ = crate::leanh::lean_ctor_get(v_res_7010_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7011_);
                    v_vec_7012_ = crate::leanh::lean_ctor_get(v_res_7010_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7012_);
                    crate::leanh::lean_dec_ref(v_res_7010_);
                    v_aig_7000_ = v_aig_7011_;
                    v_len_7001_ = v___x_7007_;
                    v_x_7002_ = v_vec_7012_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45(
    mut v_w_7014_: *mut crate::leanh::LeanObject,
    mut v_aig_7015_: *mut crate::leanh::LeanObject,
    mut v_target_7016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_len_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_len_7017_ = crate::leanh::lean_ctor_get(v_target_7016_, 0);
    crate::leanh::lean_inc(v_len_7017_);
    v_x_7018_ = crate::leanh::lean_ctor_get(v_target_7016_, 1);
    crate::leanh::lean_inc_ref(v_x_7018_);
    crate::leanh::lean_dec_ref(v_target_7016_);
    v___x_7019_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62___redArg(v_w_7014_, v_aig_7015_, v_len_7017_, v_x_7018_);
    return v___x_7019_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60_spec__79(
    mut v_w_7020_: *mut crate::leanh::LeanObject,
    mut v_aig_7021_: *mut crate::leanh::LeanObject,
    mut v_target_7022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7032_: u8 = 0;
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7040_: u8 = 0;
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7044_: u8 = 0;
    let mut v_reuseFailAlloc_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_7023_ = crate::leanh::lean_ctor_get(v_target_7022_, 0);
                v_x_7024_ = crate::leanh::lean_ctor_get(v_target_7022_, 1);
                v___x_7025_ = crate::leanh::lean_unsigned_to_nat(1);
                crate::leanh::lean_inc(v_start_7023_);
                crate::leanh::lean_inc_ref(v_x_7024_);
                crate::leanh::lean_inc(v_w_7020_);
                v___x_7026_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7026_, 0, v_w_7020_);
                crate::leanh::lean_ctor_set(v___x_7026_, 1, v_x_7024_);
                crate::leanh::lean_ctor_set(v___x_7026_, 2, v_start_7023_);
                v_res_7027_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(v___x_7025_, v_aig_7021_, v___x_7026_);
                crate::leanh::lean_dec_ref_known(v___x_7026_, 3);
                v_aig_7028_ = crate::leanh::lean_ctor_get(v_res_7027_, 0);
                v_vec_7029_ = crate::leanh::lean_ctor_get(v_res_7027_, 1);
                v_isSharedCheck_7046_ = (!crate::leanh::lean_is_exclusive(v_res_7027_)) as u8;
                if v_isSharedCheck_7046_ == 0 {
                    v___x_7031_ = v_res_7027_;
                    v_isShared_7032_ = v_isSharedCheck_7046_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7029_);
                    crate::leanh::lean_inc(v_aig_7028_);
                    crate::leanh::lean_dec(v_res_7027_);
                    v___x_7031_ = crate::leanh::lean_box(0);
                    v_isShared_7032_ = v_isSharedCheck_7046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7031_, 0, v___x_7025_);
                    v___x_7034_ = v___x_7031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7045_, 0, v___x_7025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7045_, 1, v_vec_7029_);
                    v___x_7034_ = v_reuseFailAlloc_7045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_7035_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85(v_w_7020_, v_aig_7028_, v___x_7034_);
                crate::leanh::lean_dec_ref(v___x_7034_);
                crate::leanh::lean_dec(v_w_7020_);
                v_aig_7036_ = crate::leanh::lean_ctor_get(v_res_7035_, 0);
                v_vec_7037_ = crate::leanh::lean_ctor_get(v_res_7035_, 1);
                v_isSharedCheck_7044_ = (!crate::leanh::lean_is_exclusive(v_res_7035_)) as u8;
                if v_isSharedCheck_7044_ == 0 {
                    v___x_7039_ = v_res_7035_;
                    v_isShared_7040_ = v_isSharedCheck_7044_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7037_);
                    crate::leanh::lean_inc(v_aig_7036_);
                    crate::leanh::lean_dec(v_res_7035_);
                    v___x_7039_ = crate::leanh::lean_box(0);
                    v_isShared_7040_ = v_isSharedCheck_7044_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7040_ == 0 {
                    v___x_7042_ = v___x_7039_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7043_, 0, v_aig_7036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7043_, 1, v_vec_7037_);
                    v___x_7042_ = v_reuseFailAlloc_7043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60_spec__79___boxed(
    mut v_w_7047_: *mut crate::leanh::LeanObject,
    mut v_aig_7048_: *mut crate::leanh::LeanObject,
    mut v_target_7049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7050_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60_spec__79(v_w_7047_, v_aig_7048_, v_target_7049_);
    crate::leanh::lean_dec_ref(v_target_7049_);
    return v_res_7050_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60___redArg(
    mut v_aig_7051_: *mut crate::leanh::LeanObject,
    mut v_w_7052_: *mut crate::leanh::LeanObject,
    mut v_idx_7053_: *mut crate::leanh::LeanObject,
    mut v_x_7054_: *mut crate::leanh::LeanObject,
    mut v_acc_7055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7056_: u8 = 0;
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7056_ = lean_nat_dec_lt(v_idx_7053_, v_w_7052_);
                if v___x_7056_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_7054_);
                    crate::leanh::lean_dec(v_idx_7053_);
                    crate::leanh::lean_dec(v_w_7052_);
                    v___x_7057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7057_, 0, v_aig_7051_);
                    crate::leanh::lean_ctor_set(v___x_7057_, 1, v_acc_7055_);
                    return v___x_7057_;
                } else {
                    crate::leanh::lean_inc_ref(v_x_7054_);
                    crate::leanh::lean_inc(v_idx_7053_);
                    v___x_7058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7058_, 0, v_idx_7053_);
                    crate::leanh::lean_ctor_set(v___x_7058_, 1, v_x_7054_);
                    crate::leanh::lean_inc(v_w_7052_);
                    v_res_7059_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60_spec__79(v_w_7052_, v_aig_7051_, v___x_7058_);
                    crate::leanh::lean_dec_ref_known(v___x_7058_, 2);
                    v_aig_7060_ = crate::leanh::lean_ctor_get(v_res_7059_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7060_);
                    v_vec_7061_ = crate::leanh::lean_ctor_get(v_res_7059_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7061_);
                    crate::leanh::lean_dec_ref(v_res_7059_);
                    v_acc_7062_ = l_Array_append___redArg(v_acc_7055_, v_vec_7061_);
                    crate::leanh::lean_dec_ref(v_vec_7061_);
                    v___x_7063_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7064_ = lean_nat_add(v_idx_7053_, v___x_7063_);
                    crate::leanh::lean_dec(v_idx_7053_);
                    v_aig_7051_ = v_aig_7060_;
                    v_idx_7053_ = v___x_7064_;
                    v_acc_7055_ = v_acc_7062_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44(
    mut v_outWidth_7066_: *mut crate::leanh::LeanObject,
    mut v_aig_7067_: *mut crate::leanh::LeanObject,
    mut v_target_7068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initAcc_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_7069_ = crate::leanh::lean_ctor_get(v_target_7068_, 0);
    crate::leanh::lean_inc(v_w_7069_);
    v_x_7070_ = crate::leanh::lean_ctor_get(v_target_7068_, 1);
    crate::leanh::lean_inc_ref(v_x_7070_);
    crate::leanh::lean_dec_ref(v_target_7068_);
    v___x_7071_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82___closed__0);
    v_initAcc_7073_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v___x_7071_, v_aig_7067_, v___x_7072_);
    v___x_7074_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60___redArg(v_aig_7067_, v_w_7069_, v___x_7071_, v_x_7070_, v_initAcc_7073_);
    return v___x_7074_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44___boxed(
    mut v_outWidth_7075_: *mut crate::leanh::LeanObject,
    mut v_aig_7076_: *mut crate::leanh::LeanObject,
    mut v_target_7077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7078_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44(v_outWidth_7075_, v_aig_7076_, v_target_7077_);
    crate::leanh::lean_dec(v_outWidth_7075_);
    return v_res_7078_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21(
    mut v_w_7079_: *mut crate::leanh::LeanObject,
    mut v_aig_7080_: *mut crate::leanh::LeanObject,
    mut v_x_7081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: u8 = 0;
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: u8 = 0;
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7097_: u8 = 0;
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7082_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7083_ = lean_nat_dec_lt(v___x_7082_, v_w_7079_);
                if v___x_7083_ == 0 {
                    v___x_7084_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7085_ = lean_nat_dec_lt(v___x_7084_, v_w_7079_);
                    if v___x_7085_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_7081_);
                        v___x_7086_ = l_BitVec_ofNat(v_w_7079_, v___x_7084_);
                        v_zero_7087_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_7079_, v_aig_7080_, v___x_7086_);
                        crate::leanh::lean_dec(v___x_7086_);
                        crate::leanh::lean_dec(v_w_7079_);
                        v___x_7088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7088_, 0, v_aig_7080_);
                        crate::leanh::lean_ctor_set(v___x_7088_, 1, v_zero_7087_);
                        return v___x_7088_;
                    } else {
                        crate::leanh::lean_dec(v_w_7079_);
                        v___x_7089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7089_, 0, v_aig_7080_);
                        crate::leanh::lean_ctor_set(v___x_7089_, 1, v_x_7081_);
                        return v___x_7089_;
                    }
                } else {
                    v___x_7090_ = lean_nat_mul(v_w_7079_, v_w_7079_);
                    crate::leanh::lean_inc(v_w_7079_);
                    v___x_7091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7091_, 0, v_w_7079_);
                    crate::leanh::lean_ctor_set(v___x_7091_, 1, v_x_7081_);
                    v_res_7092_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44(v___x_7090_, v_aig_7080_, v___x_7091_);
                    crate::leanh::lean_dec(v___x_7090_);
                    v_aig_7093_ = crate::leanh::lean_ctor_get(v_res_7092_, 0);
                    v_vec_7094_ = crate::leanh::lean_ctor_get(v_res_7092_, 1);
                    v_isSharedCheck_7102_ = (!crate::leanh::lean_is_exclusive(v_res_7092_)) as u8;
                    if v_isSharedCheck_7102_ == 0 {
                        v___x_7096_ = v_res_7092_;
                        v_isShared_7097_ = v_isSharedCheck_7102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vec_7094_);
                        crate::leanh::lean_inc(v_aig_7093_);
                        crate::leanh::lean_dec(v_res_7092_);
                        v___x_7096_ = crate::leanh::lean_box(0);
                        v_isShared_7097_ = v_isSharedCheck_7102_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_w_7079_);
                if v_isShared_7097_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7096_, 0, v_w_7079_);
                    v___x_7099_ = v___x_7096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7101_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7101_, 0, v_w_7079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7101_, 1, v_vec_7094_);
                    v___x_7099_ = v_reuseFailAlloc_7101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7100_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45(v_w_7079_, v_aig_7093_, v___x_7099_);
                return v___x_7100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___redArg(
    mut v_len_7103_: *mut crate::leanh::LeanObject,
    mut v_aig_7104_: *mut crate::leanh::LeanObject,
    mut v_idx_7105_: *mut crate::leanh::LeanObject,
    mut v_s_7106_: *mut crate::leanh::LeanObject,
    mut v_lhs_7107_: *mut crate::leanh::LeanObject,
    mut v_rhs_7108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7117_: u8 = 0;
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: u8 = 0;
    let mut v___y_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: u8 = 0;
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: u8 = 0;
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: u8 = 0;
    let mut v___x_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: u8 = 0;
    let mut v___x_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7126_ = lean_nat_dec_lt(v_idx_7105_, v_len_7103_);
                if v___x_7126_ == 0 {
                    crate::leanh::lean_dec(v_idx_7105_);
                    v___x_7138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7138_, 0, v_aig_7104_);
                    crate::leanh::lean_ctor_set(v___x_7138_, 1, v_s_7106_);
                    return v___x_7138_;
                } else {
                    v_ref_7139_ = lean_array_fget_borrowed(v_lhs_7107_, v_idx_7105_);
                    v___x_7140_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7141_ = lean_nat_shiftr(v_ref_7139_, v___x_7140_);
                    v___x_7142_ = lean_nat_land(v___x_7140_, v_ref_7139_);
                    v___x_7143_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7144_ = lean_nat_dec_eq(v___x_7142_, v___x_7143_);
                    crate::leanh::lean_dec(v___x_7142_);
                    if v___x_7144_ == 0 {
                        v___x_7145_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7145_, 0, v___x_7141_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7145_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7126_,
                        );
                        v___y_7128_ = v___x_7145_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7146_ = 0;
                        v___x_7147_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7147_, 0, v___x_7141_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7147_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7146_,
                        );
                        v___y_7128_ = v___x_7147_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7112_, 0, v___y_7110_);
                crate::leanh::lean_ctor_set(v___x_7112_, 1, v___y_7111_);
                v_res_7113_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5(v_aig_7104_, v___x_7112_);
                v_ref_7114_ = crate::leanh::lean_ctor_get(v_res_7113_, 1);
                crate::leanh::lean_inc_ref(v_ref_7114_);
                v_aig_7115_ = crate::leanh::lean_ctor_get(v_res_7113_, 0);
                crate::leanh::lean_inc_ref(v_aig_7115_);
                crate::leanh::lean_dec_ref(v_res_7113_);
                v_gate_7116_ = crate::leanh::lean_ctor_get(v_ref_7114_, 0);
                crate::leanh::lean_inc(v_gate_7116_);
                v_invert_7117_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_7114_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_7114_);
                v___x_7118_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7119_ = lean_nat_add(v_idx_7105_, v___x_7118_);
                crate::leanh::lean_dec(v_idx_7105_);
                v___x_7120_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7121_ = lean_nat_mul(v_gate_7116_, v___x_7120_);
                crate::leanh::lean_dec(v_gate_7116_);
                v___x_7122_ = l_Bool_toNat(v_invert_7117_);
                v___x_7123_ = lean_nat_lor(v___x_7121_, v___x_7122_);
                crate::leanh::lean_dec(v___x_7122_);
                crate::leanh::lean_dec(v___x_7121_);
                v_s_7124_ = lean_array_push(v_s_7106_, v___x_7123_);
                v_aig_7104_ = v_aig_7115_;
                v_idx_7105_ = v___x_7119_;
                v_s_7106_ = v_s_7124_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_7129_ = lean_array_fget_borrowed(v_rhs_7108_, v_idx_7105_);
                v___x_7130_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7131_ = lean_nat_shiftr(v_ref_7129_, v___x_7130_);
                v___x_7132_ = lean_nat_land(v___x_7130_, v_ref_7129_);
                v___x_7133_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7134_ = lean_nat_dec_eq(v___x_7132_, v___x_7133_);
                crate::leanh::lean_dec(v___x_7132_);
                if v___x_7134_ == 0 {
                    v___x_7135_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7135_, 0, v___x_7131_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7135_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7126_,
                    );
                    v___y_7110_ = v___y_7128_;
                    v___y_7111_ = v___x_7135_;
                    state = 1;
                    continue;
                } else {
                    v___x_7136_ = 0;
                    v___x_7137_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7137_, 0, v___x_7131_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7137_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7136_,
                    );
                    v___y_7110_ = v___y_7128_;
                    v___y_7111_ = v___x_7137_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___redArg___boxed(
    mut v_len_7148_: *mut crate::leanh::LeanObject,
    mut v_aig_7149_: *mut crate::leanh::LeanObject,
    mut v_idx_7150_: *mut crate::leanh::LeanObject,
    mut v_s_7151_: *mut crate::leanh::LeanObject,
    mut v_lhs_7152_: *mut crate::leanh::LeanObject,
    mut v_rhs_7153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7154_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___redArg(v_len_7148_, v_aig_7149_, v_idx_7150_, v_s_7151_, v_lhs_7152_, v_rhs_7153_);
    crate::leanh::lean_dec_ref(v_rhs_7153_);
    crate::leanh::lean_dec_ref(v_lhs_7152_);
    crate::leanh::lean_dec(v_len_7148_);
    return v_res_7154_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___redArg(
    mut v_len_7155_: *mut crate::leanh::LeanObject,
    mut v_aig_7156_: *mut crate::leanh::LeanObject,
    mut v_input_7157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_7158_ = crate::leanh::lean_ctor_get(v_input_7157_, 0);
    v_rhs_7159_ = crate::leanh::lean_ctor_get(v_input_7157_, 1);
    v___x_7160_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7161_ = lean_mk_empty_array_with_capacity(v_len_7155_);
    v___x_7162_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___redArg(v_len_7155_, v_aig_7156_, v___x_7160_, v___x_7161_, v_lhs_7158_, v_rhs_7159_);
    return v___x_7162_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___redArg___boxed(
    mut v_len_7163_: *mut crate::leanh::LeanObject,
    mut v_aig_7164_: *mut crate::leanh::LeanObject,
    mut v_input_7165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7166_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___redArg(
            v_len_7163_,
            v_aig_7164_,
            v_input_7165_,
        );
    crate::leanh::lean_dec_ref(v_input_7165_);
    crate::leanh::lean_dec(v_len_7163_);
    return v_res_7166_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___redArg(
    mut v_len_7167_: *mut crate::leanh::LeanObject,
    mut v_aig_7168_: *mut crate::leanh::LeanObject,
    mut v_idx_7169_: *mut crate::leanh::LeanObject,
    mut v_s_7170_: *mut crate::leanh::LeanObject,
    mut v_lhs_7171_: *mut crate::leanh::LeanObject,
    mut v_rhs_7172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7181_: u8 = 0;
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: u8 = 0;
    let mut v___y_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: u8 = 0;
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: u8 = 0;
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: u8 = 0;
    let mut v___x_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: u8 = 0;
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7190_ = lean_nat_dec_lt(v_idx_7169_, v_len_7167_);
                if v___x_7190_ == 0 {
                    crate::leanh::lean_dec(v_idx_7169_);
                    v___x_7202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7202_, 0, v_aig_7168_);
                    crate::leanh::lean_ctor_set(v___x_7202_, 1, v_s_7170_);
                    return v___x_7202_;
                } else {
                    v_ref_7203_ = lean_array_fget_borrowed(v_lhs_7171_, v_idx_7169_);
                    v___x_7204_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7205_ = lean_nat_shiftr(v_ref_7203_, v___x_7204_);
                    v___x_7206_ = lean_nat_land(v___x_7204_, v_ref_7203_);
                    v___x_7207_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7208_ = lean_nat_dec_eq(v___x_7206_, v___x_7207_);
                    crate::leanh::lean_dec(v___x_7206_);
                    if v___x_7208_ == 0 {
                        v___x_7209_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7209_, 0, v___x_7205_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7209_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7190_,
                        );
                        v___y_7192_ = v___x_7209_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7210_ = 0;
                        v___x_7211_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7211_, 0, v___x_7205_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7211_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7210_,
                        );
                        v___y_7192_ = v___x_7211_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7176_, 0, v___y_7174_);
                crate::leanh::lean_ctor_set(v___x_7176_, 1, v___y_7175_);
                v_res_7177_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__7(v_aig_7168_, v___x_7176_);
                v_ref_7178_ = crate::leanh::lean_ctor_get(v_res_7177_, 1);
                crate::leanh::lean_inc_ref(v_ref_7178_);
                v_aig_7179_ = crate::leanh::lean_ctor_get(v_res_7177_, 0);
                crate::leanh::lean_inc_ref(v_aig_7179_);
                crate::leanh::lean_dec_ref(v_res_7177_);
                v_gate_7180_ = crate::leanh::lean_ctor_get(v_ref_7178_, 0);
                crate::leanh::lean_inc(v_gate_7180_);
                v_invert_7181_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_7178_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_7178_);
                v___x_7182_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7183_ = lean_nat_add(v_idx_7169_, v___x_7182_);
                crate::leanh::lean_dec(v_idx_7169_);
                v___x_7184_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7185_ = lean_nat_mul(v_gate_7180_, v___x_7184_);
                crate::leanh::lean_dec(v_gate_7180_);
                v___x_7186_ = l_Bool_toNat(v_invert_7181_);
                v___x_7187_ = lean_nat_lor(v___x_7185_, v___x_7186_);
                crate::leanh::lean_dec(v___x_7186_);
                crate::leanh::lean_dec(v___x_7185_);
                v_s_7188_ = lean_array_push(v_s_7170_, v___x_7187_);
                v_aig_7168_ = v_aig_7179_;
                v_idx_7169_ = v___x_7183_;
                v_s_7170_ = v_s_7188_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_7193_ = lean_array_fget_borrowed(v_rhs_7172_, v_idx_7169_);
                v___x_7194_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7195_ = lean_nat_shiftr(v_ref_7193_, v___x_7194_);
                v___x_7196_ = lean_nat_land(v___x_7194_, v_ref_7193_);
                v___x_7197_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7198_ = lean_nat_dec_eq(v___x_7196_, v___x_7197_);
                crate::leanh::lean_dec(v___x_7196_);
                if v___x_7198_ == 0 {
                    v___x_7199_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7199_, 0, v___x_7195_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7190_,
                    );
                    v___y_7174_ = v___y_7192_;
                    v___y_7175_ = v___x_7199_;
                    state = 1;
                    continue;
                } else {
                    v___x_7200_ = 0;
                    v___x_7201_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7201_, 0, v___x_7195_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7201_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7200_,
                    );
                    v___y_7174_ = v___y_7192_;
                    v___y_7175_ = v___x_7201_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___redArg___boxed(
    mut v_len_7212_: *mut crate::leanh::LeanObject,
    mut v_aig_7213_: *mut crate::leanh::LeanObject,
    mut v_idx_7214_: *mut crate::leanh::LeanObject,
    mut v_s_7215_: *mut crate::leanh::LeanObject,
    mut v_lhs_7216_: *mut crate::leanh::LeanObject,
    mut v_rhs_7217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7218_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___redArg(v_len_7212_, v_aig_7213_, v_idx_7214_, v_s_7215_, v_lhs_7216_, v_rhs_7217_);
    crate::leanh::lean_dec_ref(v_rhs_7217_);
    crate::leanh::lean_dec_ref(v_lhs_7216_);
    crate::leanh::lean_dec(v_len_7212_);
    return v_res_7218_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___redArg(
    mut v_len_7219_: *mut crate::leanh::LeanObject,
    mut v_aig_7220_: *mut crate::leanh::LeanObject,
    mut v_input_7221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_7222_ = crate::leanh::lean_ctor_get(v_input_7221_, 0);
    v_rhs_7223_ = crate::leanh::lean_ctor_get(v_input_7221_, 1);
    v___x_7224_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7225_ = lean_mk_empty_array_with_capacity(v_len_7219_);
    v___x_7226_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___redArg(v_len_7219_, v_aig_7220_, v___x_7224_, v___x_7225_, v_lhs_7222_, v_rhs_7223_);
    return v___x_7226_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___redArg___boxed(
    mut v_len_7227_: *mut crate::leanh::LeanObject,
    mut v_aig_7228_: *mut crate::leanh::LeanObject,
    mut v_input_7229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7230_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___redArg(
            v_len_7227_,
            v_aig_7228_,
            v_input_7229_,
        );
    crate::leanh::lean_dec_ref(v_input_7229_);
    crate::leanh::lean_dec(v_len_7227_);
    return v_res_7230_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___redArg(
    mut v_n_7231_: *mut crate::leanh::LeanObject,
    mut v_input_7232_: *mut crate::leanh::LeanObject,
    mut v_curr_7233_: *mut crate::leanh::LeanObject,
    mut v_s_7234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7235_: u8 = 0;
    let mut v_s_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7235_ = lean_nat_dec_lt(v_curr_7233_, v_n_7231_);
                if v___x_7235_ == 0 {
                    crate::leanh::lean_dec(v_curr_7233_);
                    return v_s_7234_;
                } else {
                    v_s_7236_ = l_Array_append___redArg(v_s_7234_, v_input_7232_);
                    v___x_7237_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7238_ = lean_nat_add(v_curr_7233_, v___x_7237_);
                    crate::leanh::lean_dec(v_curr_7233_);
                    v_curr_7233_ = v___x_7238_;
                    v_s_7234_ = v_s_7236_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___redArg___boxed(
    mut v_n_7240_: *mut crate::leanh::LeanObject,
    mut v_input_7241_: *mut crate::leanh::LeanObject,
    mut v_curr_7242_: *mut crate::leanh::LeanObject,
    mut v_s_7243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7244_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___redArg(v_n_7240_, v_input_7241_, v_curr_7242_, v_s_7243_);
    crate::leanh::lean_dec_ref(v_input_7241_);
    crate::leanh::lean_dec(v_n_7240_);
    return v_res_7244_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23(
    mut v_newWidth_7245_: *mut crate::leanh::LeanObject,
    mut v_aig_7246_: *mut crate::leanh::LeanObject,
    mut v_target_7247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_7248_ = crate::leanh::lean_ctor_get(v_target_7247_, 1);
    v_inner_7249_ = crate::leanh::lean_ctor_get(v_target_7247_, 2);
    v___x_7250_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7251_ = lean_mk_empty_array_with_capacity(v_newWidth_7245_);
    v_ref_7252_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___redArg(v_n_7248_, v_inner_7249_, v___x_7250_, v___x_7251_);
    v___x_7253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7253_, 0, v_aig_7246_);
    crate::leanh::lean_ctor_set(v___x_7253_, 1, v_ref_7252_);
    return v___x_7253_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23___boxed(
    mut v_newWidth_7254_: *mut crate::leanh::LeanObject,
    mut v_aig_7255_: *mut crate::leanh::LeanObject,
    mut v_target_7256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7257_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23(v_newWidth_7254_, v_aig_7255_, v_target_7256_);
    crate::leanh::lean_dec_ref(v_target_7256_);
    crate::leanh::lean_dec(v_newWidth_7254_);
    return v_res_7257_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___redArg(
    mut v_w_7258_: *mut crate::leanh::LeanObject,
    mut v_input_7259_: *mut crate::leanh::LeanObject,
    mut v_distance_7260_: *mut crate::leanh::LeanObject,
    mut v_curr_7261_: *mut crate::leanh::LeanObject,
    mut v_s_7262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7265_: u8 = 0;
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7276_: u8 = 0;
    let mut v___x_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: u8 = 0;
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: u8 = 0;
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: u8 = 0;
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: u8 = 0;
    let mut v___x_7303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7285_ = lean_nat_dec_lt(v_curr_7261_, v_w_7258_);
                if v___x_7285_ == 0 {
                    crate::leanh::lean_dec(v_curr_7261_);
                    return v_s_7262_;
                } else {
                    v___x_7286_ = lean_nat_mod(v_distance_7260_, v_w_7258_);
                    v___x_7287_ = lean_nat_dec_lt(v_curr_7261_, v___x_7286_);
                    if v___x_7287_ == 0 {
                        v___x_7288_ = lean_nat_sub(v_curr_7261_, v___x_7286_);
                        crate::leanh::lean_dec(v___x_7286_);
                        v_ref_7289_ = lean_array_fget_borrowed(v_input_7259_, v___x_7288_);
                        crate::leanh::lean_dec(v___x_7288_);
                        v___x_7290_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7291_ = lean_nat_shiftr(v_ref_7289_, v___x_7290_);
                        v___x_7292_ = lean_nat_land(v___x_7290_, v_ref_7289_);
                        v___x_7293_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7294_ = lean_nat_dec_eq(v___x_7292_, v___x_7293_);
                        crate::leanh::lean_dec(v___x_7292_);
                        if v___x_7294_ == 0 {
                            v_gate_7264_ = v___x_7291_;
                            v_invert_7265_ = v___x_7285_;
                            state = 1;
                            continue;
                        } else {
                            v_gate_7264_ = v___x_7291_;
                            v_invert_7265_ = v___x_7287_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7295_ = lean_nat_sub(v_w_7258_, v___x_7286_);
                        crate::leanh::lean_dec(v___x_7286_);
                        v___x_7296_ = lean_nat_add(v___x_7295_, v_curr_7261_);
                        crate::leanh::lean_dec(v___x_7295_);
                        v_ref_7297_ = lean_array_fget_borrowed(v_input_7259_, v___x_7296_);
                        crate::leanh::lean_dec(v___x_7296_);
                        v___x_7298_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7299_ = lean_nat_shiftr(v_ref_7297_, v___x_7298_);
                        v___x_7300_ = lean_nat_land(v___x_7298_, v_ref_7297_);
                        v___x_7301_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7302_ = lean_nat_dec_eq(v___x_7300_, v___x_7301_);
                        crate::leanh::lean_dec(v___x_7300_);
                        if v___x_7302_ == 0 {
                            v_gate_7275_ = v___x_7299_;
                            v_invert_7276_ = v___x_7287_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7303_ = 0;
                            v_gate_7275_ = v___x_7299_;
                            v_invert_7276_ = v___x_7303_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7266_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7267_ = lean_nat_add(v_curr_7261_, v___x_7266_);
                crate::leanh::lean_dec(v_curr_7261_);
                v___x_7268_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7269_ = lean_nat_mul(v_gate_7264_, v___x_7268_);
                crate::leanh::lean_dec(v_gate_7264_);
                v___x_7270_ = l_Bool_toNat(v_invert_7265_);
                v___x_7271_ = lean_nat_lor(v___x_7269_, v___x_7270_);
                crate::leanh::lean_dec(v___x_7270_);
                crate::leanh::lean_dec(v___x_7269_);
                v_s_7272_ = lean_array_push(v_s_7262_, v___x_7271_);
                v_curr_7261_ = v___x_7267_;
                v_s_7262_ = v_s_7272_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7277_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7278_ = lean_nat_add(v_curr_7261_, v___x_7277_);
                crate::leanh::lean_dec(v_curr_7261_);
                v___x_7279_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7280_ = lean_nat_mul(v_gate_7275_, v___x_7279_);
                crate::leanh::lean_dec(v_gate_7275_);
                v___x_7281_ = l_Bool_toNat(v_invert_7276_);
                v___x_7282_ = lean_nat_lor(v___x_7280_, v___x_7281_);
                crate::leanh::lean_dec(v___x_7281_);
                crate::leanh::lean_dec(v___x_7280_);
                v_s_7283_ = lean_array_push(v_s_7262_, v___x_7282_);
                v_curr_7261_ = v___x_7278_;
                v_s_7262_ = v_s_7283_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___redArg___boxed(
    mut v_w_7304_: *mut crate::leanh::LeanObject,
    mut v_input_7305_: *mut crate::leanh::LeanObject,
    mut v_distance_7306_: *mut crate::leanh::LeanObject,
    mut v_curr_7307_: *mut crate::leanh::LeanObject,
    mut v_s_7308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7309_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___redArg(v_w_7304_, v_input_7305_, v_distance_7306_, v_curr_7307_, v_s_7308_);
    crate::leanh::lean_dec(v_distance_7306_);
    crate::leanh::lean_dec_ref(v_input_7305_);
    crate::leanh::lean_dec(v_w_7304_);
    return v_res_7309_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16(
    mut v_w_7310_: *mut crate::leanh::LeanObject,
    mut v_aig_7311_: *mut crate::leanh::LeanObject,
    mut v_target_7312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7317_: u8 = 0;
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vec_7313_ = crate::leanh::lean_ctor_get(v_target_7312_, 0);
                v_distance_7314_ = crate::leanh::lean_ctor_get(v_target_7312_, 1);
                v_isSharedCheck_7324_ = (!crate::leanh::lean_is_exclusive(v_target_7312_)) as u8;
                if v_isSharedCheck_7324_ == 0 {
                    v___x_7316_ = v_target_7312_;
                    v_isShared_7317_ = v_isSharedCheck_7324_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_distance_7314_);
                    crate::leanh::lean_inc(v_vec_7313_);
                    crate::leanh::lean_dec(v_target_7312_);
                    v___x_7316_ = crate::leanh::lean_box(0);
                    v_isShared_7317_ = v_isSharedCheck_7324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7318_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7319_ = lean_mk_empty_array_with_capacity(v_w_7310_);
                v___x_7320_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___redArg(v_w_7310_, v_vec_7313_, v_distance_7314_, v___x_7318_, v___x_7319_);
                crate::leanh::lean_dec(v_distance_7314_);
                crate::leanh::lean_dec_ref(v_vec_7313_);
                if v_isShared_7317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7316_, 1, v___x_7320_);
                    crate::leanh::lean_ctor_set(v___x_7316_, 0, v_aig_7311_);
                    v___x_7322_ = v___x_7316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7323_, 0, v_aig_7311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7323_, 1, v___x_7320_);
                    v___x_7322_ = v_reuseFailAlloc_7323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16___boxed(
    mut v_w_7325_: *mut crate::leanh::LeanObject,
    mut v_aig_7326_: *mut crate::leanh::LeanObject,
    mut v_target_7327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7328_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16(v_w_7325_, v_aig_7326_, v_target_7327_);
    crate::leanh::lean_dec(v_w_7325_);
    return v_res_7328_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50(
    mut v_w_7329_: *mut crate::leanh::LeanObject,
    mut v_aig_7330_: *mut crate::leanh::LeanObject,
    mut v_target_7331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: u8 = 0;
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: u8 = 0;
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: u8 = 0;
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_7332_ = crate::leanh::lean_ctor_get(v_target_7331_, 0);
                v_lhs_7333_ = crate::leanh::lean_ctor_get(v_target_7331_, 1);
                v_rhs_7334_ = crate::leanh::lean_ctor_get(v_target_7331_, 2);
                v_pow_7335_ = crate::leanh::lean_ctor_get(v_target_7331_, 3);
                v___x_7336_ = lean_nat_dec_lt(v_pow_7335_, v_n_7332_);
                if v___x_7336_ == 0 {
                    crate::leanh::lean_inc_ref(v_lhs_7333_);
                    v___x_7337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7337_, 0, v_aig_7330_);
                    crate::leanh::lean_ctor_set(v___x_7337_, 1, v_lhs_7333_);
                    return v___x_7337_;
                } else {
                    v___x_7338_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_7339_ = lean_nat_pow(v___x_7338_, v_pow_7335_);
                    crate::leanh::lean_inc_ref(v_lhs_7333_);
                    v___x_7340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7340_, 0, v_lhs_7333_);
                    crate::leanh::lean_ctor_set(v___x_7340_, 1, v___x_7339_);
                    v_res_7341_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67(v_w_7329_, v_aig_7330_, v___x_7340_);
                    crate::leanh::lean_dec_ref_known(v___x_7340_, 2);
                    v_aig_7342_ = crate::leanh::lean_ctor_get(v_res_7341_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7342_);
                    v_vec_7343_ = crate::leanh::lean_ctor_get(v_res_7341_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7343_);
                    crate::leanh::lean_dec_ref(v_res_7341_);
                    v_ref_7348_ = lean_array_fget_borrowed(v_rhs_7334_, v_pow_7335_);
                    v___x_7349_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7350_ = lean_nat_shiftr(v_ref_7348_, v___x_7349_);
                    v___x_7351_ = lean_nat_land(v___x_7349_, v_ref_7348_);
                    v___x_7352_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7353_ = lean_nat_dec_eq(v___x_7351_, v___x_7352_);
                    crate::leanh::lean_dec(v___x_7351_);
                    if v___x_7353_ == 0 {
                        v___x_7354_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7354_, 0, v___x_7350_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7354_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7336_,
                        );
                        v___y_7345_ = v___x_7354_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7355_ = 0;
                        v___x_7356_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7356_, 0, v___x_7350_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7356_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7355_,
                        );
                        v___y_7345_ = v___x_7356_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_7333_);
                v___x_7346_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7346_, 0, v___y_7345_);
                crate::leanh::lean_ctor_set(v___x_7346_, 1, v_vec_7343_);
                crate::leanh::lean_ctor_set(v___x_7346_, 2, v_lhs_7333_);
                v___x_7347_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_7329_, v_aig_7342_, v___x_7346_);
                return v___x_7347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50___boxed(
    mut v_w_7357_: *mut crate::leanh::LeanObject,
    mut v_aig_7358_: *mut crate::leanh::LeanObject,
    mut v_target_7359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7360_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50(v_w_7357_, v_aig_7358_, v_target_7359_);
    crate::leanh::lean_dec_ref(v_target_7359_);
    crate::leanh::lean_dec(v_w_7357_);
    return v_res_7360_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__51(
    mut v_w_7361_: *mut crate::leanh::LeanObject,
    mut v_n_7362_: *mut crate::leanh::LeanObject,
    mut v_aig_7363_: *mut crate::leanh::LeanObject,
    mut v_distance_7364_: *mut crate::leanh::LeanObject,
    mut v_curr_7365_: *mut crate::leanh::LeanObject,
    mut v_acc_7366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: u8 = 0;
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7367_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7368_ = lean_nat_sub(v_n_7362_, v___x_7367_);
                v___x_7369_ = lean_nat_dec_lt(v_curr_7365_, v___x_7368_);
                crate::leanh::lean_dec(v___x_7368_);
                if v___x_7369_ == 0 {
                    crate::leanh::lean_dec(v_curr_7365_);
                    crate::leanh::lean_dec_ref(v_distance_7364_);
                    crate::leanh::lean_dec(v_n_7362_);
                    v___x_7370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7370_, 0, v_aig_7363_);
                    crate::leanh::lean_ctor_set(v___x_7370_, 1, v_acc_7366_);
                    return v___x_7370_;
                } else {
                    v___x_7371_ = lean_nat_add(v_curr_7365_, v___x_7367_);
                    crate::leanh::lean_dec(v_curr_7365_);
                    crate::leanh::lean_inc(v___x_7371_);
                    crate::leanh::lean_inc_ref(v_distance_7364_);
                    crate::leanh::lean_inc(v_n_7362_);
                    v___x_7372_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7372_, 0, v_n_7362_);
                    crate::leanh::lean_ctor_set(v___x_7372_, 1, v_acc_7366_);
                    crate::leanh::lean_ctor_set(v___x_7372_, 2, v_distance_7364_);
                    crate::leanh::lean_ctor_set(v___x_7372_, 3, v___x_7371_);
                    v_res_7373_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50(v_w_7361_, v_aig_7363_, v___x_7372_);
                    crate::leanh::lean_dec_ref_known(v___x_7372_, 4);
                    v_aig_7374_ = crate::leanh::lean_ctor_get(v_res_7373_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7374_);
                    v_vec_7375_ = crate::leanh::lean_ctor_get(v_res_7373_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7375_);
                    crate::leanh::lean_dec_ref(v_res_7373_);
                    v_aig_7363_ = v_aig_7374_;
                    v_curr_7365_ = v___x_7371_;
                    v_acc_7366_ = v_vec_7375_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__51___boxed(
    mut v_w_7377_: *mut crate::leanh::LeanObject,
    mut v_n_7378_: *mut crate::leanh::LeanObject,
    mut v_aig_7379_: *mut crate::leanh::LeanObject,
    mut v_distance_7380_: *mut crate::leanh::LeanObject,
    mut v_curr_7381_: *mut crate::leanh::LeanObject,
    mut v_acc_7382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7383_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__51(v_w_7377_, v_n_7378_, v_aig_7379_, v_distance_7380_, v_curr_7381_, v_acc_7382_);
    crate::leanh::lean_dec(v_w_7377_);
    return v_res_7383_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24(
    mut v_w_7384_: *mut crate::leanh::LeanObject,
    mut v_aig_7385_: *mut crate::leanh::LeanObject,
    mut v_target_7386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: u8 = 0;
    v_n_7387_ = crate::leanh::lean_ctor_get(v_target_7386_, 0);
    crate::leanh::lean_inc(v_n_7387_);
    v_target_7388_ = crate::leanh::lean_ctor_get(v_target_7386_, 1);
    crate::leanh::lean_inc_ref(v_target_7388_);
    v_distance_7389_ = crate::leanh::lean_ctor_get(v_target_7386_, 2);
    crate::leanh::lean_inc_ref(v_distance_7389_);
    crate::leanh::lean_dec_ref(v_target_7386_);
    v___x_7390_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7391_ = lean_nat_dec_eq(v_n_7387_, v___x_7390_);
    if v___x_7391_ == 0 {
        let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_7389_);
        crate::leanh::lean_inc(v_n_7387_);
        v___x_7392_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7392_, 0, v_n_7387_);
        crate::leanh::lean_ctor_set(v___x_7392_, 1, v_target_7388_);
        crate::leanh::lean_ctor_set(v___x_7392_, 2, v_distance_7389_);
        crate::leanh::lean_ctor_set(v___x_7392_, 3, v___x_7390_);
        v_res_7393_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50(v_w_7384_, v_aig_7385_, v___x_7392_);
        crate::leanh::lean_dec_ref_known(v___x_7392_, 4);
        v_aig_7394_ = crate::leanh::lean_ctor_get(v_res_7393_, 0);
        crate::leanh::lean_inc_ref(v_aig_7394_);
        v_vec_7395_ = crate::leanh::lean_ctor_get(v_res_7393_, 1);
        crate::leanh::lean_inc_ref(v_vec_7395_);
        crate::leanh::lean_dec_ref(v_res_7393_);
        v___x_7396_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__51(v_w_7384_, v_n_7387_, v_aig_7394_, v_distance_7389_, v___x_7390_, v_vec_7395_);
        return v___x_7396_;
    } else {
        let mut v___x_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_7389_);
        crate::leanh::lean_dec(v_n_7387_);
        v___x_7397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7397_, 0, v_aig_7385_);
        crate::leanh::lean_ctor_set(v___x_7397_, 1, v_target_7388_);
        return v___x_7397_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24___boxed(
    mut v_w_7398_: *mut crate::leanh::LeanObject,
    mut v_aig_7399_: *mut crate::leanh::LeanObject,
    mut v_target_7400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7401_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24(v_w_7398_, v_aig_7399_, v_target_7400_);
    crate::leanh::lean_dec(v_w_7398_);
    return v_res_7401_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___redArg(
    mut v_w_7402_: *mut crate::leanh::LeanObject,
    mut v_input_7403_: *mut crate::leanh::LeanObject,
    mut v_distance_7404_: *mut crate::leanh::LeanObject,
    mut v_curr_7405_: *mut crate::leanh::LeanObject,
    mut v_s_7406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7409_: u8 = 0;
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7420_: u8 = 0;
    let mut v___x_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: u8 = 0;
    let mut v___x_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: u8 = 0;
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: u8 = 0;
    let mut v___x_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: u8 = 0;
    let mut v___x_7447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7429_ = lean_nat_dec_lt(v_curr_7405_, v_w_7402_);
                if v___x_7429_ == 0 {
                    crate::leanh::lean_dec(v_curr_7405_);
                    return v_s_7406_;
                } else {
                    v___x_7430_ = lean_nat_mod(v_distance_7404_, v_w_7402_);
                    v___x_7431_ = lean_nat_sub(v_w_7402_, v___x_7430_);
                    v___x_7432_ = lean_nat_dec_lt(v_curr_7405_, v___x_7431_);
                    if v___x_7432_ == 0 {
                        crate::leanh::lean_dec(v___x_7430_);
                        v___x_7433_ = lean_nat_sub(v_curr_7405_, v___x_7431_);
                        crate::leanh::lean_dec(v___x_7431_);
                        v_ref_7434_ = lean_array_fget_borrowed(v_input_7403_, v___x_7433_);
                        crate::leanh::lean_dec(v___x_7433_);
                        v___x_7435_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7436_ = lean_nat_shiftr(v_ref_7434_, v___x_7435_);
                        v___x_7437_ = lean_nat_land(v___x_7435_, v_ref_7434_);
                        v___x_7438_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7439_ = lean_nat_dec_eq(v___x_7437_, v___x_7438_);
                        crate::leanh::lean_dec(v___x_7437_);
                        if v___x_7439_ == 0 {
                            v_gate_7408_ = v___x_7436_;
                            v_invert_7409_ = v___x_7429_;
                            state = 1;
                            continue;
                        } else {
                            v_gate_7408_ = v___x_7436_;
                            v_invert_7409_ = v___x_7432_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7431_);
                        v___x_7440_ = lean_nat_add(v___x_7430_, v_curr_7405_);
                        crate::leanh::lean_dec(v___x_7430_);
                        v_ref_7441_ = lean_array_fget_borrowed(v_input_7403_, v___x_7440_);
                        crate::leanh::lean_dec(v___x_7440_);
                        v___x_7442_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7443_ = lean_nat_shiftr(v_ref_7441_, v___x_7442_);
                        v___x_7444_ = lean_nat_land(v___x_7442_, v_ref_7441_);
                        v___x_7445_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7446_ = lean_nat_dec_eq(v___x_7444_, v___x_7445_);
                        crate::leanh::lean_dec(v___x_7444_);
                        if v___x_7446_ == 0 {
                            v_gate_7419_ = v___x_7443_;
                            v_invert_7420_ = v___x_7432_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7447_ = 0;
                            v_gate_7419_ = v___x_7443_;
                            v_invert_7420_ = v___x_7447_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7410_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7411_ = lean_nat_add(v_curr_7405_, v___x_7410_);
                crate::leanh::lean_dec(v_curr_7405_);
                v___x_7412_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7413_ = lean_nat_mul(v_gate_7408_, v___x_7412_);
                crate::leanh::lean_dec(v_gate_7408_);
                v___x_7414_ = l_Bool_toNat(v_invert_7409_);
                v___x_7415_ = lean_nat_lor(v___x_7413_, v___x_7414_);
                crate::leanh::lean_dec(v___x_7414_);
                crate::leanh::lean_dec(v___x_7413_);
                v_s_7416_ = lean_array_push(v_s_7406_, v___x_7415_);
                v_curr_7405_ = v___x_7411_;
                v_s_7406_ = v_s_7416_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7421_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7422_ = lean_nat_add(v_curr_7405_, v___x_7421_);
                crate::leanh::lean_dec(v_curr_7405_);
                v___x_7423_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7424_ = lean_nat_mul(v_gate_7419_, v___x_7423_);
                crate::leanh::lean_dec(v_gate_7419_);
                v___x_7425_ = l_Bool_toNat(v_invert_7420_);
                v___x_7426_ = lean_nat_lor(v___x_7424_, v___x_7425_);
                crate::leanh::lean_dec(v___x_7425_);
                crate::leanh::lean_dec(v___x_7424_);
                v_s_7427_ = lean_array_push(v_s_7406_, v___x_7426_);
                v_curr_7405_ = v___x_7422_;
                v_s_7406_ = v_s_7427_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___redArg___boxed(
    mut v_w_7448_: *mut crate::leanh::LeanObject,
    mut v_input_7449_: *mut crate::leanh::LeanObject,
    mut v_distance_7450_: *mut crate::leanh::LeanObject,
    mut v_curr_7451_: *mut crate::leanh::LeanObject,
    mut v_s_7452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___redArg(v_w_7448_, v_input_7449_, v_distance_7450_, v_curr_7451_, v_s_7452_);
    crate::leanh::lean_dec(v_distance_7450_);
    crate::leanh::lean_dec_ref(v_input_7449_);
    crate::leanh::lean_dec(v_w_7448_);
    return v_res_7453_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17(
    mut v_w_7454_: *mut crate::leanh::LeanObject,
    mut v_aig_7455_: *mut crate::leanh::LeanObject,
    mut v_target_7456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7461_: u8 = 0;
    let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vec_7457_ = crate::leanh::lean_ctor_get(v_target_7456_, 0);
                v_distance_7458_ = crate::leanh::lean_ctor_get(v_target_7456_, 1);
                v_isSharedCheck_7468_ = (!crate::leanh::lean_is_exclusive(v_target_7456_)) as u8;
                if v_isSharedCheck_7468_ == 0 {
                    v___x_7460_ = v_target_7456_;
                    v_isShared_7461_ = v_isSharedCheck_7468_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_distance_7458_);
                    crate::leanh::lean_inc(v_vec_7457_);
                    crate::leanh::lean_dec(v_target_7456_);
                    v___x_7460_ = crate::leanh::lean_box(0);
                    v_isShared_7461_ = v_isSharedCheck_7468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7462_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7463_ = lean_mk_empty_array_with_capacity(v_w_7454_);
                v___x_7464_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___redArg(v_w_7454_, v_vec_7457_, v_distance_7458_, v___x_7462_, v___x_7463_);
                crate::leanh::lean_dec(v_distance_7458_);
                crate::leanh::lean_dec_ref(v_vec_7457_);
                if v_isShared_7461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7460_, 1, v___x_7464_);
                    crate::leanh::lean_ctor_set(v___x_7460_, 0, v_aig_7455_);
                    v___x_7466_ = v___x_7460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7467_, 0, v_aig_7455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7467_, 1, v___x_7464_);
                    v___x_7466_ = v_reuseFailAlloc_7467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17___boxed(
    mut v_w_7469_: *mut crate::leanh::LeanObject,
    mut v_aig_7470_: *mut crate::leanh::LeanObject,
    mut v_target_7471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7472_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17(v_w_7469_, v_aig_7470_, v_target_7471_);
    crate::leanh::lean_dec(v_w_7469_);
    return v_res_7472_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__42(
    mut v_w_7473_: *mut crate::leanh::LeanObject,
    mut v_aig_7474_: *mut crate::leanh::LeanObject,
    mut v_x_7475_: *mut crate::leanh::LeanObject,
    mut v_curr_7476_: *mut crate::leanh::LeanObject,
    mut v_acc_7477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7478_: u8 = 0;
    let mut v___x_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: u8 = 0;
    let mut v___x_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: u8 = 0;
    let mut v___x_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7478_ = lean_nat_dec_lt(v_curr_7476_, v_w_7473_);
                if v___x_7478_ == 0 {
                    crate::leanh::lean_dec(v_curr_7476_);
                    v___x_7479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7479_, 0, v_aig_7474_);
                    crate::leanh::lean_ctor_set(v___x_7479_, 1, v_acc_7477_);
                    return v___x_7479_;
                } else {
                    v___x_7480_ = l_BitVec_ofNat(v_w_7473_, v_w_7473_);
                    v___x_7481_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7482_ = l_BitVec_ofNat(v_w_7473_, v___x_7481_);
                    v___x_7483_ = l_BitVec_sub(v_w_7473_, v___x_7480_, v___x_7482_);
                    crate::leanh::lean_dec(v___x_7482_);
                    crate::leanh::lean_dec(v___x_7480_);
                    v___x_7484_ = l_BitVec_ofNat(v_w_7473_, v_curr_7476_);
                    v___x_7485_ = l_BitVec_sub(v_w_7473_, v___x_7483_, v___x_7484_);
                    crate::leanh::lean_dec(v___x_7484_);
                    crate::leanh::lean_dec(v___x_7483_);
                    v_lhs_7486_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_7473_, v_aig_7474_, v___x_7485_);
                    crate::leanh::lean_dec(v___x_7485_);
                    v_ref_7495_ = lean_array_fget_borrowed(v_x_7475_, v_curr_7476_);
                    v___x_7496_ = lean_nat_shiftr(v_ref_7495_, v___x_7481_);
                    v___x_7497_ = lean_nat_land(v___x_7481_, v_ref_7495_);
                    v___x_7498_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7499_ = lean_nat_dec_eq(v___x_7497_, v___x_7498_);
                    crate::leanh::lean_dec(v___x_7497_);
                    if v___x_7499_ == 0 {
                        v___x_7500_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7500_, 0, v___x_7496_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7500_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7478_,
                        );
                        v___y_7488_ = v___x_7500_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7501_ = 0;
                        v___x_7502_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7502_, 0, v___x_7496_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7502_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7501_,
                        );
                        v___y_7488_ = v___x_7502_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7489_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7489_, 0, v___y_7488_);
                crate::leanh::lean_ctor_set(v___x_7489_, 1, v_lhs_7486_);
                crate::leanh::lean_ctor_set(v___x_7489_, 2, v_acc_7477_);
                v_res_7490_ = l_Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29(v_w_7473_, v_aig_7474_, v___x_7489_);
                v_aig_7491_ = crate::leanh::lean_ctor_get(v_res_7490_, 0);
                crate::leanh::lean_inc_ref(v_aig_7491_);
                v_vec_7492_ = crate::leanh::lean_ctor_get(v_res_7490_, 1);
                crate::leanh::lean_inc_ref(v_vec_7492_);
                crate::leanh::lean_dec_ref(v_res_7490_);
                v___x_7493_ = lean_nat_add(v_curr_7476_, v___x_7481_);
                crate::leanh::lean_dec(v_curr_7476_);
                v_aig_7474_ = v_aig_7491_;
                v_curr_7476_ = v___x_7493_;
                v_acc_7477_ = v_vec_7492_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__42___boxed(
    mut v_w_7503_: *mut crate::leanh::LeanObject,
    mut v_aig_7504_: *mut crate::leanh::LeanObject,
    mut v_x_7505_: *mut crate::leanh::LeanObject,
    mut v_curr_7506_: *mut crate::leanh::LeanObject,
    mut v_acc_7507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7508_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__42(v_w_7503_, v_aig_7504_, v_x_7505_, v_curr_7506_, v_acc_7507_);
    crate::leanh::lean_dec_ref(v_x_7505_);
    crate::leanh::lean_dec(v_w_7503_);
    return v_res_7508_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20(
    mut v_w_7509_: *mut crate::leanh::LeanObject,
    mut v_aig_7510_: *mut crate::leanh::LeanObject,
    mut v_x_7511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wconst_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7512_ = l_BitVec_ofNat(v_w_7509_, v_w_7509_);
    v_wconst_7513_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_7509_, v_aig_7510_, v___x_7512_);
    crate::leanh::lean_dec(v___x_7512_);
    v___x_7514_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7515_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__42(v_w_7509_, v_aig_7510_, v_x_7511_, v___x_7514_, v_wconst_7513_);
    return v___x_7515_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20___boxed(
    mut v_w_7516_: *mut crate::leanh::LeanObject,
    mut v_aig_7517_: *mut crate::leanh::LeanObject,
    mut v_x_7518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7519_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20(v_w_7516_, v_aig_7517_, v_x_7518_);
    crate::leanh::lean_dec_ref(v_x_7518_);
    crate::leanh::lean_dec(v_w_7516_);
    return v_res_7519_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___redArg(
    mut v_len_7520_: *mut crate::leanh::LeanObject,
    mut v_aig_7521_: *mut crate::leanh::LeanObject,
    mut v_idx_7522_: *mut crate::leanh::LeanObject,
    mut v_s_7523_: *mut crate::leanh::LeanObject,
    mut v_lhs_7524_: *mut crate::leanh::LeanObject,
    mut v_rhs_7525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_7534_: u8 = 0;
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: u8 = 0;
    let mut v___y_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: u8 = 0;
    let mut v___x_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: u8 = 0;
    let mut v___x_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: u8 = 0;
    let mut v___x_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: u8 = 0;
    let mut v___x_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7543_ = lean_nat_dec_lt(v_idx_7522_, v_len_7520_);
                if v___x_7543_ == 0 {
                    crate::leanh::lean_dec(v_idx_7522_);
                    v___x_7555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7555_, 0, v_aig_7521_);
                    crate::leanh::lean_ctor_set(v___x_7555_, 1, v_s_7523_);
                    return v___x_7555_;
                } else {
                    v_ref_7556_ = lean_array_fget_borrowed(v_lhs_7524_, v_idx_7522_);
                    v___x_7557_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7558_ = lean_nat_shiftr(v_ref_7556_, v___x_7557_);
                    v___x_7559_ = lean_nat_land(v___x_7557_, v_ref_7556_);
                    v___x_7560_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7561_ = lean_nat_dec_eq(v___x_7559_, v___x_7560_);
                    crate::leanh::lean_dec(v___x_7559_);
                    if v___x_7561_ == 0 {
                        v___x_7562_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7562_, 0, v___x_7558_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7562_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7543_,
                        );
                        v___y_7545_ = v___x_7562_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7563_ = 0;
                        v___x_7564_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7564_, 0, v___x_7558_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7564_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7563_,
                        );
                        v___y_7545_ = v___x_7564_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7529_, 0, v___y_7527_);
                crate::leanh::lean_ctor_set(v___x_7529_, 1, v___y_7528_);
                v_res_7530_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(v_aig_7521_, v___x_7529_);
                v_ref_7531_ = crate::leanh::lean_ctor_get(v_res_7530_, 1);
                crate::leanh::lean_inc_ref(v_ref_7531_);
                v_aig_7532_ = crate::leanh::lean_ctor_get(v_res_7530_, 0);
                crate::leanh::lean_inc_ref(v_aig_7532_);
                crate::leanh::lean_dec_ref(v_res_7530_);
                v_gate_7533_ = crate::leanh::lean_ctor_get(v_ref_7531_, 0);
                crate::leanh::lean_inc(v_gate_7533_);
                v_invert_7534_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_7531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_7531_);
                v___x_7535_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7536_ = lean_nat_add(v_idx_7522_, v___x_7535_);
                crate::leanh::lean_dec(v_idx_7522_);
                v___x_7537_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7538_ = lean_nat_mul(v_gate_7533_, v___x_7537_);
                crate::leanh::lean_dec(v_gate_7533_);
                v___x_7539_ = l_Bool_toNat(v_invert_7534_);
                v___x_7540_ = lean_nat_lor(v___x_7538_, v___x_7539_);
                crate::leanh::lean_dec(v___x_7539_);
                crate::leanh::lean_dec(v___x_7538_);
                v_s_7541_ = lean_array_push(v_s_7523_, v___x_7540_);
                v_aig_7521_ = v_aig_7532_;
                v_idx_7522_ = v___x_7536_;
                v_s_7523_ = v_s_7541_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_7546_ = lean_array_fget_borrowed(v_rhs_7525_, v_idx_7522_);
                v___x_7547_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7548_ = lean_nat_shiftr(v_ref_7546_, v___x_7547_);
                v___x_7549_ = lean_nat_land(v___x_7547_, v_ref_7546_);
                v___x_7550_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7551_ = lean_nat_dec_eq(v___x_7549_, v___x_7550_);
                crate::leanh::lean_dec(v___x_7549_);
                if v___x_7551_ == 0 {
                    v___x_7552_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7552_, 0, v___x_7548_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7552_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7543_,
                    );
                    v___y_7527_ = v___y_7545_;
                    v___y_7528_ = v___x_7552_;
                    state = 1;
                    continue;
                } else {
                    v___x_7553_ = 0;
                    v___x_7554_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7554_, 0, v___x_7548_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7554_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_7553_,
                    );
                    v___y_7527_ = v___y_7545_;
                    v___y_7528_ = v___x_7554_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___redArg___boxed(
    mut v_len_7565_: *mut crate::leanh::LeanObject,
    mut v_aig_7566_: *mut crate::leanh::LeanObject,
    mut v_idx_7567_: *mut crate::leanh::LeanObject,
    mut v_s_7568_: *mut crate::leanh::LeanObject,
    mut v_lhs_7569_: *mut crate::leanh::LeanObject,
    mut v_rhs_7570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7571_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___redArg(v_len_7565_, v_aig_7566_, v_idx_7567_, v_s_7568_, v_lhs_7569_, v_rhs_7570_);
    crate::leanh::lean_dec_ref(v_rhs_7570_);
    crate::leanh::lean_dec_ref(v_lhs_7569_);
    crate::leanh::lean_dec(v_len_7565_);
    return v_res_7571_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___redArg(
    mut v_len_7572_: *mut crate::leanh::LeanObject,
    mut v_aig_7573_: *mut crate::leanh::LeanObject,
    mut v_input_7574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_7575_ = crate::leanh::lean_ctor_get(v_input_7574_, 0);
    v_rhs_7576_ = crate::leanh::lean_ctor_get(v_input_7574_, 1);
    v___x_7577_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7578_ = lean_mk_empty_array_with_capacity(v_len_7572_);
    v___x_7579_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___redArg(v_len_7572_, v_aig_7573_, v___x_7577_, v___x_7578_, v_lhs_7575_, v_rhs_7576_);
    return v___x_7579_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___redArg___boxed(
    mut v_len_7580_: *mut crate::leanh::LeanObject,
    mut v_aig_7581_: *mut crate::leanh::LeanObject,
    mut v_input_7582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7583_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___redArg(
            v_len_7580_,
            v_aig_7581_,
            v_input_7582_,
        );
    crate::leanh::lean_dec_ref(v_input_7582_);
    crate::leanh::lean_dec(v_len_7580_);
    return v_res_7583_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_go(
    mut v_w_7584_: *mut crate::leanh::LeanObject,
    mut v_aig_7585_: *mut crate::leanh::LeanObject,
    mut v_expr_7586_: *mut crate::leanh::LeanObject,
    mut v_cache_7587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7603_: u8 = 0;
    let mut v_aig_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7611_: u8 = 0;
    let mut v_lhs_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_7613_: u8 = 0;
    let mut v_rhs_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7625_: u8 = 0;
    let mut v_aig_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7630_: u8 = 0;
    let mut v___x_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7638_: u8 = 0;
    let mut v_isSharedCheck_7639_: u8 = 0;
    let mut v_unused_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7644_: u8 = 0;
    let mut v_aig_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7649_: u8 = 0;
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7657_: u8 = 0;
    let mut v_isSharedCheck_7658_: u8 = 0;
    let mut v_unused_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7663_: u8 = 0;
    let mut v_aig_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7668_: u8 = 0;
    let mut v___x_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_isSharedCheck_7677_: u8 = 0;
    let mut v_unused_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7682_: u8 = 0;
    let mut v_aig_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7687_: u8 = 0;
    let mut v___x_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7695_: u8 = 0;
    let mut v_isSharedCheck_7696_: u8 = 0;
    let mut v_unused_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7701_: u8 = 0;
    let mut v_aig_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7706_: u8 = 0;
    let mut v___x_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7714_: u8 = 0;
    let mut v_isSharedCheck_7715_: u8 = 0;
    let mut v_unused_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7720_: u8 = 0;
    let mut v_aig_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7725_: u8 = 0;
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7733_: u8 = 0;
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v_unused_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7739_: u8 = 0;
    let mut v_aig_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7744_: u8 = 0;
    let mut v___x_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7752_: u8 = 0;
    let mut v_isSharedCheck_7753_: u8 = 0;
    let mut v_unused_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_operand_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7762_: u8 = 0;
    let mut v_aig_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7769_: u8 = 0;
    let mut v_unused_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7774_: u8 = 0;
    let mut v_aig_7775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7779_: u8 = 0;
    let mut v_n_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7788_: u8 = 0;
    let mut v_isSharedCheck_7789_: u8 = 0;
    let mut v_unused_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7794_: u8 = 0;
    let mut v_aig_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7799_: u8 = 0;
    let mut v_n_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7808_: u8 = 0;
    let mut v_isSharedCheck_7809_: u8 = 0;
    let mut v_unused_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7814_: u8 = 0;
    let mut v_aig_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7819_: u8 = 0;
    let mut v_n_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7828_: u8 = 0;
    let mut v_isSharedCheck_7829_: u8 = 0;
    let mut v_unused_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7834_: u8 = 0;
    let mut v_aig_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7841_: u8 = 0;
    let mut v_unused_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7846_: u8 = 0;
    let mut v_aig_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7853_: u8 = 0;
    let mut v_unused_7854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7858_: u8 = 0;
    let mut v_aig_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7865_: u8 = 0;
    let mut v_unused_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7881_: u8 = 0;
    let mut v_aig_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7889_: u8 = 0;
    let mut v_w_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7898_: u8 = 0;
    let mut v_aig_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7906_: u8 = 0;
    let mut v_n_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7920_: u8 = 0;
    let mut v_aig_7921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7928_: u8 = 0;
    let mut v_n_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7942_: u8 = 0;
    let mut v_aig_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7950_: u8 = 0;
    let mut v_n_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7964_: u8 = 0;
    let mut v_aig_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_expr_7586_) {
                0 => {
                    v_idx_7588_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc(v_idx_7588_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 2);
                    v_res_7589_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(
                        v_w_7584_,
                        v_aig_7585_,
                        v_idx_7588_,
                    );
                    v___x_7590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7590_, 0, v_res_7589_);
                    crate::leanh::lean_ctor_set(v___x_7590_, 1, v_cache_7587_);
                    return v___x_7590_;
                }
                1 => {
                    v_val_7591_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc(v_val_7591_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 2);
                    v_res_7592_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3(v_w_7584_, v_aig_7585_, v_val_7591_);
                    crate::leanh::lean_dec(v_val_7591_);
                    crate::leanh::lean_dec(v_w_7584_);
                    v___x_7593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7593_, 0, v_aig_7585_);
                    crate::leanh::lean_ctor_set(v___x_7593_, 1, v_res_7592_);
                    v___x_7594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7594_, 0, v___x_7593_);
                    crate::leanh::lean_ctor_set(v___x_7594_, 1, v_cache_7587_);
                    return v___x_7594_;
                }
                2 => {
                    v_w_7595_ = crate::leanh::lean_ctor_get(v_expr_7586_, 0);
                    crate::leanh::lean_inc_n(v_w_7595_, 2);
                    v_start_7596_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc(v_start_7596_);
                    v_expr_7597_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_expr_7597_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 4);
                    v___x_7598_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7595_,
                        v_aig_7585_,
                        v_expr_7597_,
                        v_cache_7587_,
                    );
                    v_result_7599_ = crate::leanh::lean_ctor_get(v___x_7598_, 0);
                    v_cache_7600_ = crate::leanh::lean_ctor_get(v___x_7598_, 1);
                    v_isSharedCheck_7611_ = (!crate::leanh::lean_is_exclusive(v___x_7598_)) as u8;
                    if v_isSharedCheck_7611_ == 0 {
                        v___x_7602_ = v___x_7598_;
                        v_isShared_7603_ = v_isSharedCheck_7611_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7600_);
                        crate::leanh::lean_inc(v_result_7599_);
                        crate::leanh::lean_dec(v___x_7598_);
                        v___x_7602_ = crate::leanh::lean_box(0);
                        v_isShared_7603_ = v_isSharedCheck_7611_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_lhs_7612_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc_ref(v_lhs_7612_);
                    v_op_7613_ = crate::leanh::lean_ctor_get_uint8(
                        v_expr_7586_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v_rhs_7614_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc_ref(v_rhs_7614_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 3);
                    crate::leanh::lean_inc_n(v_w_7584_, 2);
                    v___x_7615_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7585_,
                        v_lhs_7612_,
                        v_cache_7587_,
                    );
                    v_result_7616_ = crate::leanh::lean_ctor_get(v___x_7615_, 0);
                    crate::leanh::lean_inc_ref(v_result_7616_);
                    v_cache_7617_ = crate::leanh::lean_ctor_get(v___x_7615_, 1);
                    crate::leanh::lean_inc_ref(v_cache_7617_);
                    crate::leanh::lean_dec_ref(v___x_7615_);
                    v_aig_7618_ = crate::leanh::lean_ctor_get(v_result_7616_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7618_);
                    v_vec_7619_ = crate::leanh::lean_ctor_get(v_result_7616_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7619_);
                    crate::leanh::lean_dec_ref(v_result_7616_);
                    v___x_7620_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7618_,
                        v_rhs_7614_,
                        v_cache_7617_,
                    );
                    v_result_7621_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                    crate::leanh::lean_inc_ref(v_result_7621_);
                    match v_op_7613_ {
                        0 => {
                            v_cache_7622_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7639_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7639_ == 0 {
                                v_unused_7640_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7640_);
                                v___x_7624_ = v___x_7620_;
                                v_isShared_7625_ = v_isSharedCheck_7639_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7622_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7624_ = crate::leanh::lean_box(0);
                                v_isShared_7625_ = v_isSharedCheck_7639_;
                                state = 3;
                                continue;
                            }
                        }
                        1 => {
                            v_cache_7641_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7658_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7658_ == 0 {
                                v_unused_7659_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7659_);
                                v___x_7643_ = v___x_7620_;
                                v_isShared_7644_ = v_isSharedCheck_7658_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7641_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7643_ = crate::leanh::lean_box(0);
                                v_isShared_7644_ = v_isSharedCheck_7658_;
                                state = 7;
                                continue;
                            }
                        }
                        2 => {
                            v_cache_7660_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7677_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7677_ == 0 {
                                v_unused_7678_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7678_);
                                v___x_7662_ = v___x_7620_;
                                v_isShared_7663_ = v_isSharedCheck_7677_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7660_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7662_ = crate::leanh::lean_box(0);
                                v_isShared_7663_ = v_isSharedCheck_7677_;
                                state = 11;
                                continue;
                            }
                        }
                        3 => {
                            v_cache_7679_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7696_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7696_ == 0 {
                                v_unused_7697_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7697_);
                                v___x_7681_ = v___x_7620_;
                                v_isShared_7682_ = v_isSharedCheck_7696_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7679_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7681_ = crate::leanh::lean_box(0);
                                v_isShared_7682_ = v_isSharedCheck_7696_;
                                state = 15;
                                continue;
                            }
                        }
                        4 => {
                            v_cache_7698_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7715_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7715_ == 0 {
                                v_unused_7716_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7716_);
                                v___x_7700_ = v___x_7620_;
                                v_isShared_7701_ = v_isSharedCheck_7715_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7698_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7700_ = crate::leanh::lean_box(0);
                                v_isShared_7701_ = v_isSharedCheck_7715_;
                                state = 19;
                                continue;
                            }
                        }
                        5 => {
                            v_cache_7717_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7734_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7734_ == 0 {
                                v_unused_7735_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7735_);
                                v___x_7719_ = v___x_7620_;
                                v_isShared_7720_ = v_isSharedCheck_7734_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7717_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7719_ = crate::leanh::lean_box(0);
                                v_isShared_7720_ = v_isSharedCheck_7734_;
                                state = 23;
                                continue;
                            }
                        }
                        _ => {
                            v_cache_7736_ = crate::leanh::lean_ctor_get(v___x_7620_, 1);
                            v_isSharedCheck_7753_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7620_)) as u8;
                            if v_isSharedCheck_7753_ == 0 {
                                v_unused_7754_ = crate::leanh::lean_ctor_get(v___x_7620_, 0);
                                crate::leanh::lean_dec(v_unused_7754_);
                                v___x_7738_ = v___x_7620_;
                                v_isShared_7739_ = v_isSharedCheck_7753_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7736_);
                                crate::leanh::lean_dec(v___x_7620_);
                                v___x_7738_ = crate::leanh::lean_box(0);
                                v_isShared_7739_ = v_isSharedCheck_7753_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                }
                4 => {
                    v_op_7755_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc(v_op_7755_);
                    v_operand_7756_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc_ref(v_operand_7756_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 3);
                    crate::leanh::lean_inc(v_w_7584_);
                    v___x_7757_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7585_,
                        v_operand_7756_,
                        v_cache_7587_,
                    );
                    v_result_7758_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                    crate::leanh::lean_inc_ref(v_result_7758_);
                    match crate::leanh::lean_obj_tag(v_op_7755_) {
                        0 => {
                            v_cache_7759_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7769_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7769_ == 0 {
                                v_unused_7770_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7770_);
                                v___x_7761_ = v___x_7757_;
                                v_isShared_7762_ = v_isSharedCheck_7769_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7759_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7761_ = crate::leanh::lean_box(0);
                                v_isShared_7762_ = v_isSharedCheck_7769_;
                                state = 31;
                                continue;
                            }
                        }
                        1 => {
                            v_cache_7771_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7789_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7789_ == 0 {
                                v_unused_7790_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7790_);
                                v___x_7773_ = v___x_7757_;
                                v_isShared_7774_ = v_isSharedCheck_7789_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7771_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7773_ = crate::leanh::lean_box(0);
                                v_isShared_7774_ = v_isSharedCheck_7789_;
                                state = 33;
                                continue;
                            }
                        }
                        2 => {
                            v_cache_7791_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7809_ == 0 {
                                v_unused_7810_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7810_);
                                v___x_7793_ = v___x_7757_;
                                v_isShared_7794_ = v_isSharedCheck_7809_;
                                state = 37;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7791_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7793_ = crate::leanh::lean_box(0);
                                v_isShared_7794_ = v_isSharedCheck_7809_;
                                state = 37;
                                continue;
                            }
                        }
                        3 => {
                            v_cache_7811_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7829_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7829_ == 0 {
                                v_unused_7830_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7830_);
                                v___x_7813_ = v___x_7757_;
                                v_isShared_7814_ = v_isSharedCheck_7829_;
                                state = 41;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7811_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7813_ = crate::leanh::lean_box(0);
                                v_isShared_7814_ = v_isSharedCheck_7829_;
                                state = 41;
                                continue;
                            }
                        }
                        4 => {
                            crate::leanh::lean_dec(v_w_7584_);
                            v_cache_7831_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7841_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7841_ == 0 {
                                v_unused_7842_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7842_);
                                v___x_7833_ = v___x_7757_;
                                v_isShared_7834_ = v_isSharedCheck_7841_;
                                state = 45;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7831_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7833_ = crate::leanh::lean_box(0);
                                v_isShared_7834_ = v_isSharedCheck_7841_;
                                state = 45;
                                continue;
                            }
                        }
                        5 => {
                            v_cache_7843_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7853_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7853_ == 0 {
                                v_unused_7854_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7854_);
                                v___x_7845_ = v___x_7757_;
                                v_isShared_7846_ = v_isSharedCheck_7853_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7843_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7845_ = crate::leanh::lean_box(0);
                                v_isShared_7846_ = v_isSharedCheck_7853_;
                                state = 47;
                                continue;
                            }
                        }
                        _ => {
                            v_cache_7855_ = crate::leanh::lean_ctor_get(v___x_7757_, 1);
                            v_isSharedCheck_7865_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                            if v_isSharedCheck_7865_ == 0 {
                                v_unused_7866_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                                crate::leanh::lean_dec(v_unused_7866_);
                                v___x_7857_ = v___x_7757_;
                                v_isShared_7858_ = v_isSharedCheck_7865_;
                                state = 49;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_cache_7855_);
                                crate::leanh::lean_dec(v___x_7757_);
                                v___x_7857_ = crate::leanh::lean_box(0);
                                v_isShared_7858_ = v_isSharedCheck_7865_;
                                state = 49;
                                continue;
                            }
                        }
                    }
                }
                5 => {
                    crate::leanh::lean_dec(v_w_7584_);
                    v_l_7867_ = crate::leanh::lean_ctor_get(v_expr_7586_, 0);
                    crate::leanh::lean_inc_n(v_l_7867_, 2);
                    v_r_7868_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc_n(v_r_7868_, 2);
                    v_lhs_7869_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_lhs_7869_);
                    v_rhs_7870_ = crate::leanh::lean_ctor_get(v_expr_7586_, 4);
                    crate::leanh::lean_inc_ref(v_rhs_7870_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 5);
                    v___x_7871_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_l_7867_,
                        v_aig_7585_,
                        v_lhs_7869_,
                        v_cache_7587_,
                    );
                    v_result_7872_ = crate::leanh::lean_ctor_get(v___x_7871_, 0);
                    crate::leanh::lean_inc_ref(v_result_7872_);
                    v_cache_7873_ = crate::leanh::lean_ctor_get(v___x_7871_, 1);
                    crate::leanh::lean_inc_ref(v_cache_7873_);
                    crate::leanh::lean_dec_ref(v___x_7871_);
                    v_aig_7874_ = crate::leanh::lean_ctor_get(v_result_7872_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7874_);
                    v_vec_7875_ = crate::leanh::lean_ctor_get(v_result_7872_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7875_);
                    crate::leanh::lean_dec_ref(v_result_7872_);
                    v___x_7876_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_r_7868_,
                        v_aig_7874_,
                        v_rhs_7870_,
                        v_cache_7873_,
                    );
                    v_result_7877_ = crate::leanh::lean_ctor_get(v___x_7876_, 0);
                    v_cache_7878_ = crate::leanh::lean_ctor_get(v___x_7876_, 1);
                    v_isSharedCheck_7889_ = (!crate::leanh::lean_is_exclusive(v___x_7876_)) as u8;
                    if v_isSharedCheck_7889_ == 0 {
                        v___x_7880_ = v___x_7876_;
                        v_isShared_7881_ = v_isSharedCheck_7889_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7878_);
                        crate::leanh::lean_inc(v_result_7877_);
                        crate::leanh::lean_dec(v___x_7876_);
                        v___x_7880_ = crate::leanh::lean_box(0);
                        v_isShared_7881_ = v_isSharedCheck_7889_;
                        state = 51;
                        continue;
                    }
                }
                6 => {
                    v_w_7890_ = crate::leanh::lean_ctor_get(v_expr_7586_, 0);
                    crate::leanh::lean_inc_n(v_w_7890_, 2);
                    v_n_7891_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc(v_n_7891_);
                    v_expr_7892_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_expr_7892_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 4);
                    v___x_7893_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7890_,
                        v_aig_7585_,
                        v_expr_7892_,
                        v_cache_7587_,
                    );
                    v_result_7894_ = crate::leanh::lean_ctor_get(v___x_7893_, 0);
                    v_cache_7895_ = crate::leanh::lean_ctor_get(v___x_7893_, 1);
                    v_isSharedCheck_7906_ = (!crate::leanh::lean_is_exclusive(v___x_7893_)) as u8;
                    if v_isSharedCheck_7906_ == 0 {
                        v___x_7897_ = v___x_7893_;
                        v_isShared_7898_ = v_isSharedCheck_7906_;
                        state = 53;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7895_);
                        crate::leanh::lean_inc(v_result_7894_);
                        crate::leanh::lean_dec(v___x_7893_);
                        v___x_7897_ = crate::leanh::lean_box(0);
                        v_isShared_7898_ = v_isSharedCheck_7906_;
                        state = 53;
                        continue;
                    }
                }
                7 => {
                    v_n_7907_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc_n(v_n_7907_, 2);
                    v_lhs_7908_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_7908_);
                    v_rhs_7909_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_7909_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 4);
                    crate::leanh::lean_inc(v_w_7584_);
                    v___x_7910_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7585_,
                        v_lhs_7908_,
                        v_cache_7587_,
                    );
                    v_result_7911_ = crate::leanh::lean_ctor_get(v___x_7910_, 0);
                    crate::leanh::lean_inc_ref(v_result_7911_);
                    v_cache_7912_ = crate::leanh::lean_ctor_get(v___x_7910_, 1);
                    crate::leanh::lean_inc_ref(v_cache_7912_);
                    crate::leanh::lean_dec_ref(v___x_7910_);
                    v_aig_7913_ = crate::leanh::lean_ctor_get(v_result_7911_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7913_);
                    v_vec_7914_ = crate::leanh::lean_ctor_get(v_result_7911_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7914_);
                    crate::leanh::lean_dec_ref(v_result_7911_);
                    v___x_7915_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_n_7907_,
                        v_aig_7913_,
                        v_rhs_7909_,
                        v_cache_7912_,
                    );
                    v_result_7916_ = crate::leanh::lean_ctor_get(v___x_7915_, 0);
                    v_cache_7917_ = crate::leanh::lean_ctor_get(v___x_7915_, 1);
                    v_isSharedCheck_7928_ = (!crate::leanh::lean_is_exclusive(v___x_7915_)) as u8;
                    if v_isSharedCheck_7928_ == 0 {
                        v___x_7919_ = v___x_7915_;
                        v_isShared_7920_ = v_isSharedCheck_7928_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7917_);
                        crate::leanh::lean_inc(v_result_7916_);
                        crate::leanh::lean_dec(v___x_7915_);
                        v___x_7919_ = crate::leanh::lean_box(0);
                        v_isShared_7920_ = v_isSharedCheck_7928_;
                        state = 55;
                        continue;
                    }
                }
                8 => {
                    v_n_7929_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc_n(v_n_7929_, 2);
                    v_lhs_7930_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_7930_);
                    v_rhs_7931_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_7931_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 4);
                    crate::leanh::lean_inc(v_w_7584_);
                    v___x_7932_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7585_,
                        v_lhs_7930_,
                        v_cache_7587_,
                    );
                    v_result_7933_ = crate::leanh::lean_ctor_get(v___x_7932_, 0);
                    crate::leanh::lean_inc_ref(v_result_7933_);
                    v_cache_7934_ = crate::leanh::lean_ctor_get(v___x_7932_, 1);
                    crate::leanh::lean_inc_ref(v_cache_7934_);
                    crate::leanh::lean_dec_ref(v___x_7932_);
                    v_aig_7935_ = crate::leanh::lean_ctor_get(v_result_7933_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7935_);
                    v_vec_7936_ = crate::leanh::lean_ctor_get(v_result_7933_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7936_);
                    crate::leanh::lean_dec_ref(v_result_7933_);
                    v___x_7937_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_n_7929_,
                        v_aig_7935_,
                        v_rhs_7931_,
                        v_cache_7934_,
                    );
                    v_result_7938_ = crate::leanh::lean_ctor_get(v___x_7937_, 0);
                    v_cache_7939_ = crate::leanh::lean_ctor_get(v___x_7937_, 1);
                    v_isSharedCheck_7950_ = (!crate::leanh::lean_is_exclusive(v___x_7937_)) as u8;
                    if v_isSharedCheck_7950_ == 0 {
                        v___x_7941_ = v___x_7937_;
                        v_isShared_7942_ = v_isSharedCheck_7950_;
                        state = 57;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7939_);
                        crate::leanh::lean_inc(v_result_7938_);
                        crate::leanh::lean_dec(v___x_7937_);
                        v___x_7941_ = crate::leanh::lean_box(0);
                        v_isShared_7942_ = v_isSharedCheck_7950_;
                        state = 57;
                        continue;
                    }
                }
                _ => {
                    v_n_7951_ = crate::leanh::lean_ctor_get(v_expr_7586_, 1);
                    crate::leanh::lean_inc_n(v_n_7951_, 2);
                    v_lhs_7952_ = crate::leanh::lean_ctor_get(v_expr_7586_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_7952_);
                    v_rhs_7953_ = crate::leanh::lean_ctor_get(v_expr_7586_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_7953_);
                    crate::leanh::lean_dec_ref_known(v_expr_7586_, 4);
                    crate::leanh::lean_inc(v_w_7584_);
                    v___x_7954_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_w_7584_,
                        v_aig_7585_,
                        v_lhs_7952_,
                        v_cache_7587_,
                    );
                    v_result_7955_ = crate::leanh::lean_ctor_get(v___x_7954_, 0);
                    crate::leanh::lean_inc_ref(v_result_7955_);
                    v_cache_7956_ = crate::leanh::lean_ctor_get(v___x_7954_, 1);
                    crate::leanh::lean_inc_ref(v_cache_7956_);
                    crate::leanh::lean_dec_ref(v___x_7954_);
                    v_aig_7957_ = crate::leanh::lean_ctor_get(v_result_7955_, 0);
                    crate::leanh::lean_inc_ref(v_aig_7957_);
                    v_vec_7958_ = crate::leanh::lean_ctor_get(v_result_7955_, 1);
                    crate::leanh::lean_inc_ref(v_vec_7958_);
                    crate::leanh::lean_dec_ref(v_result_7955_);
                    v___x_7959_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
                        v_n_7951_,
                        v_aig_7957_,
                        v_rhs_7953_,
                        v_cache_7956_,
                    );
                    v_result_7960_ = crate::leanh::lean_ctor_get(v___x_7959_, 0);
                    v_cache_7961_ = crate::leanh::lean_ctor_get(v___x_7959_, 1);
                    v_isSharedCheck_7972_ = (!crate::leanh::lean_is_exclusive(v___x_7959_)) as u8;
                    if v_isSharedCheck_7972_ == 0 {
                        v___x_7963_ = v___x_7959_;
                        v_isShared_7964_ = v_isSharedCheck_7972_;
                        state = 59;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7961_);
                        crate::leanh::lean_inc(v_result_7960_);
                        crate::leanh::lean_dec(v___x_7959_);
                        v___x_7963_ = crate::leanh::lean_box(0);
                        v_isShared_7964_ = v_isSharedCheck_7972_;
                        state = 59;
                        continue;
                    }
                }
            },
            1 => {
                v_aig_7604_ = crate::leanh::lean_ctor_get(v_result_7599_, 0);
                crate::leanh::lean_inc_ref(v_aig_7604_);
                v_vec_7605_ = crate::leanh::lean_ctor_get(v_result_7599_, 1);
                crate::leanh::lean_inc_ref(v_vec_7605_);
                crate::leanh::lean_dec_ref(v_result_7599_);
                v___x_7606_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7606_, 0, v_w_7595_);
                crate::leanh::lean_ctor_set(v___x_7606_, 1, v_vec_7605_);
                crate::leanh::lean_ctor_set(v___x_7606_, 2, v_start_7596_);
                v_res_7607_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(v_w_7584_, v_aig_7604_, v___x_7606_);
                crate::leanh::lean_dec_ref_known(v___x_7606_, 3);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7602_, 0, v_res_7607_);
                    v___x_7609_ = v___x_7602_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7610_, 0, v_res_7607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7610_, 1, v_cache_7600_);
                    v___x_7609_ = v_reuseFailAlloc_7610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7609_;
            }
            3 => {
                v_aig_7626_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7627_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7638_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7638_ == 0 {
                    v___x_7629_ = v_result_7621_;
                    v_isShared_7630_ = v_isSharedCheck_7638_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7627_);
                    crate::leanh::lean_inc(v_aig_7626_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7629_ = crate::leanh::lean_box(0);
                    v_isShared_7630_ = v_isSharedCheck_7638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7629_, 0, v_vec_7619_);
                    v___x_7632_ = v___x_7629_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7637_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7637_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7637_, 1, v_vec_7627_);
                    v___x_7632_ = v_reuseFailAlloc_7637_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_res_7633_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___redArg(v_w_7584_, v_aig_7626_, v___x_7632_);
                crate::leanh::lean_dec_ref(v___x_7632_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7624_, 0, v_res_7633_);
                    v___x_7635_ = v___x_7624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7636_, 0, v_res_7633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7636_, 1, v_cache_7622_);
                    v___x_7635_ = v_reuseFailAlloc_7636_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7635_;
            }
            7 => {
                v_aig_7645_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7646_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7657_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7657_ == 0 {
                    v___x_7648_ = v_result_7621_;
                    v_isShared_7649_ = v_isSharedCheck_7657_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7646_);
                    crate::leanh::lean_inc(v_aig_7645_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7648_ = crate::leanh::lean_box(0);
                    v_isShared_7649_ = v_isSharedCheck_7657_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_7649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7648_, 0, v_vec_7619_);
                    v___x_7651_ = v___x_7648_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7656_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7656_, 1, v_vec_7646_);
                    v___x_7651_ = v_reuseFailAlloc_7656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_res_7652_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___redArg(v_w_7584_, v_aig_7645_, v___x_7651_);
                crate::leanh::lean_dec_ref(v___x_7651_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7643_, 0, v_res_7652_);
                    v___x_7654_ = v___x_7643_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7655_, 0, v_res_7652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7655_, 1, v_cache_7641_);
                    v___x_7654_ = v_reuseFailAlloc_7655_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7654_;
            }
            11 => {
                v_aig_7664_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7665_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7676_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7676_ == 0 {
                    v___x_7667_ = v_result_7621_;
                    v_isShared_7668_ = v_isSharedCheck_7676_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7665_);
                    crate::leanh::lean_inc(v_aig_7664_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7667_ = crate::leanh::lean_box(0);
                    v_isShared_7668_ = v_isSharedCheck_7676_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_7668_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7667_, 0, v_vec_7619_);
                    v___x_7670_ = v___x_7667_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 1, v_vec_7665_);
                    v___x_7670_ = v_reuseFailAlloc_7675_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_res_7671_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___redArg(v_w_7584_, v_aig_7664_, v___x_7670_);
                crate::leanh::lean_dec_ref(v___x_7670_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7662_, 0, v_res_7671_);
                    v___x_7673_ = v___x_7662_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7674_, 0, v_res_7671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7674_, 1, v_cache_7660_);
                    v___x_7673_ = v_reuseFailAlloc_7674_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7673_;
            }
            15 => {
                v_aig_7683_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7684_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7695_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7695_ == 0 {
                    v___x_7686_ = v_result_7621_;
                    v_isShared_7687_ = v_isSharedCheck_7695_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7684_);
                    crate::leanh::lean_inc(v_aig_7683_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7686_ = crate::leanh::lean_box(0);
                    v_isShared_7687_ = v_isSharedCheck_7695_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_7687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7686_, 0, v_vec_7619_);
                    v___x_7689_ = v___x_7686_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 1, v_vec_7684_);
                    v___x_7689_ = v_reuseFailAlloc_7694_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v_res_7690_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11(v_w_7584_, v_aig_7683_, v___x_7689_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7681_, 0, v_res_7690_);
                    v___x_7692_ = v___x_7681_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7693_, 0, v_res_7690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7693_, 1, v_cache_7679_);
                    v___x_7692_ = v_reuseFailAlloc_7693_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7692_;
            }
            19 => {
                v_aig_7702_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7703_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7714_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7714_ == 0 {
                    v___x_7705_ = v_result_7621_;
                    v_isShared_7706_ = v_isSharedCheck_7714_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7703_);
                    crate::leanh::lean_inc(v_aig_7702_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7705_ = crate::leanh::lean_box(0);
                    v_isShared_7706_ = v_isSharedCheck_7714_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_7706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7705_, 0, v_vec_7619_);
                    v___x_7708_ = v___x_7705_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 1, v_vec_7703_);
                    v___x_7708_ = v_reuseFailAlloc_7713_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_res_7709_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(v_w_7584_, v_aig_7702_, v___x_7708_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7700_, 0, v_res_7709_);
                    v___x_7711_ = v___x_7700_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7712_, 0, v_res_7709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7712_, 1, v_cache_7698_);
                    v___x_7711_ = v_reuseFailAlloc_7712_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7711_;
            }
            23 => {
                v_aig_7721_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7722_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7733_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7733_ == 0 {
                    v___x_7724_ = v_result_7621_;
                    v_isShared_7725_ = v_isSharedCheck_7733_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7722_);
                    crate::leanh::lean_inc(v_aig_7721_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7724_ = crate::leanh::lean_box(0);
                    v_isShared_7725_ = v_isSharedCheck_7733_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_7725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7724_, 0, v_vec_7619_);
                    v___x_7727_ = v___x_7724_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 1, v_vec_7722_);
                    v___x_7727_ = v_reuseFailAlloc_7732_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v_res_7728_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13(v_w_7584_, v_aig_7721_, v___x_7727_);
                if v_isShared_7720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7719_, 0, v_res_7728_);
                    v___x_7730_ = v___x_7719_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v_res_7728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 1, v_cache_7717_);
                    v___x_7730_ = v_reuseFailAlloc_7731_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7730_;
            }
            27 => {
                v_aig_7740_ = crate::leanh::lean_ctor_get(v_result_7621_, 0);
                v_vec_7741_ = crate::leanh::lean_ctor_get(v_result_7621_, 1);
                v_isSharedCheck_7752_ = (!crate::leanh::lean_is_exclusive(v_result_7621_)) as u8;
                if v_isSharedCheck_7752_ == 0 {
                    v___x_7743_ = v_result_7621_;
                    v_isShared_7744_ = v_isSharedCheck_7752_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7741_);
                    crate::leanh::lean_inc(v_aig_7740_);
                    crate::leanh::lean_dec(v_result_7621_);
                    v___x_7743_ = crate::leanh::lean_box(0);
                    v_isShared_7744_ = v_isSharedCheck_7752_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_7744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7743_, 0, v_vec_7619_);
                    v___x_7746_ = v___x_7743_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7751_, 0, v_vec_7619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7751_, 1, v_vec_7741_);
                    v___x_7746_ = v_reuseFailAlloc_7751_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v_res_7747_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__14(v_w_7584_, v_aig_7740_, v___x_7746_);
                if v_isShared_7739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7738_, 0, v_res_7747_);
                    v___x_7749_ = v___x_7738_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7750_, 0, v_res_7747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7750_, 1, v_cache_7736_);
                    v___x_7749_ = v_reuseFailAlloc_7750_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_7749_;
            }
            31 => {
                v_aig_7763_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                crate::leanh::lean_inc_ref(v_aig_7763_);
                v_vec_7764_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                crate::leanh::lean_inc_ref(v_vec_7764_);
                crate::leanh::lean_dec_ref(v_result_7758_);
                v_res_7765_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15(v_w_7584_, v_aig_7763_, v_vec_7764_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7761_, 0, v_res_7765_);
                    v___x_7767_ = v___x_7761_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_7768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7768_, 0, v_res_7765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7768_, 1, v_cache_7759_);
                    v___x_7767_ = v_reuseFailAlloc_7768_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_7767_;
            }
            33 => {
                v_aig_7775_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                v_vec_7776_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                v_isSharedCheck_7788_ = (!crate::leanh::lean_is_exclusive(v_result_7758_)) as u8;
                if v_isSharedCheck_7788_ == 0 {
                    v___x_7778_ = v_result_7758_;
                    v_isShared_7779_ = v_isSharedCheck_7788_;
                    state = 34;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7776_);
                    crate::leanh::lean_inc(v_aig_7775_);
                    crate::leanh::lean_dec(v_result_7758_);
                    v___x_7778_ = crate::leanh::lean_box(0);
                    v_isShared_7779_ = v_isSharedCheck_7788_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v_n_7780_ = crate::leanh::lean_ctor_get(v_op_7755_, 0);
                crate::leanh::lean_inc(v_n_7780_);
                crate::leanh::lean_dec_ref_known(v_op_7755_, 1);
                if v_isShared_7779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7778_, 1, v_n_7780_);
                    crate::leanh::lean_ctor_set(v___x_7778_, 0, v_vec_7776_);
                    v___x_7782_ = v___x_7778_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7787_, 0, v_vec_7776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7787_, 1, v_n_7780_);
                    v___x_7782_ = v_reuseFailAlloc_7787_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v_res_7783_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16(v_w_7584_, v_aig_7775_, v___x_7782_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7774_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7773_, 0, v_res_7783_);
                    v___x_7785_ = v___x_7773_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_7786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7786_, 0, v_res_7783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7786_, 1, v_cache_7771_);
                    v___x_7785_ = v_reuseFailAlloc_7786_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_7785_;
            }
            37 => {
                v_aig_7795_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                v_vec_7796_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                v_isSharedCheck_7808_ = (!crate::leanh::lean_is_exclusive(v_result_7758_)) as u8;
                if v_isSharedCheck_7808_ == 0 {
                    v___x_7798_ = v_result_7758_;
                    v_isShared_7799_ = v_isSharedCheck_7808_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7796_);
                    crate::leanh::lean_inc(v_aig_7795_);
                    crate::leanh::lean_dec(v_result_7758_);
                    v___x_7798_ = crate::leanh::lean_box(0);
                    v_isShared_7799_ = v_isSharedCheck_7808_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v_n_7800_ = crate::leanh::lean_ctor_get(v_op_7755_, 0);
                crate::leanh::lean_inc(v_n_7800_);
                crate::leanh::lean_dec_ref_known(v_op_7755_, 1);
                if v_isShared_7799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7798_, 1, v_n_7800_);
                    crate::leanh::lean_ctor_set(v___x_7798_, 0, v_vec_7796_);
                    v___x_7802_ = v___x_7798_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_7807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7807_, 0, v_vec_7796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7807_, 1, v_n_7800_);
                    v___x_7802_ = v_reuseFailAlloc_7807_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v_res_7803_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17(v_w_7584_, v_aig_7795_, v___x_7802_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7793_, 0, v_res_7803_);
                    v___x_7805_ = v___x_7793_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_7806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7806_, 0, v_res_7803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7806_, 1, v_cache_7791_);
                    v___x_7805_ = v_reuseFailAlloc_7806_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_7805_;
            }
            41 => {
                v_aig_7815_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                v_vec_7816_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                v_isSharedCheck_7828_ = (!crate::leanh::lean_is_exclusive(v_result_7758_)) as u8;
                if v_isSharedCheck_7828_ == 0 {
                    v___x_7818_ = v_result_7758_;
                    v_isShared_7819_ = v_isSharedCheck_7828_;
                    state = 42;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_7816_);
                    crate::leanh::lean_inc(v_aig_7815_);
                    crate::leanh::lean_dec(v_result_7758_);
                    v___x_7818_ = crate::leanh::lean_box(0);
                    v_isShared_7819_ = v_isSharedCheck_7828_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v_n_7820_ = crate::leanh::lean_ctor_get(v_op_7755_, 0);
                crate::leanh::lean_inc(v_n_7820_);
                crate::leanh::lean_dec_ref_known(v_op_7755_, 1);
                if v_isShared_7819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7818_, 1, v_n_7820_);
                    crate::leanh::lean_ctor_set(v___x_7818_, 0, v_vec_7816_);
                    v___x_7822_ = v___x_7818_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_7827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7827_, 0, v_vec_7816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7827_, 1, v_n_7820_);
                    v___x_7822_ = v_reuseFailAlloc_7827_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v_res_7823_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18(v_w_7584_, v_aig_7815_, v___x_7822_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7813_, 0, v_res_7823_);
                    v___x_7825_ = v___x_7813_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_7826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7826_, 0, v_res_7823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7826_, 1, v_cache_7811_);
                    v___x_7825_ = v_reuseFailAlloc_7826_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_7825_;
            }
            45 => {
                v_aig_7835_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                crate::leanh::lean_inc_ref(v_aig_7835_);
                v_vec_7836_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                crate::leanh::lean_inc_ref(v_vec_7836_);
                crate::leanh::lean_dec_ref(v_result_7758_);
                v_res_7837_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19___redArg(v_aig_7835_, v_vec_7836_);
                if v_isShared_7834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7833_, 0, v_res_7837_);
                    v___x_7839_ = v___x_7833_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_7840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7840_, 0, v_res_7837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7840_, 1, v_cache_7831_);
                    v___x_7839_ = v_reuseFailAlloc_7840_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_7839_;
            }
            47 => {
                v_aig_7847_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                crate::leanh::lean_inc_ref(v_aig_7847_);
                v_vec_7848_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                crate::leanh::lean_inc_ref(v_vec_7848_);
                crate::leanh::lean_dec_ref(v_result_7758_);
                v_res_7849_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20(v_w_7584_, v_aig_7847_, v_vec_7848_);
                crate::leanh::lean_dec_ref(v_vec_7848_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7845_, 0, v_res_7849_);
                    v___x_7851_ = v___x_7845_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7852_, 0, v_res_7849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7852_, 1, v_cache_7843_);
                    v___x_7851_ = v_reuseFailAlloc_7852_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7851_;
            }
            49 => {
                v_aig_7859_ = crate::leanh::lean_ctor_get(v_result_7758_, 0);
                crate::leanh::lean_inc_ref(v_aig_7859_);
                v_vec_7860_ = crate::leanh::lean_ctor_get(v_result_7758_, 1);
                crate::leanh::lean_inc_ref(v_vec_7860_);
                crate::leanh::lean_dec_ref(v_result_7758_);
                v_res_7861_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21(v_w_7584_, v_aig_7859_, v_vec_7860_);
                if v_isShared_7858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7857_, 0, v_res_7861_);
                    v___x_7863_ = v___x_7857_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_7864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7864_, 0, v_res_7861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7864_, 1, v_cache_7855_);
                    v___x_7863_ = v_reuseFailAlloc_7864_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_7863_;
            }
            51 => {
                v_aig_7882_ = crate::leanh::lean_ctor_get(v_result_7877_, 0);
                crate::leanh::lean_inc_ref(v_aig_7882_);
                v_vec_7883_ = crate::leanh::lean_ctor_get(v_result_7877_, 1);
                crate::leanh::lean_inc_ref(v_vec_7883_);
                crate::leanh::lean_dec_ref(v_result_7877_);
                v___x_7884_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7884_, 0, v_l_7867_);
                crate::leanh::lean_ctor_set(v___x_7884_, 1, v_r_7868_);
                crate::leanh::lean_ctor_set(v___x_7884_, 2, v_vec_7875_);
                crate::leanh::lean_ctor_set(v___x_7884_, 3, v_vec_7883_);
                v_res_7885_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22___redArg(v_aig_7882_, v___x_7884_);
                if v_isShared_7881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7880_, 0, v_res_7885_);
                    v___x_7887_ = v___x_7880_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_7888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7888_, 0, v_res_7885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7888_, 1, v_cache_7878_);
                    v___x_7887_ = v_reuseFailAlloc_7888_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_7887_;
            }
            53 => {
                v_aig_7899_ = crate::leanh::lean_ctor_get(v_result_7894_, 0);
                crate::leanh::lean_inc_ref(v_aig_7899_);
                v_vec_7900_ = crate::leanh::lean_ctor_get(v_result_7894_, 1);
                crate::leanh::lean_inc_ref(v_vec_7900_);
                crate::leanh::lean_dec_ref(v_result_7894_);
                v___x_7901_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7901_, 0, v_w_7890_);
                crate::leanh::lean_ctor_set(v___x_7901_, 1, v_n_7891_);
                crate::leanh::lean_ctor_set(v___x_7901_, 2, v_vec_7900_);
                v_res_7902_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23(v_w_7584_, v_aig_7899_, v___x_7901_);
                crate::leanh::lean_dec_ref_known(v___x_7901_, 3);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7897_, 0, v_res_7902_);
                    v___x_7904_ = v___x_7897_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_7905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7905_, 0, v_res_7902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7905_, 1, v_cache_7895_);
                    v___x_7904_ = v_reuseFailAlloc_7905_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_7904_;
            }
            55 => {
                v_aig_7921_ = crate::leanh::lean_ctor_get(v_result_7916_, 0);
                crate::leanh::lean_inc_ref(v_aig_7921_);
                v_vec_7922_ = crate::leanh::lean_ctor_get(v_result_7916_, 1);
                crate::leanh::lean_inc_ref(v_vec_7922_);
                crate::leanh::lean_dec_ref(v_result_7916_);
                v___x_7923_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7923_, 0, v_n_7907_);
                crate::leanh::lean_ctor_set(v___x_7923_, 1, v_vec_7914_);
                crate::leanh::lean_ctor_set(v___x_7923_, 2, v_vec_7922_);
                v_res_7924_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24(v_w_7584_, v_aig_7921_, v___x_7923_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7919_, 0, v_res_7924_);
                    v___x_7926_ = v___x_7919_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7927_, 0, v_res_7924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7927_, 1, v_cache_7917_);
                    v___x_7926_ = v_reuseFailAlloc_7927_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_7926_;
            }
            57 => {
                v_aig_7943_ = crate::leanh::lean_ctor_get(v_result_7938_, 0);
                crate::leanh::lean_inc_ref(v_aig_7943_);
                v_vec_7944_ = crate::leanh::lean_ctor_get(v_result_7938_, 1);
                crate::leanh::lean_inc_ref(v_vec_7944_);
                crate::leanh::lean_dec_ref(v_result_7938_);
                v___x_7945_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7945_, 0, v_n_7929_);
                crate::leanh::lean_ctor_set(v___x_7945_, 1, v_vec_7936_);
                crate::leanh::lean_ctor_set(v___x_7945_, 2, v_vec_7944_);
                v_res_7946_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25(v_w_7584_, v_aig_7943_, v___x_7945_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7941_, 0, v_res_7946_);
                    v___x_7948_ = v___x_7941_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7949_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7949_, 0, v_res_7946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7949_, 1, v_cache_7939_);
                    v___x_7948_ = v_reuseFailAlloc_7949_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_7948_;
            }
            59 => {
                v_aig_7965_ = crate::leanh::lean_ctor_get(v_result_7960_, 0);
                crate::leanh::lean_inc_ref(v_aig_7965_);
                v_vec_7966_ = crate::leanh::lean_ctor_get(v_result_7960_, 1);
                crate::leanh::lean_inc_ref(v_vec_7966_);
                crate::leanh::lean_dec_ref(v_result_7960_);
                v___x_7967_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7967_, 0, v_n_7951_);
                crate::leanh::lean_ctor_set(v___x_7967_, 1, v_vec_7958_);
                crate::leanh::lean_ctor_set(v___x_7967_, 2, v_vec_7966_);
                v_res_7968_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__26(v_w_7584_, v_aig_7965_, v___x_7967_);
                crate::leanh::lean_dec(v_w_7584_);
                if v_isShared_7964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7963_, 0, v_res_7968_);
                    v___x_7970_ = v___x_7963_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7971_, 0, v_res_7968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7971_, 1, v_cache_7961_);
                    v___x_7970_ = v_reuseFailAlloc_7971_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_7970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
    mut v_w_7973_: *mut crate::leanh::LeanObject,
    mut v_aig_7974_: *mut crate::leanh::LeanObject,
    mut v_expr_7975_: *mut crate::leanh::LeanObject,
    mut v_cache_7976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7984_: u8 = 0;
    let mut v_vec_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7990_: u8 = 0;
    let mut v_val_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_expr_7975_);
                crate::leanh::lean_inc(v_w_7973_);
                v___x_7977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7977_, 0, v_w_7973_);
                crate::leanh::lean_ctor_set(v___x_7977_, 1, v_expr_7975_);
                v___x_7978_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___redArg(v_cache_7976_, v___x_7977_);
                if crate::leanh::lean_obj_tag(v___x_7978_) == 0 {
                    v___x_7979_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(
                        v_w_7973_,
                        v_aig_7974_,
                        v_expr_7975_,
                        v_cache_7976_,
                    );
                    v_result_7980_ = crate::leanh::lean_ctor_get(v___x_7979_, 0);
                    v_cache_7981_ = crate::leanh::lean_ctor_get(v___x_7979_, 1);
                    v_isSharedCheck_7990_ = (!crate::leanh::lean_is_exclusive(v___x_7979_)) as u8;
                    if v_isSharedCheck_7990_ == 0 {
                        v___x_7983_ = v___x_7979_;
                        v_isShared_7984_ = v_isSharedCheck_7990_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_7981_);
                        crate::leanh::lean_inc(v_result_7980_);
                        crate::leanh::lean_dec(v___x_7979_);
                        v___x_7983_ = crate::leanh::lean_box(0);
                        v_isShared_7984_ = v_isSharedCheck_7990_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7977_, 2);
                    crate::leanh::lean_dec_ref(v_expr_7975_);
                    crate::leanh::lean_dec(v_w_7973_);
                    v_val_7991_ = crate::leanh::lean_ctor_get(v___x_7978_, 0);
                    crate::leanh::lean_inc(v_val_7991_);
                    crate::leanh::lean_dec_ref_known(v___x_7978_, 1);
                    v___x_7992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7992_, 0, v_aig_7974_);
                    crate::leanh::lean_ctor_set(v___x_7992_, 1, v_val_7991_);
                    v___x_7993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7993_, 0, v___x_7992_);
                    crate::leanh::lean_ctor_set(v___x_7993_, 1, v_cache_7976_);
                    return v___x_7993_;
                }
            }
            1 => {
                v_vec_7985_ = crate::leanh::lean_ctor_get(v_result_7980_, 1);
                crate::leanh::lean_inc_ref(v_vec_7985_);
                v___x_7986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1___redArg(v_cache_7981_, v___x_7977_, v_vec_7985_);
                if v_isShared_7984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7983_, 1, v___x_7986_);
                    v___x_7988_ = v___x_7983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7989_, 0, v_result_7980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7989_, 1, v___x_7986_);
                    v___x_7988_ = v_reuseFailAlloc_7989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19(
    mut v_w_7994_: *mut crate::leanh::LeanObject,
    mut v_aig_7995_: *mut crate::leanh::LeanObject,
    mut v_s_7996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7997_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19___redArg(v_aig_7995_, v_s_7996_);
    return v___x_7997_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19___boxed(
    mut v_w_7998_: *mut crate::leanh::LeanObject,
    mut v_aig_7999_: *mut crate::leanh::LeanObject,
    mut v_s_8000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8001_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__19(v_w_7998_, v_aig_7999_, v_s_8000_);
    crate::leanh::lean_dec(v_w_7998_);
    return v_res_8001_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22(
    mut v_newWidth_8002_: *mut crate::leanh::LeanObject,
    mut v_aig_8003_: *mut crate::leanh::LeanObject,
    mut v_target_8004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8005_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22___redArg(v_aig_8003_, v_target_8004_);
    return v___x_8005_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22___boxed(
    mut v_newWidth_8006_: *mut crate::leanh::LeanObject,
    mut v_aig_8007_: *mut crate::leanh::LeanObject,
    mut v_target_8008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8009_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__22(v_newWidth_8006_, v_aig_8007_, v_target_8008_);
    crate::leanh::lean_dec(v_newWidth_8006_);
    return v_res_8009_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0(
    mut v_00_u03b2_8010_: *mut crate::leanh::LeanObject,
    mut v_inst_8011_: *mut crate::leanh::LeanObject,
    mut v_m_8012_: *mut crate::leanh::LeanObject,
    mut v_a_8013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8014_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___redArg(v_m_8012_, v_a_8013_);
    return v___x_8014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0___boxed(
    mut v_00_u03b2_8015_: *mut crate::leanh::LeanObject,
    mut v_inst_8016_: *mut crate::leanh::LeanObject,
    mut v_m_8017_: *mut crate::leanh::LeanObject,
    mut v_a_8018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8019_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0(v_00_u03b2_8015_, v_inst_8016_, v_m_8017_, v_a_8018_);
    crate::leanh::lean_dec_ref(v_a_8018_);
    crate::leanh::lean_dec_ref(v_m_8017_);
    return v_res_8019_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1(
    mut v_00_u03b2_8020_: *mut crate::leanh::LeanObject,
    mut v_m_8021_: *mut crate::leanh::LeanObject,
    mut v_a_8022_: *mut crate::leanh::LeanObject,
    mut v_b_8023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8024_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1___redArg(v_m_8021_, v_a_8022_, v_b_8023_);
    return v___x_8024_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7___redArg(
    mut v_c_8025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8026_ = lean_mk_empty_array_with_capacity(v_c_8025_);
    return v___x_8026_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7___redArg___boxed(
    mut v_c_8027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8028_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7___redArg(v_c_8027_);
    crate::leanh::lean_dec(v_c_8027_);
    return v_res_8028_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7(
    mut v_aig_8029_: *mut crate::leanh::LeanObject,
    mut v_c_8030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8031_ = lean_mk_empty_array_with_capacity(v_c_8030_);
    return v___x_8031_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7___boxed(
    mut v_aig_8032_: *mut crate::leanh::LeanObject,
    mut v_c_8033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8034_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__7(v_aig_8032_, v_c_8033_);
    crate::leanh::lean_dec(v_c_8033_);
    crate::leanh::lean_dec_ref(v_aig_8032_);
    return v_res_8034_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6(
    mut v_len_8035_: *mut crate::leanh::LeanObject,
    mut v_aig_8036_: *mut crate::leanh::LeanObject,
    mut v_input_8037_: *mut crate::leanh::LeanObject,
    mut v_inst_8038_: *mut crate::leanh::LeanObject,
    mut v_inst_8039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8040_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___redArg(
            v_len_8035_,
            v_aig_8036_,
            v_input_8037_,
        );
    return v___x_8040_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6___boxed(
    mut v_len_8041_: *mut crate::leanh::LeanObject,
    mut v_aig_8042_: *mut crate::leanh::LeanObject,
    mut v_input_8043_: *mut crate::leanh::LeanObject,
    mut v_inst_8044_: *mut crate::leanh::LeanObject,
    mut v_inst_8045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8046_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6(
        v_len_8041_,
        v_aig_8042_,
        v_input_8043_,
        v_inst_8044_,
        v_inst_8045_,
    );
    crate::leanh::lean_dec_ref(v_input_8043_);
    crate::leanh::lean_dec(v_len_8041_);
    return v_res_8046_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8(
    mut v_len_8047_: *mut crate::leanh::LeanObject,
    mut v_aig_8048_: *mut crate::leanh::LeanObject,
    mut v_input_8049_: *mut crate::leanh::LeanObject,
    mut v_inst_8050_: *mut crate::leanh::LeanObject,
    mut v_inst_8051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8052_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___redArg(
            v_len_8047_,
            v_aig_8048_,
            v_input_8049_,
        );
    return v___x_8052_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8___boxed(
    mut v_len_8053_: *mut crate::leanh::LeanObject,
    mut v_aig_8054_: *mut crate::leanh::LeanObject,
    mut v_input_8055_: *mut crate::leanh::LeanObject,
    mut v_inst_8056_: *mut crate::leanh::LeanObject,
    mut v_inst_8057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8058_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8(
        v_len_8053_,
        v_aig_8054_,
        v_input_8055_,
        v_inst_8056_,
        v_inst_8057_,
    );
    crate::leanh::lean_dec_ref(v_input_8055_);
    crate::leanh::lean_dec(v_len_8053_);
    return v_res_8058_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10(
    mut v_len_8059_: *mut crate::leanh::LeanObject,
    mut v_aig_8060_: *mut crate::leanh::LeanObject,
    mut v_input_8061_: *mut crate::leanh::LeanObject,
    mut v_inst_8062_: *mut crate::leanh::LeanObject,
    mut v_inst_8063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8064_ =
        l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___redArg(
            v_len_8059_,
            v_aig_8060_,
            v_input_8061_,
        );
    return v___x_8064_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10___boxed(
    mut v_len_8065_: *mut crate::leanh::LeanObject,
    mut v_aig_8066_: *mut crate::leanh::LeanObject,
    mut v_input_8067_: *mut crate::leanh::LeanObject,
    mut v_inst_8068_: *mut crate::leanh::LeanObject,
    mut v_inst_8069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8070_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10(
        v_len_8065_,
        v_aig_8066_,
        v_input_8067_,
        v_inst_8068_,
        v_inst_8069_,
    );
    crate::leanh::lean_dec_ref(v_input_8067_);
    crate::leanh::lean_dec(v_len_8065_);
    return v_res_8070_;
}
pub unsafe fn l_Nat_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__41(
    mut v_w_8071_: *mut crate::leanh::LeanObject,
    mut v_a_8072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8073_ = l_BitVec_ofNat(v_w_8071_, v_a_8072_);
    return v___x_8073_;
}
pub unsafe fn l_Nat_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__41___boxed(
    mut v_w_8074_: *mut crate::leanh::LeanObject,
    mut v_a_8075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8076_ = l_Nat_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__20_spec__41(v_w_8074_, v_a_8075_);
    crate::leanh::lean_dec(v_a_8075_);
    crate::leanh::lean_dec(v_w_8074_);
    return v_res_8076_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0(
    mut v_00_u03b2_8077_: *mut crate::leanh::LeanObject,
    mut v_inst_8078_: *mut crate::leanh::LeanObject,
    mut v_a_8079_: *mut crate::leanh::LeanObject,
    mut v_x_8080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8081_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___redArg(v_a_8079_, v_x_8080_);
    return v___x_8081_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0___boxed(
    mut v_00_u03b2_8082_: *mut crate::leanh::LeanObject,
    mut v_inst_8083_: *mut crate::leanh::LeanObject,
    mut v_a_8084_: *mut crate::leanh::LeanObject,
    mut v_x_8085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8086_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__0_spec__0(v_00_u03b2_8082_, v_inst_8083_, v_a_8084_, v_x_8085_);
    crate::leanh::lean_dec(v_x_8085_);
    crate::leanh::lean_dec_ref(v_a_8084_);
    return v_res_8086_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2(
    mut v_00_u03b2_8087_: *mut crate::leanh::LeanObject,
    mut v_a_8088_: *mut crate::leanh::LeanObject,
    mut v_x_8089_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8090_: u8 = 0;
    v___x_8090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___redArg(v_a_8088_, v_x_8089_);
    return v___x_8090_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2___boxed(
    mut v_00_u03b2_8091_: *mut crate::leanh::LeanObject,
    mut v_a_8092_: *mut crate::leanh::LeanObject,
    mut v_x_8093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8094_: u8 = 0;
    let mut v_r_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8094_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__2(v_00_u03b2_8091_, v_a_8092_, v_x_8093_);
    crate::leanh::lean_dec(v_x_8093_);
    crate::leanh::lean_dec_ref(v_a_8092_);
    v_r_8095_ = crate::leanh::lean_box((v_res_8094_) as usize);
    return v_r_8095_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3(
    mut v_00_u03b2_8096_: *mut crate::leanh::LeanObject,
    mut v_data_8097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3___redArg(v_data_8097_);
    return v___x_8098_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__4(
    mut v_00_u03b2_8099_: *mut crate::leanh::LeanObject,
    mut v_a_8100_: *mut crate::leanh::LeanObject,
    mut v_b_8101_: *mut crate::leanh::LeanObject,
    mut v_x_8102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8103_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__4___redArg(v_a_8100_, v_b_8101_, v_x_8102_);
    return v___x_8103_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8(
    mut v_w_8104_: *mut crate::leanh::LeanObject,
    mut v_aig_8105_: *mut crate::leanh::LeanObject,
    mut v_val_8106_: *mut crate::leanh::LeanObject,
    mut v_curr_8107_: *mut crate::leanh::LeanObject,
    mut v_s_8108_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8110_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___redArg(v_w_8104_, v_val_8106_, v_curr_8107_, v_s_8108_);
    return v___x_8110_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8___boxed(
    mut v_w_8111_: *mut crate::leanh::LeanObject,
    mut v_aig_8112_: *mut crate::leanh::LeanObject,
    mut v_val_8113_: *mut crate::leanh::LeanObject,
    mut v_curr_8114_: *mut crate::leanh::LeanObject,
    mut v_s_8115_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8117_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__3_spec__8(v_w_8111_, v_aig_8112_, v_val_8113_, v_curr_8114_, v_s_8115_, v_hcurr_8116_);
    crate::leanh::lean_dec(v_val_8113_);
    crate::leanh::lean_dec_ref(v_aig_8112_);
    crate::leanh::lean_dec(v_w_8111_);
    return v_res_8117_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10(
    mut v_newWidth_8118_: *mut crate::leanh::LeanObject,
    mut v_aig_8119_: *mut crate::leanh::LeanObject,
    mut v_w_8120_: *mut crate::leanh::LeanObject,
    mut v_input_8121_: *mut crate::leanh::LeanObject,
    mut v_start_8122_: *mut crate::leanh::LeanObject,
    mut v_curr_8123_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8124_: *mut crate::leanh::LeanObject,
    mut v_s_8125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8126_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___redArg(v_newWidth_8118_, v_w_8120_, v_input_8121_, v_start_8122_, v_curr_8123_, v_s_8125_);
    return v___x_8126_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10___boxed(
    mut v_newWidth_8127_: *mut crate::leanh::LeanObject,
    mut v_aig_8128_: *mut crate::leanh::LeanObject,
    mut v_w_8129_: *mut crate::leanh::LeanObject,
    mut v_input_8130_: *mut crate::leanh::LeanObject,
    mut v_start_8131_: *mut crate::leanh::LeanObject,
    mut v_curr_8132_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8133_: *mut crate::leanh::LeanObject,
    mut v_s_8134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8135_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4_spec__10(v_newWidth_8127_, v_aig_8128_, v_w_8129_, v_input_8130_, v_start_8131_, v_curr_8132_, v_hcurr_8133_, v_s_8134_);
    crate::leanh::lean_dec(v_start_8131_);
    crate::leanh::lean_dec_ref(v_input_8130_);
    crate::leanh::lean_dec(v_w_8129_);
    crate::leanh::lean_dec_ref(v_aig_8128_);
    crate::leanh::lean_dec(v_newWidth_8127_);
    return v_res_8135_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14(
    mut v_len_8136_: *mut crate::leanh::LeanObject,
    mut v_aig_8137_: *mut crate::leanh::LeanObject,
    mut v_idx_8138_: *mut crate::leanh::LeanObject,
    mut v_s_8139_: *mut crate::leanh::LeanObject,
    mut v_hidx_8140_: *mut crate::leanh::LeanObject,
    mut v_lhs_8141_: *mut crate::leanh::LeanObject,
    mut v_rhs_8142_: *mut crate::leanh::LeanObject,
    mut v_inst_8143_: *mut crate::leanh::LeanObject,
    mut v_inst_8144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8145_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___redArg(v_len_8136_, v_aig_8137_, v_idx_8138_, v_s_8139_, v_lhs_8141_, v_rhs_8142_);
    return v___x_8145_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14___boxed(
    mut v_len_8146_: *mut crate::leanh::LeanObject,
    mut v_aig_8147_: *mut crate::leanh::LeanObject,
    mut v_idx_8148_: *mut crate::leanh::LeanObject,
    mut v_s_8149_: *mut crate::leanh::LeanObject,
    mut v_hidx_8150_: *mut crate::leanh::LeanObject,
    mut v_lhs_8151_: *mut crate::leanh::LeanObject,
    mut v_rhs_8152_: *mut crate::leanh::LeanObject,
    mut v_inst_8153_: *mut crate::leanh::LeanObject,
    mut v_inst_8154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8155_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__6_spec__14(v_len_8146_, v_aig_8147_, v_idx_8148_, v_s_8149_, v_hidx_8150_, v_lhs_8151_, v_rhs_8152_, v_inst_8153_, v_inst_8154_);
    crate::leanh::lean_dec_ref(v_rhs_8152_);
    crate::leanh::lean_dec_ref(v_lhs_8151_);
    crate::leanh::lean_dec(v_len_8146_);
    return v_res_8155_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17(
    mut v_len_8156_: *mut crate::leanh::LeanObject,
    mut v_aig_8157_: *mut crate::leanh::LeanObject,
    mut v_idx_8158_: *mut crate::leanh::LeanObject,
    mut v_s_8159_: *mut crate::leanh::LeanObject,
    mut v_hidx_8160_: *mut crate::leanh::LeanObject,
    mut v_lhs_8161_: *mut crate::leanh::LeanObject,
    mut v_rhs_8162_: *mut crate::leanh::LeanObject,
    mut v_inst_8163_: *mut crate::leanh::LeanObject,
    mut v_inst_8164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8165_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___redArg(v_len_8156_, v_aig_8157_, v_idx_8158_, v_s_8159_, v_lhs_8161_, v_rhs_8162_);
    return v___x_8165_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17___boxed(
    mut v_len_8166_: *mut crate::leanh::LeanObject,
    mut v_aig_8167_: *mut crate::leanh::LeanObject,
    mut v_idx_8168_: *mut crate::leanh::LeanObject,
    mut v_s_8169_: *mut crate::leanh::LeanObject,
    mut v_hidx_8170_: *mut crate::leanh::LeanObject,
    mut v_lhs_8171_: *mut crate::leanh::LeanObject,
    mut v_rhs_8172_: *mut crate::leanh::LeanObject,
    mut v_inst_8173_: *mut crate::leanh::LeanObject,
    mut v_inst_8174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8175_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__8_spec__17(v_len_8166_, v_aig_8167_, v_idx_8168_, v_s_8169_, v_hidx_8170_, v_lhs_8171_, v_rhs_8172_, v_inst_8173_, v_inst_8174_);
    crate::leanh::lean_dec_ref(v_rhs_8172_);
    crate::leanh::lean_dec_ref(v_lhs_8171_);
    crate::leanh::lean_dec(v_len_8166_);
    return v_res_8175_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20(
    mut v_len_8176_: *mut crate::leanh::LeanObject,
    mut v_aig_8177_: *mut crate::leanh::LeanObject,
    mut v_idx_8178_: *mut crate::leanh::LeanObject,
    mut v_s_8179_: *mut crate::leanh::LeanObject,
    mut v_hidx_8180_: *mut crate::leanh::LeanObject,
    mut v_lhs_8181_: *mut crate::leanh::LeanObject,
    mut v_rhs_8182_: *mut crate::leanh::LeanObject,
    mut v_inst_8183_: *mut crate::leanh::LeanObject,
    mut v_inst_8184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8185_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___redArg(v_len_8176_, v_aig_8177_, v_idx_8178_, v_s_8179_, v_lhs_8181_, v_rhs_8182_);
    return v___x_8185_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20___boxed(
    mut v_len_8186_: *mut crate::leanh::LeanObject,
    mut v_aig_8187_: *mut crate::leanh::LeanObject,
    mut v_idx_8188_: *mut crate::leanh::LeanObject,
    mut v_s_8189_: *mut crate::leanh::LeanObject,
    mut v_hidx_8190_: *mut crate::leanh::LeanObject,
    mut v_lhs_8191_: *mut crate::leanh::LeanObject,
    mut v_rhs_8192_: *mut crate::leanh::LeanObject,
    mut v_inst_8193_: *mut crate::leanh::LeanObject,
    mut v_inst_8194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8195_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__10_spec__20(v_len_8186_, v_aig_8187_, v_idx_8188_, v_s_8189_, v_hidx_8190_, v_lhs_8191_, v_rhs_8192_, v_inst_8193_, v_inst_8194_);
    crate::leanh::lean_dec_ref(v_rhs_8192_);
    crate::leanh::lean_dec_ref(v_lhs_8191_);
    crate::leanh::lean_dec(v_len_8186_);
    return v_res_8195_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34(
    mut v_w_8196_: *mut crate::leanh::LeanObject,
    mut v_aig_8197_: *mut crate::leanh::LeanObject,
    mut v_input_8198_: *mut crate::leanh::LeanObject,
    mut v_distance_8199_: *mut crate::leanh::LeanObject,
    mut v_curr_8200_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8201_: *mut crate::leanh::LeanObject,
    mut v_s_8202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8203_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___redArg(v_w_8196_, v_input_8198_, v_distance_8199_, v_curr_8200_, v_s_8202_);
    return v___x_8203_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34___boxed(
    mut v_w_8204_: *mut crate::leanh::LeanObject,
    mut v_aig_8205_: *mut crate::leanh::LeanObject,
    mut v_input_8206_: *mut crate::leanh::LeanObject,
    mut v_distance_8207_: *mut crate::leanh::LeanObject,
    mut v_curr_8208_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8209_: *mut crate::leanh::LeanObject,
    mut v_s_8210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8211_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__16_spec__34(v_w_8204_, v_aig_8205_, v_input_8206_, v_distance_8207_, v_curr_8208_, v_hcurr_8209_, v_s_8210_);
    crate::leanh::lean_dec(v_distance_8207_);
    crate::leanh::lean_dec_ref(v_input_8206_);
    crate::leanh::lean_dec_ref(v_aig_8205_);
    crate::leanh::lean_dec(v_w_8204_);
    return v_res_8211_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36(
    mut v_w_8212_: *mut crate::leanh::LeanObject,
    mut v_aig_8213_: *mut crate::leanh::LeanObject,
    mut v_input_8214_: *mut crate::leanh::LeanObject,
    mut v_distance_8215_: *mut crate::leanh::LeanObject,
    mut v_curr_8216_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8217_: *mut crate::leanh::LeanObject,
    mut v_s_8218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8219_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___redArg(v_w_8212_, v_input_8214_, v_distance_8215_, v_curr_8216_, v_s_8218_);
    return v___x_8219_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36___boxed(
    mut v_w_8220_: *mut crate::leanh::LeanObject,
    mut v_aig_8221_: *mut crate::leanh::LeanObject,
    mut v_input_8222_: *mut crate::leanh::LeanObject,
    mut v_distance_8223_: *mut crate::leanh::LeanObject,
    mut v_curr_8224_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8225_: *mut crate::leanh::LeanObject,
    mut v_s_8226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8227_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__17_spec__36(v_w_8220_, v_aig_8221_, v_input_8222_, v_distance_8223_, v_curr_8224_, v_hcurr_8225_, v_s_8226_);
    crate::leanh::lean_dec(v_distance_8223_);
    crate::leanh::lean_dec_ref(v_input_8222_);
    crate::leanh::lean_dec_ref(v_aig_8221_);
    crate::leanh::lean_dec(v_w_8220_);
    return v_res_8227_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38(
    mut v_w_8228_: *mut crate::leanh::LeanObject,
    mut v_aig_8229_: *mut crate::leanh::LeanObject,
    mut v_input_8230_: *mut crate::leanh::LeanObject,
    mut v_distance_8231_: *mut crate::leanh::LeanObject,
    mut v_curr_8232_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8233_: *mut crate::leanh::LeanObject,
    mut v_s_8234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8235_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___redArg(v_w_8228_, v_input_8230_, v_distance_8231_, v_curr_8232_, v_s_8234_);
    return v___x_8235_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38___boxed(
    mut v_w_8236_: *mut crate::leanh::LeanObject,
    mut v_aig_8237_: *mut crate::leanh::LeanObject,
    mut v_input_8238_: *mut crate::leanh::LeanObject,
    mut v_distance_8239_: *mut crate::leanh::LeanObject,
    mut v_curr_8240_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8241_: *mut crate::leanh::LeanObject,
    mut v_s_8242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8243_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__18_spec__38(v_w_8236_, v_aig_8237_, v_input_8238_, v_distance_8239_, v_curr_8240_, v_hcurr_8241_, v_s_8242_);
    crate::leanh::lean_dec(v_distance_8239_);
    crate::leanh::lean_dec_ref(v_input_8238_);
    crate::leanh::lean_dec_ref(v_aig_8237_);
    crate::leanh::lean_dec(v_w_8236_);
    return v_res_8243_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48(
    mut v_aig_8244_: *mut crate::leanh::LeanObject,
    mut v_w_8245_: *mut crate::leanh::LeanObject,
    mut v_n_8246_: *mut crate::leanh::LeanObject,
    mut v_input_8247_: *mut crate::leanh::LeanObject,
    mut v_curr_8248_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8249_: *mut crate::leanh::LeanObject,
    mut v_s_8250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8251_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___redArg(v_n_8246_, v_input_8247_, v_curr_8248_, v_s_8250_);
    return v___x_8251_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48___boxed(
    mut v_aig_8252_: *mut crate::leanh::LeanObject,
    mut v_w_8253_: *mut crate::leanh::LeanObject,
    mut v_n_8254_: *mut crate::leanh::LeanObject,
    mut v_input_8255_: *mut crate::leanh::LeanObject,
    mut v_curr_8256_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8257_: *mut crate::leanh::LeanObject,
    mut v_s_8258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8259_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__23_spec__48(v_aig_8252_, v_w_8253_, v_n_8254_, v_input_8255_, v_curr_8256_, v_hcurr_8257_, v_s_8258_);
    crate::leanh::lean_dec_ref(v_input_8255_);
    crate::leanh::lean_dec(v_n_8254_);
    crate::leanh::lean_dec(v_w_8253_);
    crate::leanh::lean_dec_ref(v_aig_8252_);
    return v_res_8259_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7(
    mut v_00_u03b2_8260_: *mut crate::leanh::LeanObject,
    mut v_i_8261_: *mut crate::leanh::LeanObject,
    mut v_source_8262_: *mut crate::leanh::LeanObject,
    mut v_target_8263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8264_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7___redArg(v_i_8261_, v_source_8262_, v_target_8263_);
    return v___x_8264_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16(
    mut v_00_u03b2_8265_: *mut crate::leanh::LeanObject,
    mut v_m_8266_: *mut crate::leanh::LeanObject,
    mut v_a_8267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___redArg(v_m_8266_, v_a_8267_);
    return v___x_8268_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16___boxed(
    mut v_00_u03b2_8269_: *mut crate::leanh::LeanObject,
    mut v_m_8270_: *mut crate::leanh::LeanObject,
    mut v_a_8271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16(v_00_u03b2_8269_, v_m_8270_, v_a_8271_);
    crate::leanh::lean_dec_ref(v_m_8270_);
    return v_res_8272_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18(
    mut v_00_u03b2_8273_: *mut crate::leanh::LeanObject,
    mut v_m_8274_: *mut crate::leanh::LeanObject,
    mut v_a_8275_: *mut crate::leanh::LeanObject,
    mut v_b_8276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18___redArg(v_m_8274_, v_a_8275_, v_b_8276_);
    return v___x_8277_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31(
    mut v_w_8278_: *mut crate::leanh::LeanObject,
    mut v_aig_8279_: *mut crate::leanh::LeanObject,
    mut v_lhs_8280_: *mut crate::leanh::LeanObject,
    mut v_rhs_8281_: *mut crate::leanh::LeanObject,
    mut v_curr_8282_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8283_: *mut crate::leanh::LeanObject,
    mut v_cin_8284_: *mut crate::leanh::LeanObject,
    mut v_s_8285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8286_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___redArg(v_w_8278_, v_aig_8279_, v_lhs_8280_, v_rhs_8281_, v_curr_8282_, v_cin_8284_, v_s_8285_);
    return v___x_8286_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31___boxed(
    mut v_w_8287_: *mut crate::leanh::LeanObject,
    mut v_aig_8288_: *mut crate::leanh::LeanObject,
    mut v_lhs_8289_: *mut crate::leanh::LeanObject,
    mut v_rhs_8290_: *mut crate::leanh::LeanObject,
    mut v_curr_8291_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8292_: *mut crate::leanh::LeanObject,
    mut v_cin_8293_: *mut crate::leanh::LeanObject,
    mut v_s_8294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8295_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31(v_w_8287_, v_aig_8288_, v_lhs_8289_, v_rhs_8290_, v_curr_8291_, v_hcurr_8292_, v_cin_8293_, v_s_8294_);
    crate::leanh::lean_dec_ref(v_rhs_8290_);
    crate::leanh::lean_dec_ref(v_lhs_8289_);
    crate::leanh::lean_dec(v_w_8287_);
    return v_res_8295_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39(
    mut v_len_8296_: *mut crate::leanh::LeanObject,
    mut v_aig_8297_: *mut crate::leanh::LeanObject,
    mut v_input_8298_: *mut crate::leanh::LeanObject,
    mut v_inst_8299_: *mut crate::leanh::LeanObject,
    mut v_inst_8300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8301_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___redArg(v_len_8296_, v_aig_8297_, v_input_8298_);
    return v___x_8301_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39___boxed(
    mut v_len_8302_: *mut crate::leanh::LeanObject,
    mut v_aig_8303_: *mut crate::leanh::LeanObject,
    mut v_input_8304_: *mut crate::leanh::LeanObject,
    mut v_inst_8305_: *mut crate::leanh::LeanObject,
    mut v_inst_8306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8307_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39(v_len_8302_, v_aig_8303_, v_input_8304_, v_inst_8305_, v_inst_8306_);
    crate::leanh::lean_dec_ref(v_input_8304_);
    crate::leanh::lean_dec(v_len_8302_);
    return v_res_8307_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40(
    mut v_len_8308_: *mut crate::leanh::LeanObject,
    mut v_aig_8309_: *mut crate::leanh::LeanObject,
    mut v_vec_8310_: *mut crate::leanh::LeanObject,
    mut v_inst_8311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8312_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___redArg(v_len_8308_, v_aig_8309_, v_vec_8310_);
    return v___x_8312_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40___boxed(
    mut v_len_8313_: *mut crate::leanh::LeanObject,
    mut v_aig_8314_: *mut crate::leanh::LeanObject,
    mut v_vec_8315_: *mut crate::leanh::LeanObject,
    mut v_inst_8316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8317_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40(v_len_8313_, v_aig_8314_, v_vec_8315_, v_inst_8316_);
    crate::leanh::lean_dec_ref(v_vec_8315_);
    crate::leanh::lean_dec(v_len_8313_);
    return v_res_8317_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44(
    mut v_w_8318_: *mut crate::leanh::LeanObject,
    mut v_aig_8319_: *mut crate::leanh::LeanObject,
    mut v_curr_8320_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8321_: *mut crate::leanh::LeanObject,
    mut v_discr_8322_: *mut crate::leanh::LeanObject,
    mut v_lhs_8323_: *mut crate::leanh::LeanObject,
    mut v_rhs_8324_: *mut crate::leanh::LeanObject,
    mut v_s_8325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8326_ = l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___redArg(v_w_8318_, v_aig_8319_, v_curr_8320_, v_discr_8322_, v_lhs_8323_, v_rhs_8324_, v_s_8325_);
    return v___x_8326_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44___boxed(
    mut v_w_8327_: *mut crate::leanh::LeanObject,
    mut v_aig_8328_: *mut crate::leanh::LeanObject,
    mut v_curr_8329_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8330_: *mut crate::leanh::LeanObject,
    mut v_discr_8331_: *mut crate::leanh::LeanObject,
    mut v_lhs_8332_: *mut crate::leanh::LeanObject,
    mut v_rhs_8333_: *mut crate::leanh::LeanObject,
    mut v_s_8334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8335_ = l_Std_Sat_AIG_RefVec_ite_go___at___00Std_Sat_AIG_RefVec_ite___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__29_spec__44(v_w_8327_, v_aig_8328_, v_curr_8329_, v_hcurr_8330_, v_discr_8331_, v_lhs_8332_, v_rhs_8333_, v_s_8334_);
    crate::leanh::lean_dec_ref(v_rhs_8333_);
    crate::leanh::lean_dec_ref(v_lhs_8332_);
    crate::leanh::lean_dec(v_w_8327_);
    return v_res_8335_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48(
    mut v___x_8336_: *mut crate::leanh::LeanObject,
    mut v_len_8337_: *mut crate::leanh::LeanObject,
    mut v_aig_8338_: *mut crate::leanh::LeanObject,
    mut v_idx_8339_: *mut crate::leanh::LeanObject,
    mut v_hidx_8340_: *mut crate::leanh::LeanObject,
    mut v_s_8341_: *mut crate::leanh::LeanObject,
    mut v_input_8342_: *mut crate::leanh::LeanObject,
    mut v_inst_8343_: *mut crate::leanh::LeanObject,
    mut v_inst_8344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8345_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___redArg(v___x_8336_, v_len_8337_, v_aig_8338_, v_idx_8339_, v_s_8341_, v_input_8342_);
    return v___x_8345_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48___boxed(
    mut v___x_8346_: *mut crate::leanh::LeanObject,
    mut v_len_8347_: *mut crate::leanh::LeanObject,
    mut v_aig_8348_: *mut crate::leanh::LeanObject,
    mut v_idx_8349_: *mut crate::leanh::LeanObject,
    mut v_hidx_8350_: *mut crate::leanh::LeanObject,
    mut v_s_8351_: *mut crate::leanh::LeanObject,
    mut v_input_8352_: *mut crate::leanh::LeanObject,
    mut v_inst_8353_: *mut crate::leanh::LeanObject,
    mut v_inst_8354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8355_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__15_spec__32_spec__48(v___x_8346_, v_len_8347_, v_aig_8348_, v_idx_8349_, v_hidx_8350_, v_s_8351_, v_input_8352_, v_inst_8353_, v_inst_8354_);
    crate::leanh::lean_dec_ref(v_input_8352_);
    crate::leanh::lean_dec(v_len_8347_);
    return v_res_8355_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60(
    mut v_outWidth_8356_: *mut crate::leanh::LeanObject,
    mut v_aig_8357_: *mut crate::leanh::LeanObject,
    mut v_w_8358_: *mut crate::leanh::LeanObject,
    mut v_idx_8359_: *mut crate::leanh::LeanObject,
    mut v_x_8360_: *mut crate::leanh::LeanObject,
    mut v_acc_8361_: *mut crate::leanh::LeanObject,
    mut v_h_8362_: *mut crate::leanh::LeanObject,
    mut v_h_x27_8363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8364_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60___redArg(v_aig_8357_, v_w_8358_, v_idx_8359_, v_x_8360_, v_acc_8361_);
    return v___x_8364_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60___boxed(
    mut v_outWidth_8365_: *mut crate::leanh::LeanObject,
    mut v_aig_8366_: *mut crate::leanh::LeanObject,
    mut v_w_8367_: *mut crate::leanh::LeanObject,
    mut v_idx_8368_: *mut crate::leanh::LeanObject,
    mut v_x_8369_: *mut crate::leanh::LeanObject,
    mut v_acc_8370_: *mut crate::leanh::LeanObject,
    mut v_h_8371_: *mut crate::leanh::LeanObject,
    mut v_h_x27_8372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8373_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__44_spec__60(v_outWidth_8365_, v_aig_8366_, v_w_8367_, v_idx_8368_, v_x_8369_, v_acc_8370_, v_h_8371_, v_h_x27_8372_);
    crate::leanh::lean_dec(v_outWidth_8365_);
    return v_res_8373_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62(
    mut v_w_8374_: *mut crate::leanh::LeanObject,
    mut v_aig_8375_: *mut crate::leanh::LeanObject,
    mut v_len_8376_: *mut crate::leanh::LeanObject,
    mut v_x_8377_: *mut crate::leanh::LeanObject,
    mut v_h_8378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8379_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62___redArg(v_w_8374_, v_aig_8375_, v_len_8376_, v_x_8377_);
    return v___x_8379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7_spec__32(
    mut v_00_u03b2_8380_: *mut crate::leanh::LeanObject,
    mut v_x_8381_: *mut crate::leanh::LeanObject,
    mut v_x_8382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVExpr_bitblast_goCache_spec__1_spec__3_spec__7_spec__32___redArg(v_x_8381_, v_x_8382_);
    return v___x_8383_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__39(
    mut v_00_u03b2_8384_: *mut crate::leanh::LeanObject,
    mut v_a_8385_: *mut crate::leanh::LeanObject,
    mut v_x_8386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8387_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__16_spec__39___redArg(v_a_8385_, v_x_8386_);
    return v___x_8387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42(
    mut v_00_u03b2_8388_: *mut crate::leanh::LeanObject,
    mut v_a_8389_: *mut crate::leanh::LeanObject,
    mut v_x_8390_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8391_: u8 = 0;
    v___x_8391_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___redArg(v_a_8389_, v_x_8390_);
    return v___x_8391_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42___boxed(
    mut v_00_u03b2_8392_: *mut crate::leanh::LeanObject,
    mut v_a_8393_: *mut crate::leanh::LeanObject,
    mut v_x_8394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8395_: u8 = 0;
    let mut v_r_8396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8395_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__42(v_00_u03b2_8392_, v_a_8393_, v_x_8394_);
    v_r_8396_ = crate::leanh::lean_box((v_res_8395_) as usize);
    return v_r_8396_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43(
    mut v_00_u03b2_8397_: *mut crate::leanh::LeanObject,
    mut v_data_8398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43___redArg(v_data_8398_);
    return v___x_8399_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__44(
    mut v_00_u03b2_8400_: *mut crate::leanh::LeanObject,
    mut v_a_8401_: *mut crate::leanh::LeanObject,
    mut v_b_8402_: *mut crate::leanh::LeanObject,
    mut v_x_8403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8404_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__44___redArg(v_a_8401_, v_b_8402_, v_x_8403_);
    return v___x_8404_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74(
    mut v_aig1_8405_: *mut crate::leanh::LeanObject,
    mut v_aig2_8406_: *mut crate::leanh::LeanObject,
    mut v_val_8407_: *mut crate::leanh::LeanObject,
    mut v_h_8408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8409_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74___redArg(v_val_8407_);
    return v___x_8409_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74___boxed(
    mut v_aig1_8410_: *mut crate::leanh::LeanObject,
    mut v_aig2_8411_: *mut crate::leanh::LeanObject,
    mut v_val_8412_: *mut crate::leanh::LeanObject,
    mut v_h_8413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8414_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__11_spec__23_spec__31_spec__52_spec__74(v_aig1_8410_, v_aig2_8411_, v_val_8412_, v_h_8413_);
    crate::leanh::lean_dec_ref(v_aig2_8411_);
    crate::leanh::lean_dec_ref(v_aig1_8410_);
    return v_res_8414_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60(
    mut v_len_8415_: *mut crate::leanh::LeanObject,
    mut v_aig_8416_: *mut crate::leanh::LeanObject,
    mut v_idx_8417_: *mut crate::leanh::LeanObject,
    mut v_s_8418_: *mut crate::leanh::LeanObject,
    mut v_hidx_8419_: *mut crate::leanh::LeanObject,
    mut v_lhs_8420_: *mut crate::leanh::LeanObject,
    mut v_rhs_8421_: *mut crate::leanh::LeanObject,
    mut v_inst_8422_: *mut crate::leanh::LeanObject,
    mut v_inst_8423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8424_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___redArg(v_len_8415_, v_aig_8416_, v_idx_8417_, v_s_8418_, v_lhs_8420_, v_rhs_8421_);
    return v___x_8424_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60___boxed(
    mut v_len_8425_: *mut crate::leanh::LeanObject,
    mut v_aig_8426_: *mut crate::leanh::LeanObject,
    mut v_idx_8427_: *mut crate::leanh::LeanObject,
    mut v_s_8428_: *mut crate::leanh::LeanObject,
    mut v_hidx_8429_: *mut crate::leanh::LeanObject,
    mut v_lhs_8430_: *mut crate::leanh::LeanObject,
    mut v_rhs_8431_: *mut crate::leanh::LeanObject,
    mut v_inst_8432_: *mut crate::leanh::LeanObject,
    mut v_inst_8433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8434_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__39_spec__60(v_len_8425_, v_aig_8426_, v_idx_8427_, v_s_8428_, v_hidx_8429_, v_lhs_8430_, v_rhs_8431_, v_inst_8432_, v_inst_8433_);
    crate::leanh::lean_dec_ref(v_rhs_8431_);
    crate::leanh::lean_dec_ref(v_lhs_8430_);
    crate::leanh::lean_dec(v_len_8425_);
    return v_res_8434_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62(
    mut v_aig_8435_: *mut crate::leanh::LeanObject,
    mut v_acc_8436_: *mut crate::leanh::LeanObject,
    mut v_idx_8437_: *mut crate::leanh::LeanObject,
    mut v_len_8438_: *mut crate::leanh::LeanObject,
    mut v_input_8439_: *mut crate::leanh::LeanObject,
    mut v_inst_8440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8441_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___redArg(v_aig_8435_, v_acc_8436_, v_idx_8437_, v_len_8438_, v_input_8439_);
    return v___x_8441_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62___boxed(
    mut v_aig_8442_: *mut crate::leanh::LeanObject,
    mut v_acc_8443_: *mut crate::leanh::LeanObject,
    mut v_idx_8444_: *mut crate::leanh::LeanObject,
    mut v_len_8445_: *mut crate::leanh::LeanObject,
    mut v_input_8446_: *mut crate::leanh::LeanObject,
    mut v_inst_8447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8448_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__27_spec__40_spec__62(v_aig_8442_, v_acc_8443_, v_idx_8444_, v_len_8445_, v_input_8446_, v_inst_8447_);
    crate::leanh::lean_dec_ref(v_input_8446_);
    crate::leanh::lean_dec(v_len_8445_);
    return v_res_8448_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86(
    mut v_w_8449_: *mut crate::leanh::LeanObject,
    mut v_aig_8450_: *mut crate::leanh::LeanObject,
    mut v_input_8451_: *mut crate::leanh::LeanObject,
    mut v_distance_8452_: *mut crate::leanh::LeanObject,
    mut v_curr_8453_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8454_: *mut crate::leanh::LeanObject,
    mut v_s_8455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8456_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___redArg(v_w_8449_, v_aig_8450_, v_input_8451_, v_distance_8452_, v_curr_8453_, v_s_8455_);
    return v___x_8456_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86___boxed(
    mut v_w_8457_: *mut crate::leanh::LeanObject,
    mut v_aig_8458_: *mut crate::leanh::LeanObject,
    mut v_input_8459_: *mut crate::leanh::LeanObject,
    mut v_distance_8460_: *mut crate::leanh::LeanObject,
    mut v_curr_8461_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8462_: *mut crate::leanh::LeanObject,
    mut v_s_8463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8464_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__50_spec__67_spec__86(v_w_8457_, v_aig_8458_, v_input_8459_, v_distance_8460_, v_curr_8461_, v_hcurr_8462_, v_s_8463_);
    crate::leanh::lean_dec(v_distance_8460_);
    crate::leanh::lean_dec_ref(v_input_8459_);
    crate::leanh::lean_dec(v_w_8457_);
    return v_res_8464_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90(
    mut v_w_8465_: *mut crate::leanh::LeanObject,
    mut v_aig_8466_: *mut crate::leanh::LeanObject,
    mut v_input_8467_: *mut crate::leanh::LeanObject,
    mut v_distance_8468_: *mut crate::leanh::LeanObject,
    mut v_curr_8469_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8470_: *mut crate::leanh::LeanObject,
    mut v_s_8471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8472_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___redArg(v_w_8465_, v_aig_8466_, v_input_8467_, v_distance_8468_, v_curr_8469_, v_s_8471_);
    return v___x_8472_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90___boxed(
    mut v_w_8473_: *mut crate::leanh::LeanObject,
    mut v_aig_8474_: *mut crate::leanh::LeanObject,
    mut v_input_8475_: *mut crate::leanh::LeanObject,
    mut v_distance_8476_: *mut crate::leanh::LeanObject,
    mut v_curr_8477_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8478_: *mut crate::leanh::LeanObject,
    mut v_s_8479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8480_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__25_spec__53_spec__71_spec__90(v_w_8473_, v_aig_8474_, v_input_8475_, v_distance_8476_, v_curr_8477_, v_hcurr_8478_, v_s_8479_);
    crate::leanh::lean_dec(v_distance_8476_);
    crate::leanh::lean_dec_ref(v_input_8475_);
    crate::leanh::lean_dec(v_w_8473_);
    return v_res_8480_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68(
    mut v_00_u03b2_8481_: *mut crate::leanh::LeanObject,
    mut v_i_8482_: *mut crate::leanh::LeanObject,
    mut v_source_8483_: *mut crate::leanh::LeanObject,
    mut v_target_8484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68___redArg(v_i_8482_, v_source_8483_, v_target_8484_);
    return v___x_8485_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97(
    mut v_outWidth_8486_: *mut crate::leanh::LeanObject,
    mut v_aig_8487_: *mut crate::leanh::LeanObject,
    mut v_w_8488_: *mut crate::leanh::LeanObject,
    mut v_len_8489_: *mut crate::leanh::LeanObject,
    mut v_iterNum_8490_: *mut crate::leanh::LeanObject,
    mut v_oldLayer_8491_: *mut crate::leanh::LeanObject,
    mut v_newLayer_8492_: *mut crate::leanh::LeanObject,
    mut v_hold_8493_: *mut crate::leanh::LeanObject,
    mut v_hout_8494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8495_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___redArg(v_aig_8487_, v_w_8488_, v_len_8489_, v_iterNum_8490_, v_oldLayer_8491_, v_newLayer_8492_);
    return v___x_8495_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97___boxed(
    mut v_outWidth_8496_: *mut crate::leanh::LeanObject,
    mut v_aig_8497_: *mut crate::leanh::LeanObject,
    mut v_w_8498_: *mut crate::leanh::LeanObject,
    mut v_len_8499_: *mut crate::leanh::LeanObject,
    mut v_iterNum_8500_: *mut crate::leanh::LeanObject,
    mut v_oldLayer_8501_: *mut crate::leanh::LeanObject,
    mut v_newLayer_8502_: *mut crate::leanh::LeanObject,
    mut v_hold_8503_: *mut crate::leanh::LeanObject,
    mut v_hout_8504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8505_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__21_spec__45_spec__62_spec__82_spec__97(v_outWidth_8496_, v_aig_8497_, v_w_8498_, v_len_8499_, v_iterNum_8500_, v_oldLayer_8501_, v_newLayer_8502_, v_hold_8503_, v_hout_8504_);
    crate::leanh::lean_dec(v_len_8499_);
    crate::leanh::lean_dec(v_outWidth_8496_);
    return v_res_8505_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68_spec__83(
    mut v_00_u03b2_8506_: *mut crate::leanh::LeanObject,
    mut v_x_8507_: *mut crate::leanh::LeanObject,
    mut v_x_8508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__5_spec__12_spec__18_spec__43_spec__68_spec__83___redArg(v_x_8507_, v_x_8508_);
    return v___x_8509_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93(
    mut v_aig_8510_: *mut crate::leanh::LeanObject,
    mut v_w_8511_: *mut crate::leanh::LeanObject,
    mut v_input_8512_: *mut crate::leanh::LeanObject,
    mut v_newWidth_8513_: *mut crate::leanh::LeanObject,
    mut v_curr_8514_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8515_: *mut crate::leanh::LeanObject,
    mut v_s_8516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8517_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___redArg(v_aig_8510_, v_w_8511_, v_input_8512_, v_newWidth_8513_, v_curr_8514_, v_s_8516_);
    return v___x_8517_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93___boxed(
    mut v_aig_8518_: *mut crate::leanh::LeanObject,
    mut v_w_8519_: *mut crate::leanh::LeanObject,
    mut v_input_8520_: *mut crate::leanh::LeanObject,
    mut v_newWidth_8521_: *mut crate::leanh::LeanObject,
    mut v_curr_8522_: *mut crate::leanh::LeanObject,
    mut v_hcurr_8523_: *mut crate::leanh::LeanObject,
    mut v_s_8524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8525_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___00Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__13_spec__28_spec__42_spec__65_spec__85_spec__93(v_aig_8518_, v_w_8519_, v_input_8520_, v_newWidth_8521_, v_curr_8522_, v_hcurr_8523_, v_s_8524_);
    crate::leanh::lean_dec(v_newWidth_8521_);
    crate::leanh::lean_dec_ref(v_input_8520_);
    crate::leanh::lean_dec(v_w_8519_);
    return v_res_8525_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(
    mut v_x_8526_: *mut crate::leanh::LeanObject,
    mut v_h__1_8527_: *mut crate::leanh::LeanObject,
    mut v_h__2_8528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_8526_) == 0 {
        let mut v___x_8529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_8527_);
        v___x_8529_ = crate::leanh::lean_box(0);
        v___x_8530_ = crate::leanh::lean_apply_1(v_h__2_8528_, v___x_8529_);
        return v___x_8530_;
    } else {
        let mut v_val_8531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_8528_);
        v_val_8531_ = crate::leanh::lean_ctor_get(v_x_8526_, 0);
        crate::leanh::lean_inc(v_val_8531_);
        crate::leanh::lean_dec_ref_known(v_x_8526_, 1);
        v___x_8532_ = crate::leanh::lean_apply_1(v_h__1_8527_, v_val_8531_);
        return v___x_8532_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(
    mut v_w_8533_: *mut crate::leanh::LeanObject,
    mut v_aig_8534_: *mut crate::leanh::LeanObject,
    mut v_motive_8535_: *mut crate::leanh::LeanObject,
    mut v_x_8536_: *mut crate::leanh::LeanObject,
    mut v_h__1_8537_: *mut crate::leanh::LeanObject,
    mut v_h__2_8538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_8536_) == 0 {
        let mut v___x_8539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_8537_);
        v___x_8539_ = crate::leanh::lean_box(0);
        v___x_8540_ = crate::leanh::lean_apply_1(v_h__2_8538_, v___x_8539_);
        return v___x_8540_;
    } else {
        let mut v_val_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_8538_);
        v_val_8541_ = crate::leanh::lean_ctor_get(v_x_8536_, 0);
        crate::leanh::lean_inc(v_val_8541_);
        crate::leanh::lean_dec_ref_known(v_x_8536_, 1);
        v___x_8542_ = crate::leanh::lean_apply_1(v_h__1_8537_, v_val_8541_);
        return v___x_8542_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(
    mut v_w_8543_: *mut crate::leanh::LeanObject,
    mut v_aig_8544_: *mut crate::leanh::LeanObject,
    mut v_motive_8545_: *mut crate::leanh::LeanObject,
    mut v_x_8546_: *mut crate::leanh::LeanObject,
    mut v_h__1_8547_: *mut crate::leanh::LeanObject,
    mut v_h__2_8548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8549_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_8543_, v_aig_8544_, v_motive_8545_, v_x_8546_, v_h__1_8547_, v_h__2_8548_);
    crate::leanh::lean_dec_ref(v_aig_8544_);
    crate::leanh::lean_dec(v_w_8543_);
    return v_res_8549_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__1_splitter___redArg(
    mut v_x_8550_: *mut crate::leanh::LeanObject,
    mut v_h__1_8551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8552_ = crate::leanh::lean_ctor_get(v_x_8550_, 0);
    crate::leanh::lean_inc_ref(v_result_8552_);
    v_cache_8553_ = crate::leanh::lean_ctor_get(v_x_8550_, 1);
    crate::leanh::lean_inc_ref(v_cache_8553_);
    crate::leanh::lean_dec_ref(v_x_8550_);
    v___x_8554_ = crate::leanh::lean_apply_2(v_h__1_8551_, v_result_8552_, v_cache_8553_);
    return v___x_8554_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__1_splitter(
    mut v_w_8555_: *mut crate::leanh::LeanObject,
    mut v_aig_8556_: *mut crate::leanh::LeanObject,
    mut v_motive_8557_: *mut crate::leanh::LeanObject,
    mut v_x_8558_: *mut crate::leanh::LeanObject,
    mut v_h__1_8559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8560_ = crate::leanh::lean_ctor_get(v_x_8558_, 0);
    crate::leanh::lean_inc_ref(v_result_8560_);
    v_cache_8561_ = crate::leanh::lean_ctor_get(v_x_8558_, 1);
    crate::leanh::lean_inc_ref(v_cache_8561_);
    crate::leanh::lean_dec_ref(v_x_8558_);
    v___x_8562_ = crate::leanh::lean_apply_2(v_h__1_8559_, v_result_8560_, v_cache_8561_);
    return v___x_8562_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__1_splitter___boxed(
    mut v_w_8563_: *mut crate::leanh::LeanObject,
    mut v_aig_8564_: *mut crate::leanh::LeanObject,
    mut v_motive_8565_: *mut crate::leanh::LeanObject,
    mut v_x_8566_: *mut crate::leanh::LeanObject,
    mut v_h__1_8567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8568_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__1_splitter(v_w_8563_, v_aig_8564_, v_motive_8565_, v_x_8566_, v_h__1_8567_);
    crate::leanh::lean_dec_ref(v_aig_8564_);
    crate::leanh::lean_dec(v_w_8563_);
    return v_res_8568_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(
    mut v_w_8569_: *mut crate::leanh::LeanObject,
    mut v_expr_8570_: *mut crate::leanh::LeanObject,
    mut v_h__1_8571_: *mut crate::leanh::LeanObject,
    mut v_h__2_8572_: *mut crate::leanh::LeanObject,
    mut v_h__3_8573_: *mut crate::leanh::LeanObject,
    mut v_h__4_8574_: *mut crate::leanh::LeanObject,
    mut v_h__5_8575_: *mut crate::leanh::LeanObject,
    mut v_h__6_8576_: *mut crate::leanh::LeanObject,
    mut v_h__7_8577_: *mut crate::leanh::LeanObject,
    mut v_h__8_8578_: *mut crate::leanh::LeanObject,
    mut v_h__9_8579_: *mut crate::leanh::LeanObject,
    mut v_h__10_8580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_8570_) {
        0 => {
            let mut v_idx_8581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            v_idx_8581_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_idx_8581_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 2);
            v___x_8582_ = crate::leanh::lean_apply_2(v_h__1_8571_, v_w_8569_, v_idx_8581_);
            return v___x_8582_;
        }
        1 => {
            let mut v_val_8583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_val_8583_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_val_8583_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 2);
            v___x_8584_ = crate::leanh::lean_apply_2(v_h__2_8572_, v_w_8569_, v_val_8583_);
            return v___x_8584_;
        }
        2 => {
            let mut v_w_8585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_8586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_8587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_w_8585_ = crate::leanh::lean_ctor_get(v_expr_8570_, 0);
            crate::leanh::lean_inc(v_w_8585_);
            v_start_8586_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_start_8586_);
            v_expr_8587_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_expr_8587_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 4);
            v___x_8588_ = crate::leanh::lean_apply_4(
                v_h__7_8577_,
                v_w_8569_,
                v_w_8585_,
                v_start_8586_,
                v_expr_8587_,
            );
            return v___x_8588_;
        }
        3 => {
            let mut v_lhs_8589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_8590_: u8 = 0;
            let mut v_rhs_8591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_lhs_8589_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc_ref(v_lhs_8589_);
            v_op_8590_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_8570_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_8591_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc_ref(v_rhs_8591_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 3);
            v___x_8592_ = crate::leanh::lean_box((v_op_8590_) as usize);
            v___x_8593_ = crate::leanh::lean_apply_4(
                v_h__3_8573_,
                v_w_8569_,
                v_lhs_8589_,
                v___x_8592_,
                v_rhs_8591_,
            );
            return v___x_8593_;
        }
        4 => {
            let mut v_op_8594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_8595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_op_8594_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_op_8594_);
            v_operand_8595_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc_ref(v_operand_8595_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 3);
            v___x_8596_ =
                crate::leanh::lean_apply_3(v_h__4_8574_, v_w_8569_, v_op_8594_, v_operand_8595_);
            return v___x_8596_;
        }
        5 => {
            let mut v_l_8597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_8598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_l_8597_ = crate::leanh::lean_ctor_get(v_expr_8570_, 0);
            crate::leanh::lean_inc(v_l_8597_);
            v_r_8598_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_r_8598_);
            v_lhs_8599_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_lhs_8599_);
            v_rhs_8600_ = crate::leanh::lean_ctor_get(v_expr_8570_, 4);
            crate::leanh::lean_inc_ref(v_rhs_8600_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 5);
            v___x_8601_ = crate::leanh::lean_apply_6(
                v_h__5_8575_,
                v_w_8569_,
                v_l_8597_,
                v_r_8598_,
                v_lhs_8599_,
                v_rhs_8600_,
                crate::leanh::lean_box(0),
            );
            return v___x_8601_;
        }
        6 => {
            let mut v_w_8602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_8603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_8604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_w_8602_ = crate::leanh::lean_ctor_get(v_expr_8570_, 0);
            crate::leanh::lean_inc(v_w_8602_);
            v_n_8603_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc(v_n_8603_);
            v_expr_8604_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_expr_8604_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 4);
            v___x_8605_ = crate::leanh::lean_apply_5(
                v_h__6_8576_,
                v_w_8569_,
                v_w_8602_,
                v_n_8603_,
                v_expr_8604_,
                crate::leanh::lean_box(0),
            );
            return v___x_8605_;
        }
        7 => {
            let mut v_n_8606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_n_8606_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_n_8606_);
            v_lhs_8607_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8607_);
            v_rhs_8608_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8608_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 4);
            v___x_8609_ = crate::leanh::lean_apply_4(
                v_h__8_8578_,
                v_w_8569_,
                v_n_8606_,
                v_lhs_8607_,
                v_rhs_8608_,
            );
            return v___x_8609_;
        }
        8 => {
            let mut v_n_8610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8580_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_n_8610_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_n_8610_);
            v_lhs_8611_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8611_);
            v_rhs_8612_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8612_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 4);
            v___x_8613_ = crate::leanh::lean_apply_4(
                v_h__9_8579_,
                v_w_8569_,
                v_n_8610_,
                v_lhs_8611_,
                v_rhs_8612_,
            );
            return v___x_8613_;
        }
        _ => {
            let mut v_n_8614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_8579_);
            crate::leanh::lean_dec(v_h__8_8578_);
            crate::leanh::lean_dec(v_h__7_8577_);
            crate::leanh::lean_dec(v_h__6_8576_);
            crate::leanh::lean_dec(v_h__5_8575_);
            crate::leanh::lean_dec(v_h__4_8574_);
            crate::leanh::lean_dec(v_h__3_8573_);
            crate::leanh::lean_dec(v_h__2_8572_);
            crate::leanh::lean_dec(v_h__1_8571_);
            v_n_8614_ = crate::leanh::lean_ctor_get(v_expr_8570_, 1);
            crate::leanh::lean_inc(v_n_8614_);
            v_lhs_8615_ = crate::leanh::lean_ctor_get(v_expr_8570_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8615_);
            v_rhs_8616_ = crate::leanh::lean_ctor_get(v_expr_8570_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8616_);
            crate::leanh::lean_dec_ref_known(v_expr_8570_, 4);
            v___x_8617_ = crate::leanh::lean_apply_4(
                v_h__10_8580_,
                v_w_8569_,
                v_n_8614_,
                v_lhs_8615_,
                v_rhs_8616_,
            );
            return v___x_8617_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(
    mut v_motive_8618_: *mut crate::leanh::LeanObject,
    mut v_w_8619_: *mut crate::leanh::LeanObject,
    mut v_expr_8620_: *mut crate::leanh::LeanObject,
    mut v_h__1_8621_: *mut crate::leanh::LeanObject,
    mut v_h__2_8622_: *mut crate::leanh::LeanObject,
    mut v_h__3_8623_: *mut crate::leanh::LeanObject,
    mut v_h__4_8624_: *mut crate::leanh::LeanObject,
    mut v_h__5_8625_: *mut crate::leanh::LeanObject,
    mut v_h__6_8626_: *mut crate::leanh::LeanObject,
    mut v_h__7_8627_: *mut crate::leanh::LeanObject,
    mut v_h__8_8628_: *mut crate::leanh::LeanObject,
    mut v_h__9_8629_: *mut crate::leanh::LeanObject,
    mut v_h__10_8630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_8620_) {
        0 => {
            let mut v_idx_8631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            v_idx_8631_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_idx_8631_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 2);
            v___x_8632_ = crate::leanh::lean_apply_2(v_h__1_8621_, v_w_8619_, v_idx_8631_);
            return v___x_8632_;
        }
        1 => {
            let mut v_val_8633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_val_8633_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_val_8633_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 2);
            v___x_8634_ = crate::leanh::lean_apply_2(v_h__2_8622_, v_w_8619_, v_val_8633_);
            return v___x_8634_;
        }
        2 => {
            let mut v_w_8635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_8636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_8637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_w_8635_ = crate::leanh::lean_ctor_get(v_expr_8620_, 0);
            crate::leanh::lean_inc(v_w_8635_);
            v_start_8636_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_start_8636_);
            v_expr_8637_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_expr_8637_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 4);
            v___x_8638_ = crate::leanh::lean_apply_4(
                v_h__7_8627_,
                v_w_8619_,
                v_w_8635_,
                v_start_8636_,
                v_expr_8637_,
            );
            return v___x_8638_;
        }
        3 => {
            let mut v_lhs_8639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_8640_: u8 = 0;
            let mut v_rhs_8641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_lhs_8639_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc_ref(v_lhs_8639_);
            v_op_8640_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_8620_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_8641_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc_ref(v_rhs_8641_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 3);
            v___x_8642_ = crate::leanh::lean_box((v_op_8640_) as usize);
            v___x_8643_ = crate::leanh::lean_apply_4(
                v_h__3_8623_,
                v_w_8619_,
                v_lhs_8639_,
                v___x_8642_,
                v_rhs_8641_,
            );
            return v___x_8643_;
        }
        4 => {
            let mut v_op_8644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_8645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_op_8644_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_op_8644_);
            v_operand_8645_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc_ref(v_operand_8645_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 3);
            v___x_8646_ =
                crate::leanh::lean_apply_3(v_h__4_8624_, v_w_8619_, v_op_8644_, v_operand_8645_);
            return v___x_8646_;
        }
        5 => {
            let mut v_l_8647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_8648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_l_8647_ = crate::leanh::lean_ctor_get(v_expr_8620_, 0);
            crate::leanh::lean_inc(v_l_8647_);
            v_r_8648_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_r_8648_);
            v_lhs_8649_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_lhs_8649_);
            v_rhs_8650_ = crate::leanh::lean_ctor_get(v_expr_8620_, 4);
            crate::leanh::lean_inc_ref(v_rhs_8650_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 5);
            v___x_8651_ = crate::leanh::lean_apply_6(
                v_h__5_8625_,
                v_w_8619_,
                v_l_8647_,
                v_r_8648_,
                v_lhs_8649_,
                v_rhs_8650_,
                crate::leanh::lean_box(0),
            );
            return v___x_8651_;
        }
        6 => {
            let mut v_w_8652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_8653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_8654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_w_8652_ = crate::leanh::lean_ctor_get(v_expr_8620_, 0);
            crate::leanh::lean_inc(v_w_8652_);
            v_n_8653_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc(v_n_8653_);
            v_expr_8654_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_expr_8654_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 4);
            v___x_8655_ = crate::leanh::lean_apply_5(
                v_h__6_8626_,
                v_w_8619_,
                v_w_8652_,
                v_n_8653_,
                v_expr_8654_,
                crate::leanh::lean_box(0),
            );
            return v___x_8655_;
        }
        7 => {
            let mut v_n_8656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_n_8656_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_n_8656_);
            v_lhs_8657_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8657_);
            v_rhs_8658_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8658_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 4);
            v___x_8659_ = crate::leanh::lean_apply_4(
                v_h__8_8628_,
                v_w_8619_,
                v_n_8656_,
                v_lhs_8657_,
                v_rhs_8658_,
            );
            return v___x_8659_;
        }
        8 => {
            let mut v_n_8660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_8630_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_n_8660_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_n_8660_);
            v_lhs_8661_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8661_);
            v_rhs_8662_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8662_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 4);
            v___x_8663_ = crate::leanh::lean_apply_4(
                v_h__9_8629_,
                v_w_8619_,
                v_n_8660_,
                v_lhs_8661_,
                v_rhs_8662_,
            );
            return v___x_8663_;
        }
        _ => {
            let mut v_n_8664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_8665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_8666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_8629_);
            crate::leanh::lean_dec(v_h__8_8628_);
            crate::leanh::lean_dec(v_h__7_8627_);
            crate::leanh::lean_dec(v_h__6_8626_);
            crate::leanh::lean_dec(v_h__5_8625_);
            crate::leanh::lean_dec(v_h__4_8624_);
            crate::leanh::lean_dec(v_h__3_8623_);
            crate::leanh::lean_dec(v_h__2_8622_);
            crate::leanh::lean_dec(v_h__1_8621_);
            v_n_8664_ = crate::leanh::lean_ctor_get(v_expr_8620_, 1);
            crate::leanh::lean_inc(v_n_8664_);
            v_lhs_8665_ = crate::leanh::lean_ctor_get(v_expr_8620_, 2);
            crate::leanh::lean_inc_ref(v_lhs_8665_);
            v_rhs_8666_ = crate::leanh::lean_ctor_get(v_expr_8620_, 3);
            crate::leanh::lean_inc_ref(v_rhs_8666_);
            crate::leanh::lean_dec_ref_known(v_expr_8620_, 4);
            v___x_8667_ = crate::leanh::lean_apply_4(
                v_h__10_8630_,
                v_w_8619_,
                v_n_8664_,
                v_lhs_8665_,
                v_rhs_8666_,
            );
            return v___x_8667_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__13_splitter___redArg(
    mut v_x_8668_: *mut crate::leanh::LeanObject,
    mut v_h__1_8669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_8672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_8673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8670_ = crate::leanh::lean_ctor_get(v_x_8668_, 0);
    crate::leanh::lean_inc_ref(v_result_8670_);
    v_cache_8671_ = crate::leanh::lean_ctor_get(v_x_8668_, 1);
    crate::leanh::lean_inc_ref(v_cache_8671_);
    crate::leanh::lean_dec_ref(v_x_8668_);
    v_aig_8672_ = crate::leanh::lean_ctor_get(v_result_8670_, 0);
    crate::leanh::lean_inc_ref(v_aig_8672_);
    v_vec_8673_ = crate::leanh::lean_ctor_get(v_result_8670_, 1);
    crate::leanh::lean_inc_ref(v_vec_8673_);
    crate::leanh::lean_dec_ref(v_result_8670_);
    v___x_8674_ = crate::leanh::lean_apply_4(
        v_h__1_8669_,
        v_aig_8672_,
        v_vec_8673_,
        crate::leanh::lean_box(0),
        v_cache_8671_,
    );
    return v___x_8674_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__13_splitter(
    mut v_aig_8675_: *mut crate::leanh::LeanObject,
    mut v_w_8676_: *mut crate::leanh::LeanObject,
    mut v_motive_8677_: *mut crate::leanh::LeanObject,
    mut v_x_8678_: *mut crate::leanh::LeanObject,
    mut v_h__1_8679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_8682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_8683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8680_ = crate::leanh::lean_ctor_get(v_x_8678_, 0);
    crate::leanh::lean_inc_ref(v_result_8680_);
    v_cache_8681_ = crate::leanh::lean_ctor_get(v_x_8678_, 1);
    crate::leanh::lean_inc_ref(v_cache_8681_);
    crate::leanh::lean_dec_ref(v_x_8678_);
    v_aig_8682_ = crate::leanh::lean_ctor_get(v_result_8680_, 0);
    crate::leanh::lean_inc_ref(v_aig_8682_);
    v_vec_8683_ = crate::leanh::lean_ctor_get(v_result_8680_, 1);
    crate::leanh::lean_inc_ref(v_vec_8683_);
    crate::leanh::lean_dec_ref(v_result_8680_);
    v___x_8684_ = crate::leanh::lean_apply_4(
        v_h__1_8679_,
        v_aig_8682_,
        v_vec_8683_,
        crate::leanh::lean_box(0),
        v_cache_8681_,
    );
    return v___x_8684_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__13_splitter___boxed(
    mut v_aig_8685_: *mut crate::leanh::LeanObject,
    mut v_w_8686_: *mut crate::leanh::LeanObject,
    mut v_motive_8687_: *mut crate::leanh::LeanObject,
    mut v_x_8688_: *mut crate::leanh::LeanObject,
    mut v_h__1_8689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8690_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__13_splitter(v_aig_8685_, v_w_8686_, v_motive_8687_, v_x_8688_, v_h__1_8689_);
    crate::leanh::lean_dec(v_w_8686_);
    crate::leanh::lean_dec_ref(v_aig_8685_);
    return v_res_8690_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__11_splitter___redArg(
    mut v_x_8691_: *mut crate::leanh::LeanObject,
    mut v_h__1_8692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_8695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_8696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8693_ = crate::leanh::lean_ctor_get(v_x_8691_, 0);
    crate::leanh::lean_inc_ref(v_result_8693_);
    v_cache_8694_ = crate::leanh::lean_ctor_get(v_x_8691_, 1);
    crate::leanh::lean_inc_ref(v_cache_8694_);
    crate::leanh::lean_dec_ref(v_x_8691_);
    v_aig_8695_ = crate::leanh::lean_ctor_get(v_result_8693_, 0);
    crate::leanh::lean_inc_ref(v_aig_8695_);
    v_vec_8696_ = crate::leanh::lean_ctor_get(v_result_8693_, 1);
    crate::leanh::lean_inc_ref(v_vec_8696_);
    crate::leanh::lean_dec_ref(v_result_8693_);
    v___x_8697_ = crate::leanh::lean_apply_4(
        v_h__1_8692_,
        v_aig_8695_,
        v_vec_8696_,
        crate::leanh::lean_box(0),
        v_cache_8694_,
    );
    return v___x_8697_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__11_splitter(
    mut v_w_8698_: *mut crate::leanh::LeanObject,
    mut v_aig_8699_: *mut crate::leanh::LeanObject,
    mut v_motive_8700_: *mut crate::leanh::LeanObject,
    mut v_x_8701_: *mut crate::leanh::LeanObject,
    mut v_h__1_8702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_8703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_8705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_8706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_8703_ = crate::leanh::lean_ctor_get(v_x_8701_, 0);
    crate::leanh::lean_inc_ref(v_result_8703_);
    v_cache_8704_ = crate::leanh::lean_ctor_get(v_x_8701_, 1);
    crate::leanh::lean_inc_ref(v_cache_8704_);
    crate::leanh::lean_dec_ref(v_x_8701_);
    v_aig_8705_ = crate::leanh::lean_ctor_get(v_result_8703_, 0);
    crate::leanh::lean_inc_ref(v_aig_8705_);
    v_vec_8706_ = crate::leanh::lean_ctor_get(v_result_8703_, 1);
    crate::leanh::lean_inc_ref(v_vec_8706_);
    crate::leanh::lean_dec_ref(v_result_8703_);
    v___x_8707_ = crate::leanh::lean_apply_4(
        v_h__1_8702_,
        v_aig_8705_,
        v_vec_8706_,
        crate::leanh::lean_box(0),
        v_cache_8704_,
    );
    return v___x_8707_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__11_splitter___boxed(
    mut v_w_8708_: *mut crate::leanh::LeanObject,
    mut v_aig_8709_: *mut crate::leanh::LeanObject,
    mut v_motive_8710_: *mut crate::leanh::LeanObject,
    mut v_x_8711_: *mut crate::leanh::LeanObject,
    mut v_h__1_8712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8713_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__11_splitter(v_w_8708_, v_aig_8709_, v_motive_8710_, v_x_8711_, v_h__1_8712_);
    crate::leanh::lean_dec_ref(v_aig_8709_);
    crate::leanh::lean_dec(v_w_8708_);
    return v_res_8713_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(
    mut v_op_8714_: u8,
    mut v_h__1_8715_: *mut crate::leanh::LeanObject,
    mut v_h__2_8716_: *mut crate::leanh::LeanObject,
    mut v_h__3_8717_: *mut crate::leanh::LeanObject,
    mut v_h__4_8718_: *mut crate::leanh::LeanObject,
    mut v_h__5_8719_: *mut crate::leanh::LeanObject,
    mut v_h__6_8720_: *mut crate::leanh::LeanObject,
    mut v_h__7_8721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_op_8714_ {
        0 => {
            let mut v___x_8722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__2_8716_);
            v___x_8722_ = crate::leanh::lean_box(0);
            v___x_8723_ = crate::leanh::lean_apply_1(v_h__1_8715_, v___x_8722_);
            return v___x_8723_;
        }
        1 => {
            let mut v___x_8724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8724_ = crate::leanh::lean_box(0);
            v___x_8725_ = crate::leanh::lean_apply_1(v_h__2_8716_, v___x_8724_);
            return v___x_8725_;
        }
        2 => {
            let mut v___x_8726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__2_8716_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8726_ = crate::leanh::lean_box(0);
            v___x_8727_ = crate::leanh::lean_apply_1(v_h__3_8717_, v___x_8726_);
            return v___x_8727_;
        }
        3 => {
            let mut v___x_8728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__2_8716_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8728_ = crate::leanh::lean_box(0);
            v___x_8729_ = crate::leanh::lean_apply_1(v_h__4_8718_, v___x_8728_);
            return v___x_8729_;
        }
        4 => {
            let mut v___x_8730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__2_8716_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8730_ = crate::leanh::lean_box(0);
            v___x_8731_ = crate::leanh::lean_apply_1(v_h__5_8719_, v___x_8730_);
            return v___x_8731_;
        }
        5 => {
            let mut v___x_8732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8721_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__2_8716_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8732_ = crate::leanh::lean_box(0);
            v___x_8733_ = crate::leanh::lean_apply_1(v_h__6_8720_, v___x_8732_);
            return v___x_8733_;
        }
        _ => {
            let mut v___x_8734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_8720_);
            crate::leanh::lean_dec(v_h__5_8719_);
            crate::leanh::lean_dec(v_h__4_8718_);
            crate::leanh::lean_dec(v_h__3_8717_);
            crate::leanh::lean_dec(v_h__2_8716_);
            crate::leanh::lean_dec(v_h__1_8715_);
            v___x_8734_ = crate::leanh::lean_box(0);
            v___x_8735_ = crate::leanh::lean_apply_1(v_h__7_8721_, v___x_8734_);
            return v___x_8735_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(
    mut v_op_8736_: *mut crate::leanh::LeanObject,
    mut v_h__1_8737_: *mut crate::leanh::LeanObject,
    mut v_h__2_8738_: *mut crate::leanh::LeanObject,
    mut v_h__3_8739_: *mut crate::leanh::LeanObject,
    mut v_h__4_8740_: *mut crate::leanh::LeanObject,
    mut v_h__5_8741_: *mut crate::leanh::LeanObject,
    mut v_h__6_8742_: *mut crate::leanh::LeanObject,
    mut v_h__7_8743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_76__boxed_8744_: u8 = 0;
    let mut v_res_8745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_76__boxed_8744_ = (crate::leanh::lean_unbox(v_op_8736_) as u8);
    v_res_8745_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_76__boxed_8744_, v_h__1_8737_, v_h__2_8738_, v_h__3_8739_, v_h__4_8740_, v_h__5_8741_, v_h__6_8742_, v_h__7_8743_);
    return v_res_8745_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(
    mut v_motive_8746_: *mut crate::leanh::LeanObject,
    mut v_op_8747_: u8,
    mut v_h__1_8748_: *mut crate::leanh::LeanObject,
    mut v_h__2_8749_: *mut crate::leanh::LeanObject,
    mut v_h__3_8750_: *mut crate::leanh::LeanObject,
    mut v_h__4_8751_: *mut crate::leanh::LeanObject,
    mut v_h__5_8752_: *mut crate::leanh::LeanObject,
    mut v_h__6_8753_: *mut crate::leanh::LeanObject,
    mut v_h__7_8754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_op_8747_ {
        0 => {
            let mut v___x_8755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__2_8749_);
            v___x_8755_ = crate::leanh::lean_box(0);
            v___x_8756_ = crate::leanh::lean_apply_1(v_h__1_8748_, v___x_8755_);
            return v___x_8756_;
        }
        1 => {
            let mut v___x_8757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8757_ = crate::leanh::lean_box(0);
            v___x_8758_ = crate::leanh::lean_apply_1(v_h__2_8749_, v___x_8757_);
            return v___x_8758_;
        }
        2 => {
            let mut v___x_8759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__2_8749_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8759_ = crate::leanh::lean_box(0);
            v___x_8760_ = crate::leanh::lean_apply_1(v_h__3_8750_, v___x_8759_);
            return v___x_8760_;
        }
        3 => {
            let mut v___x_8761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__2_8749_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8761_ = crate::leanh::lean_box(0);
            v___x_8762_ = crate::leanh::lean_apply_1(v_h__4_8751_, v___x_8761_);
            return v___x_8762_;
        }
        4 => {
            let mut v___x_8763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__2_8749_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8763_ = crate::leanh::lean_box(0);
            v___x_8764_ = crate::leanh::lean_apply_1(v_h__5_8752_, v___x_8763_);
            return v___x_8764_;
        }
        5 => {
            let mut v___x_8765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8754_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__2_8749_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8765_ = crate::leanh::lean_box(0);
            v___x_8766_ = crate::leanh::lean_apply_1(v_h__6_8753_, v___x_8765_);
            return v___x_8766_;
        }
        _ => {
            let mut v___x_8767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_8753_);
            crate::leanh::lean_dec(v_h__5_8752_);
            crate::leanh::lean_dec(v_h__4_8751_);
            crate::leanh::lean_dec(v_h__3_8750_);
            crate::leanh::lean_dec(v_h__2_8749_);
            crate::leanh::lean_dec(v_h__1_8748_);
            v___x_8767_ = crate::leanh::lean_box(0);
            v___x_8768_ = crate::leanh::lean_apply_1(v_h__7_8754_, v___x_8767_);
            return v___x_8768_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(
    mut v_motive_8769_: *mut crate::leanh::LeanObject,
    mut v_op_8770_: *mut crate::leanh::LeanObject,
    mut v_h__1_8771_: *mut crate::leanh::LeanObject,
    mut v_h__2_8772_: *mut crate::leanh::LeanObject,
    mut v_h__3_8773_: *mut crate::leanh::LeanObject,
    mut v_h__4_8774_: *mut crate::leanh::LeanObject,
    mut v_h__5_8775_: *mut crate::leanh::LeanObject,
    mut v_h__6_8776_: *mut crate::leanh::LeanObject,
    mut v_h__7_8777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_107__boxed_8778_: u8 = 0;
    let mut v_res_8779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_107__boxed_8778_ = (crate::leanh::lean_unbox(v_op_8770_) as u8);
    v_res_8779_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_8769_, v_op_107__boxed_8778_, v_h__1_8771_, v_h__2_8772_, v_h__3_8773_, v_h__4_8774_, v_h__5_8775_, v_h__6_8776_, v_h__7_8777_);
    return v_res_8779_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(
    mut v_op_8780_: *mut crate::leanh::LeanObject,
    mut v_h__1_8781_: *mut crate::leanh::LeanObject,
    mut v_h__2_8782_: *mut crate::leanh::LeanObject,
    mut v_h__3_8783_: *mut crate::leanh::LeanObject,
    mut v_h__4_8784_: *mut crate::leanh::LeanObject,
    mut v_h__5_8785_: *mut crate::leanh::LeanObject,
    mut v_h__6_8786_: *mut crate::leanh::LeanObject,
    mut v_h__7_8787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_op_8780_) {
        0 => {
            let mut v___x_8788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__2_8782_);
            v___x_8788_ = crate::leanh::lean_box(0);
            v___x_8789_ = crate::leanh::lean_apply_1(v_h__1_8781_, v___x_8788_);
            return v___x_8789_;
        }
        1 => {
            let mut v_n_8790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v_n_8790_ = crate::leanh::lean_ctor_get(v_op_8780_, 0);
            crate::leanh::lean_inc(v_n_8790_);
            crate::leanh::lean_dec_ref_known(v_op_8780_, 1);
            v___x_8791_ = crate::leanh::lean_apply_1(v_h__2_8782_, v_n_8790_);
            return v___x_8791_;
        }
        2 => {
            let mut v_n_8792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__2_8782_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v_n_8792_ = crate::leanh::lean_ctor_get(v_op_8780_, 0);
            crate::leanh::lean_inc(v_n_8792_);
            crate::leanh::lean_dec_ref_known(v_op_8780_, 1);
            v___x_8793_ = crate::leanh::lean_apply_1(v_h__3_8783_, v_n_8792_);
            return v___x_8793_;
        }
        3 => {
            let mut v_n_8794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__2_8782_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v_n_8794_ = crate::leanh::lean_ctor_get(v_op_8780_, 0);
            crate::leanh::lean_inc(v_n_8794_);
            crate::leanh::lean_dec_ref_known(v_op_8780_, 1);
            v___x_8795_ = crate::leanh::lean_apply_1(v_h__4_8784_, v_n_8794_);
            return v___x_8795_;
        }
        4 => {
            let mut v___x_8796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__2_8782_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v___x_8796_ = crate::leanh::lean_box(0);
            v___x_8797_ = crate::leanh::lean_apply_1(v_h__5_8785_, v___x_8796_);
            return v___x_8797_;
        }
        5 => {
            let mut v___x_8798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8787_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__2_8782_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v___x_8798_ = crate::leanh::lean_box(0);
            v___x_8799_ = crate::leanh::lean_apply_1(v_h__6_8786_, v___x_8798_);
            return v___x_8799_;
        }
        _ => {
            let mut v___x_8800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_8786_);
            crate::leanh::lean_dec(v_h__5_8785_);
            crate::leanh::lean_dec(v_h__4_8784_);
            crate::leanh::lean_dec(v_h__3_8783_);
            crate::leanh::lean_dec(v_h__2_8782_);
            crate::leanh::lean_dec(v_h__1_8781_);
            v___x_8800_ = crate::leanh::lean_box(0);
            v___x_8801_ = crate::leanh::lean_apply_1(v_h__7_8787_, v___x_8800_);
            return v___x_8801_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(
    mut v_motive_8802_: *mut crate::leanh::LeanObject,
    mut v_op_8803_: *mut crate::leanh::LeanObject,
    mut v_h__1_8804_: *mut crate::leanh::LeanObject,
    mut v_h__2_8805_: *mut crate::leanh::LeanObject,
    mut v_h__3_8806_: *mut crate::leanh::LeanObject,
    mut v_h__4_8807_: *mut crate::leanh::LeanObject,
    mut v_h__5_8808_: *mut crate::leanh::LeanObject,
    mut v_h__6_8809_: *mut crate::leanh::LeanObject,
    mut v_h__7_8810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_op_8803_) {
        0 => {
            let mut v___x_8811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__2_8805_);
            v___x_8811_ = crate::leanh::lean_box(0);
            v___x_8812_ = crate::leanh::lean_apply_1(v_h__1_8804_, v___x_8811_);
            return v___x_8812_;
        }
        1 => {
            let mut v_n_8813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v_n_8813_ = crate::leanh::lean_ctor_get(v_op_8803_, 0);
            crate::leanh::lean_inc(v_n_8813_);
            crate::leanh::lean_dec_ref_known(v_op_8803_, 1);
            v___x_8814_ = crate::leanh::lean_apply_1(v_h__2_8805_, v_n_8813_);
            return v___x_8814_;
        }
        2 => {
            let mut v_n_8815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__2_8805_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v_n_8815_ = crate::leanh::lean_ctor_get(v_op_8803_, 0);
            crate::leanh::lean_inc(v_n_8815_);
            crate::leanh::lean_dec_ref_known(v_op_8803_, 1);
            v___x_8816_ = crate::leanh::lean_apply_1(v_h__3_8806_, v_n_8815_);
            return v___x_8816_;
        }
        3 => {
            let mut v_n_8817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__2_8805_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v_n_8817_ = crate::leanh::lean_ctor_get(v_op_8803_, 0);
            crate::leanh::lean_inc(v_n_8817_);
            crate::leanh::lean_dec_ref_known(v_op_8803_, 1);
            v___x_8818_ = crate::leanh::lean_apply_1(v_h__4_8807_, v_n_8817_);
            return v___x_8818_;
        }
        4 => {
            let mut v___x_8819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__2_8805_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v___x_8819_ = crate::leanh::lean_box(0);
            v___x_8820_ = crate::leanh::lean_apply_1(v_h__5_8808_, v___x_8819_);
            return v___x_8820_;
        }
        5 => {
            let mut v___x_8821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_8810_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__2_8805_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v___x_8821_ = crate::leanh::lean_box(0);
            v___x_8822_ = crate::leanh::lean_apply_1(v_h__6_8809_, v___x_8821_);
            return v___x_8822_;
        }
        _ => {
            let mut v___x_8823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_8809_);
            crate::leanh::lean_dec(v_h__5_8808_);
            crate::leanh::lean_dec(v_h__4_8807_);
            crate::leanh::lean_dec(v_h__3_8806_);
            crate::leanh::lean_dec(v_h__2_8805_);
            crate::leanh::lean_dec(v_h__1_8804_);
            v___x_8823_ = crate::leanh::lean_box(0);
            v___x_8824_ = crate::leanh::lean_apply_1(v_h__7_8810_, v___x_8823_);
            return v___x_8824_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast(
    mut v_w_8825_: *mut crate::leanh::LeanObject,
    mut v_aig_8826_: *mut crate::leanh::LeanObject,
    mut v_input_8827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_8828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_8828_ = crate::leanh::lean_ctor_get(v_input_8827_, 0);
    crate::leanh::lean_inc(v_val_8828_);
    v_cache_8829_ = crate::leanh::lean_ctor_get(v_input_8827_, 1);
    crate::leanh::lean_inc_ref(v_cache_8829_);
    crate::leanh::lean_dec_ref(v_input_8827_);
    v___x_8830_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_goCache(
        v_w_8825_,
        v_aig_8826_,
        v_val_8828_,
        v_cache_8829_,
    );
    return v___x_8830_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(
            builtin,
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
}
