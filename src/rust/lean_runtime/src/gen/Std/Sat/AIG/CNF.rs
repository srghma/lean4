// Lean compiler output
// Module: Std.Sat.AIG.CNF
// Imports: Std.Sat.CNF Std.Sat.AIG.Lemmas Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::l_Std_Sat_AIG_denote_go___redArg;
use crate::r#gen::Std::Sat::AIG::Lemmas::{
    initialize_Std_Sat_AIG_Lemmas, runtime_initialize_Std_Sat_AIG_Lemmas,
};
use crate::r#gen::Std::Sat::CNF::Basic::l_Std_Sat_CNF_eval___redArg;
use crate::r#gen::Std::Sat::CNF::{initialize_Std_Sat_CNF, runtime_initialize_Std_Sat_CNF};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_mul, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(
    mut v_output_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = 0;
    v___x_584_ = lean_box((v___x_583_) as usize);
    v___x_585_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_585_, 0, v_output_582_);
    lean_ctor_set(v___x_585_, 1, v___x_584_);
    v___x_586_ = lean_box(0);
    v___x_587_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_587_, 0, v___x_585_);
    lean_ctor_set(v___x_587_, 1, v___x_586_);
    v___x_588_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0;
    v___x_589_ = lean_array_push(v___x_588_, v___x_587_);
    return v___x_589_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(
    mut v_00_u03b1_590_: *mut LeanObject,
    mut v_output_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_output_591_);
    return v___x_592_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(
    mut v_output_593_: *mut LeanObject,
    mut v_atom_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: u8 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = 0;
    v___x_596_ = lean_box((v___x_595_) as usize);
    lean_inc(v_output_593_);
    v___x_597_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_597_, 0, v_output_593_);
    lean_ctor_set(v___x_597_, 1, v___x_596_);
    v___x_598_ = 1;
    v___x_599_ = lean_box((v___x_598_) as usize);
    lean_inc(v_atom_594_);
    v___x_600_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_600_, 0, v_atom_594_);
    lean_ctor_set(v___x_600_, 1, v___x_599_);
    v___x_601_ = lean_box(0);
    v___x_602_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_602_, 0, v___x_600_);
    lean_ctor_set(v___x_602_, 1, v___x_601_);
    v___x_603_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_603_, 0, v___x_597_);
    lean_ctor_set(v___x_603_, 1, v___x_602_);
    v___x_604_ = lean_box((v___x_598_) as usize);
    v___x_605_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_605_, 0, v_output_593_);
    lean_ctor_set(v___x_605_, 1, v___x_604_);
    v___x_606_ = lean_box((v___x_595_) as usize);
    v___x_607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_607_, 0, v_atom_594_);
    lean_ctor_set(v___x_607_, 1, v___x_606_);
    v___x_608_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_608_, 0, v___x_607_);
    lean_ctor_set(v___x_608_, 1, v___x_601_);
    v___x_609_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_609_, 0, v___x_605_);
    lean_ctor_set(v___x_609_, 1, v___x_608_);
    v___x_610_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0;
    v___x_611_ = lean_array_push(v___x_610_, v___x_609_);
    v___x_612_ = lean_array_push(v___x_611_, v___x_603_);
    return v___x_612_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(
    mut v_00_u03b1_613_: *mut LeanObject,
    mut v_output_614_: *mut LeanObject,
    mut v_atom_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_616_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(
        v_output_614_,
        v_atom_615_,
    );
    return v___x_616_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(
    mut v_output_617_: *mut LeanObject,
    mut v_lhs_618_: *mut LeanObject,
    mut v_rhs_619_: *mut LeanObject,
    mut v_linv_620_: u8,
    mut v_rinv_621_: u8,
) -> *mut LeanObject {
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: u8 = 0;
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_638_: u8 = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_622_ = 1;
                v___x_623_ = lean_box((v___x_622_) as usize);
                lean_inc(v_output_617_);
                v___x_624_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_624_, 0, v_output_617_);
                lean_ctor_set(v___x_624_, 1, v___x_623_);
                v___x_625_ = lean_box((v_linv_620_) as usize);
                lean_inc(v_lhs_618_);
                v___x_626_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_626_, 0, v_lhs_618_);
                lean_ctor_set(v___x_626_, 1, v___x_625_);
                v___x_627_ = lean_box((v_rinv_621_) as usize);
                lean_inc(v_rhs_619_);
                v___x_628_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_628_, 0, v_rhs_619_);
                lean_ctor_set(v___x_628_, 1, v___x_627_);
                v___x_629_ = lean_box(0);
                v___x_630_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_630_, 0, v___x_628_);
                lean_ctor_set(v___x_630_, 1, v___x_629_);
                v___x_631_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_631_, 0, v___x_626_);
                lean_ctor_set(v___x_631_, 1, v___x_630_);
                v___x_632_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_632_, 0, v___x_624_);
                lean_ctor_set(v___x_632_, 1, v___x_631_);
                v___x_633_ = 0;
                v___x_634_ = lean_box((v___x_633_) as usize);
                v___x_635_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_635_, 0, v_output_617_);
                lean_ctor_set(v___x_635_, 1, v___x_634_);
                if v_rinv_621_ == 0 {
                    v___y_648_ = v___x_622_;
                    state = 2;
                    continue;
                } else {
                    v___y_648_ = v___x_633_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_639_ = lean_box((v___y_638_) as usize);
                v___x_640_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_640_, 0, v_lhs_618_);
                lean_ctor_set(v___x_640_, 1, v___x_639_);
                v___x_641_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_641_, 0, v___x_640_);
                lean_ctor_set(v___x_641_, 1, v___x_629_);
                v___x_642_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_642_, 0, v___x_635_);
                lean_ctor_set(v___x_642_, 1, v___x_641_);
                v___x_643_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0;
                v___x_644_ = lean_array_push(v___x_643_, v___x_642_);
                v___x_645_ = lean_array_push(v___x_644_, v___y_637_);
                v___x_646_ = lean_array_push(v___x_645_, v___x_632_);
                return v___x_646_;
            }
            2 => {
                v___x_649_ = lean_box((v___y_648_) as usize);
                v___x_650_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_650_, 0, v_rhs_619_);
                lean_ctor_set(v___x_650_, 1, v___x_649_);
                v___x_651_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_651_, 0, v___x_650_);
                lean_ctor_set(v___x_651_, 1, v___x_629_);
                lean_inc_ref(v___x_635_);
                v___x_652_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_652_, 0, v___x_635_);
                lean_ctor_set(v___x_652_, 1, v___x_651_);
                if v_linv_620_ == 0 {
                    v___y_637_ = v___x_652_;
                    v___y_638_ = v___x_622_;
                    state = 1;
                    continue;
                } else {
                    v___y_637_ = v___x_652_;
                    v___y_638_ = v___x_633_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(
    mut v_output_653_: *mut LeanObject,
    mut v_lhs_654_: *mut LeanObject,
    mut v_rhs_655_: *mut LeanObject,
    mut v_linv_656_: *mut LeanObject,
    mut v_rinv_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_linv_boxed_658_: u8 = 0;
    let mut v_rinv_boxed_659_: u8 = 0;
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_linv_boxed_658_ = (lean_unbox(v_linv_656_) as u8);
    v_rinv_boxed_659_ = (lean_unbox(v_rinv_657_) as u8);
    v_res_660_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(
        v_output_653_,
        v_lhs_654_,
        v_rhs_655_,
        v_linv_boxed_658_,
        v_rinv_boxed_659_,
    );
    return v_res_660_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(
    mut v_00_u03b1_661_: *mut LeanObject,
    mut v_output_662_: *mut LeanObject,
    mut v_lhs_663_: *mut LeanObject,
    mut v_rhs_664_: *mut LeanObject,
    mut v_linv_665_: u8,
    mut v_rinv_666_: u8,
) -> *mut LeanObject {
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    v___x_667_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(
        v_output_662_,
        v_lhs_663_,
        v_rhs_664_,
        v_linv_665_,
        v_rinv_666_,
    );
    return v___x_667_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(
    mut v_00_u03b1_668_: *mut LeanObject,
    mut v_output_669_: *mut LeanObject,
    mut v_lhs_670_: *mut LeanObject,
    mut v_rhs_671_: *mut LeanObject,
    mut v_linv_672_: *mut LeanObject,
    mut v_rinv_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_linv_boxed_674_: u8 = 0;
    let mut v_rinv_boxed_675_: u8 = 0;
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_linv_boxed_674_ = (lean_unbox(v_linv_672_) as u8);
    v_rinv_boxed_675_ = (lean_unbox(v_rinv_673_) as u8);
    v_res_676_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(
        v_00_u03b1_668_,
        v_output_669_,
        v_lhs_670_,
        v_rhs_671_,
        v_linv_boxed_674_,
        v_rinv_boxed_675_,
    );
    return v_res_676_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(
    mut v_aig_677_: *mut LeanObject,
    mut v_assign1_678_: *mut LeanObject,
    mut v_assign2_679_: *mut LeanObject,
    mut v_var_680_: *mut LeanObject,
) -> u8 {
    let mut v_decls_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    v_decls_681_ = lean_ctor_get(v_aig_677_, 0);
    v___x_682_ = lean_array_get_size(v_decls_681_);
    v___x_683_ = lean_nat_dec_lt(v_var_680_, v___x_682_);
    if v___x_683_ == 0 {
        let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: u8 = 0;
        lean_dec_ref(v_assign2_679_);
        v___x_684_ = lean_nat_sub(v_var_680_, v___x_682_);
        lean_dec(v_var_680_);
        v___x_685_ = lean_apply_1(v_assign1_678_, v___x_684_);
        v___x_686_ = (lean_unbox(v___x_685_) as u8);
        return v___x_686_;
    } else {
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: u8 = 0;
        lean_dec_ref(v_assign1_678_);
        v___x_687_ = lean_apply_1(v_assign2_679_, v_var_680_);
        v___x_688_ = (lean_unbox(v___x_687_) as u8);
        return v___x_688_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(
    mut v_aig_689_: *mut LeanObject,
    mut v_assign1_690_: *mut LeanObject,
    mut v_assign2_691_: *mut LeanObject,
    mut v_var_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_693_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(
        v_aig_689_,
        v_assign1_690_,
        v_assign2_691_,
        v_var_692_,
    );
    lean_dec_ref(v_aig_689_);
    v_r_694_ = lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(
    mut v_aig_695_: *mut LeanObject,
    mut v_assign_696_: *mut LeanObject,
    mut v_var_697_: *mut LeanObject,
) -> u8 {
    let mut v_decls_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    v_decls_698_ = lean_ctor_get(v_aig_695_, 0);
    v___x_699_ = lean_array_get_size(v_decls_698_);
    v___x_700_ = lean_nat_add(v_var_697_, v___x_699_);
    v___x_701_ = lean_apply_1(v_assign_696_, v___x_700_);
    v___x_702_ = (lean_unbox(v___x_701_) as u8);
    return v___x_702_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(
    mut v_aig_703_: *mut LeanObject,
    mut v_assign_704_: *mut LeanObject,
    mut v_var_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_706_: u8 = 0;
    let mut v_r_707_: *mut LeanObject = core::ptr::null_mut();
    v_res_706_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(
        v_aig_703_,
        v_assign_704_,
        v_var_705_,
    );
    lean_dec(v_var_705_);
    lean_dec_ref(v_aig_703_);
    v_r_707_ = lean_box((v_res_706_) as usize);
    return v_r_707_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(
    mut v_assign_708_: *mut LeanObject,
    mut v_idx_709_: *mut LeanObject,
) -> u8 {
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: u8 = 0;
    v___x_710_ = lean_apply_1(v_assign_708_, v_idx_709_);
    v___x_711_ = (lean_unbox(v___x_710_) as u8);
    return v___x_711_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(
    mut v_assign_712_: *mut LeanObject,
    mut v_idx_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: u8 = 0;
    let mut v_r_715_: *mut LeanObject = core::ptr::null_mut();
    v_res_714_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(
        v_assign_712_,
        v_idx_713_,
    );
    v_r_715_ = lean_box((v_res_714_) as usize);
    return v_r_715_;
}
pub unsafe fn l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(
    mut v_assign_716_: *mut LeanObject,
    mut v_entry_717_: *mut LeanObject,
) -> u8 {
    let mut v___y_719_: u8 = 0;
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: u8 = 0;
    let mut v_ref_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gate_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_725_: u8 = 0;
    let mut v_decls_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_722_ = lean_ctor_get(v_entry_717_, 1);
                v_aig_723_ = lean_ctor_get(v_entry_717_, 0);
                v_gate_724_ = lean_ctor_get(v_ref_722_, 0);
                v_invert_725_ = lean_ctor_get_uint8(
                    v_ref_722_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_decls_726_ = lean_ctor_get(v_aig_723_, 0);
                v___x_727_ =
                    l_Std_Sat_AIG_denote_go___redArg(v_gate_724_, v_decls_726_, v_assign_716_);
                if v___x_727_ == 0 {
                    if v_invert_725_ == 0 {
                        return v_invert_725_;
                    } else {
                        v___y_719_ = v___x_727_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_719_ = v_invert_725_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_719_ == 0 {
                    v___x_720_ = 1;
                    return v___x_720_;
                } else {
                    v___x_721_ = 0;
                    return v___x_721_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(
    mut v_assign_728_: *mut LeanObject,
    mut v_entry_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: u8 = 0;
    let mut v_r_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_728_, v_entry_729_);
    lean_dec_ref(v_entry_729_);
    v_r_731_ = lean_box((v_res_730_) as usize);
    return v_r_731_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(
    mut v_aig_732_: *mut LeanObject,
    mut v_assign1_733_: *mut LeanObject,
    mut v_idx_734_: *mut LeanObject,
) -> u8 {
    let mut v___x_735_: u8 = 0;
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    v___x_735_ = 0;
    v___x_736_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_736_, 0, v_idx_734_);
    lean_ctor_set_uint8(
        v___x_736_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_735_,
    );
    v___x_737_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_737_, 0, v_aig_732_);
    lean_ctor_set(v___x_737_, 1, v___x_736_);
    v___x_738_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_733_, v___x_737_);
    lean_dec_ref_known(v___x_737_, 2);
    return v___x_738_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(
    mut v_aig_739_: *mut LeanObject,
    mut v_assign1_740_: *mut LeanObject,
    mut v_idx_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_742_: u8 = 0;
    let mut v_r_743_: *mut LeanObject = core::ptr::null_mut();
    v_res_742_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(
        v_aig_739_,
        v_assign1_740_,
        v_idx_741_,
    );
    v_r_743_ = lean_box((v_res_742_) as usize);
    return v_r_743_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(
    mut v_aig_744_: *mut LeanObject,
    mut v_assign1_745_: *mut LeanObject,
    mut v_var_746_: *mut LeanObject,
) -> u8 {
    let mut v___f_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    lean_inc_ref(v_assign1_745_);
    lean_inc_ref(v_aig_744_);
    v___f_747_ = lean_alloc_closure(
        l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_747_, 0, v_aig_744_);
    lean_closure_set(v___f_747_, 1, v_assign1_745_);
    v___x_748_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(
        v_aig_744_,
        v_assign1_745_,
        v___f_747_,
        v_var_746_,
    );
    lean_dec_ref(v_aig_744_);
    return v___x_748_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(
    mut v_aig_749_: *mut LeanObject,
    mut v_assign1_750_: *mut LeanObject,
    mut v_var_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_752_: u8 = 0;
    let mut v_r_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_752_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(
        v_aig_749_,
        v_assign1_750_,
        v_var_751_,
    );
    v_r_753_ = lean_box((v_res_752_) as usize);
    return v_r_753_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(
    mut v_aig_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v_decls_755_ = lean_ctor_get(v_aig_754_, 0);
    v___x_756_ = lean_array_get_size(v_decls_755_);
    v___x_757_ = 0;
    v___x_758_ = lean_box((v___x_757_) as usize);
    v___x_759_ = lean_mk_array(v___x_756_, v___x_758_);
    return v___x_759_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(
    mut v_aig_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_761_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_760_);
    lean_dec_ref(v_aig_760_);
    return v_res_761_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(
    mut v_cache_762_: *mut LeanObject,
    mut v_idx_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = 1;
    v___x_765_ = lean_box((v___x_764_) as usize);
    v_out_766_ = lean_array_fset(v_cache_762_, v_idx_763_, v___x_765_);
    return v_out_766_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(
    mut v_cache_767_: *mut LeanObject,
    mut v_idx_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_769_: *mut LeanObject = core::ptr::null_mut();
    v_res_769_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(
        v_cache_767_,
        v_idx_768_,
    );
    lean_dec(v_idx_768_);
    return v_res_769_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(
    mut v_aig_770_: *mut LeanObject,
    mut v_cnf_771_: *mut LeanObject,
    mut v_cache_772_: *mut LeanObject,
    mut v_idx_773_: *mut LeanObject,
    mut v_h_774_: *mut LeanObject,
    mut v_htip_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(
        v_cache_772_,
        v_idx_773_,
    );
    return v___x_776_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(
    mut v_aig_777_: *mut LeanObject,
    mut v_cnf_778_: *mut LeanObject,
    mut v_cache_779_: *mut LeanObject,
    mut v_idx_780_: *mut LeanObject,
    mut v_h_781_: *mut LeanObject,
    mut v_htip_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(
        v_aig_777_,
        v_cnf_778_,
        v_cache_779_,
        v_idx_780_,
        v_h_781_,
        v_htip_782_,
    );
    lean_dec(v_idx_780_);
    lean_dec_ref(v_cnf_778_);
    lean_dec_ref(v_aig_777_);
    return v_res_783_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(
    mut v_cache_784_: *mut LeanObject,
    mut v_idx_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_786_ = 1;
    v___x_787_ = lean_box((v___x_786_) as usize);
    v_out_788_ = lean_array_fset(v_cache_784_, v_idx_785_, v___x_787_);
    return v_out_788_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(
    mut v_cache_789_: *mut LeanObject,
    mut v_idx_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(
        v_cache_789_,
        v_idx_790_,
    );
    lean_dec(v_idx_790_);
    return v_res_791_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(
    mut v_aig_792_: *mut LeanObject,
    mut v_cnf_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
    mut v_cache_795_: *mut LeanObject,
    mut v_idx_796_: *mut LeanObject,
    mut v_h_797_: *mut LeanObject,
    mut v_htip_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(
        v_cache_795_,
        v_idx_796_,
    );
    return v___x_799_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(
    mut v_aig_800_: *mut LeanObject,
    mut v_cnf_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
    mut v_cache_803_: *mut LeanObject,
    mut v_idx_804_: *mut LeanObject,
    mut v_h_805_: *mut LeanObject,
    mut v_htip_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_807_: *mut LeanObject = core::ptr::null_mut();
    v_res_807_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(
        v_aig_800_,
        v_cnf_801_,
        v_a_802_,
        v_cache_803_,
        v_idx_804_,
        v_h_805_,
        v_htip_806_,
    );
    lean_dec(v_idx_804_);
    lean_dec(v_a_802_);
    lean_dec_ref(v_cnf_801_);
    lean_dec_ref(v_aig_800_);
    return v_res_807_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(
    mut v_lhs_808_: *mut LeanObject,
    mut v_rhs_809_: *mut LeanObject,
    mut v_cache_810_: *mut LeanObject,
    mut v_idx_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = 1;
    v___x_813_ = lean_box((v___x_812_) as usize);
    v_out_814_ = lean_array_fset(v_cache_810_, v_idx_811_, v___x_813_);
    return v_out_814_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(
    mut v_lhs_815_: *mut LeanObject,
    mut v_rhs_816_: *mut LeanObject,
    mut v_cache_817_: *mut LeanObject,
    mut v_idx_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(
        v_lhs_815_,
        v_rhs_816_,
        v_cache_817_,
        v_idx_818_,
    );
    lean_dec(v_idx_818_);
    lean_dec(v_rhs_816_);
    lean_dec(v_lhs_815_);
    return v_res_819_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(
    mut v_aig_820_: *mut LeanObject,
    mut v_cnf_821_: *mut LeanObject,
    mut v_lhs_822_: *mut LeanObject,
    mut v_rhs_823_: *mut LeanObject,
    mut v_cache_824_: *mut LeanObject,
    mut v_hlb_825_: *mut LeanObject,
    mut v_hrb_826_: *mut LeanObject,
    mut v_idx_827_: *mut LeanObject,
    mut v_h_828_: *mut LeanObject,
    mut v_htip_829_: *mut LeanObject,
    mut v_hl_830_: *mut LeanObject,
    mut v_hr_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(
        v_lhs_822_,
        v_rhs_823_,
        v_cache_824_,
        v_idx_827_,
    );
    return v___x_832_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(
    mut v_aig_833_: *mut LeanObject,
    mut v_cnf_834_: *mut LeanObject,
    mut v_lhs_835_: *mut LeanObject,
    mut v_rhs_836_: *mut LeanObject,
    mut v_cache_837_: *mut LeanObject,
    mut v_hlb_838_: *mut LeanObject,
    mut v_hrb_839_: *mut LeanObject,
    mut v_idx_840_: *mut LeanObject,
    mut v_h_841_: *mut LeanObject,
    mut v_htip_842_: *mut LeanObject,
    mut v_hl_843_: *mut LeanObject,
    mut v_hr_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(
        v_aig_833_,
        v_cnf_834_,
        v_lhs_835_,
        v_rhs_836_,
        v_cache_837_,
        v_hlb_838_,
        v_hrb_839_,
        v_idx_840_,
        v_h_841_,
        v_htip_842_,
        v_hl_843_,
        v_hr_844_,
    );
    lean_dec(v_idx_840_);
    lean_dec(v_rhs_836_);
    lean_dec(v_lhs_835_);
    lean_dec_ref(v_cnf_834_);
    lean_dec_ref(v_aig_833_);
    return v_res_845_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(
    mut v_aig_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_855_: u8 = 0;
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_unused_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_861_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_847_ = lean_ctor_get(v_aig_846_, 0);
                v___x_848_ = lean_array_get_size(v_decls_847_);
                v___x_849_ = lean_unsigned_to_nat(2);
                v___x_850_ = lean_nat_mul(v___x_848_, v___x_849_);
                v___x_851_ = lean_mk_empty_array_with_capacity(v___x_850_);
                lean_dec(v___x_850_);
                v___x_852_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_846_);
                v_isSharedCheck_859_ = (!lean_is_exclusive(v_aig_846_)) as u8;
                if v_isSharedCheck_859_ == 0 {
                    v_unused_860_ = lean_ctor_get(v_aig_846_, 1);
                    lean_dec(v_unused_860_);
                    v_unused_861_ = lean_ctor_get(v_aig_846_, 0);
                    lean_dec(v_unused_861_);
                    v___x_854_ = v_aig_846_;
                    v_isShared_855_ = v_isSharedCheck_859_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_aig_846_);
                    v___x_854_ = lean_box(0);
                    v_isShared_855_ = v_isSharedCheck_859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_855_ == 0 {
                    lean_ctor_set(v___x_854_, 1, v___x_852_);
                    lean_ctor_set(v___x_854_, 0, v___x_851_);
                    v___x_857_ = v___x_854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_851_);
                    lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_852_);
                    v___x_857_ = v_reuseFailAlloc_858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(
    mut v_state_862_: *mut LeanObject,
    mut v_idx_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cnf_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v_val_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newCnf_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cnf_864_ = lean_ctor_get(v_state_862_, 0);
                v_cache_865_ = lean_ctor_get(v_state_862_, 1);
                v_isSharedCheck_875_ = (!lean_is_exclusive(v_state_862_)) as u8;
                if v_isSharedCheck_875_ == 0 {
                    v___x_867_ = v_state_862_;
                    v_isShared_868_ = v_isSharedCheck_875_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_cache_865_);
                    lean_inc(v_cnf_864_);
                    lean_dec(v_state_862_);
                    v___x_867_ = lean_box(0);
                    v_isShared_868_ = v_isSharedCheck_875_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_val_869_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(
                        v_cache_865_,
                        v_idx_863_,
                    );
                v_newCnf_870_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_863_);
                v___x_871_ = l_Array_append___redArg(v_cnf_864_, v_newCnf_870_);
                lean_dec_ref(v_newCnf_870_);
                if v_isShared_868_ == 0 {
                    lean_ctor_set(v___x_867_, 1, v_val_869_);
                    lean_ctor_set(v___x_867_, 0, v___x_871_);
                    v___x_873_ = v___x_867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
                    lean_ctor_set(v_reuseFailAlloc_874_, 1, v_val_869_);
                    v___x_873_ = v_reuseFailAlloc_874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(
    mut v_aig_876_: *mut LeanObject,
    mut v_state_877_: *mut LeanObject,
    mut v_idx_878_: *mut LeanObject,
    mut v_h_879_: *mut LeanObject,
    mut v_htip_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    v___x_881_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(
        v_state_877_,
        v_idx_878_,
    );
    return v___x_881_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(
    mut v_aig_882_: *mut LeanObject,
    mut v_state_883_: *mut LeanObject,
    mut v_idx_884_: *mut LeanObject,
    mut v_h_885_: *mut LeanObject,
    mut v_htip_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_887_: *mut LeanObject = core::ptr::null_mut();
    v_res_887_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(
        v_aig_882_,
        v_state_883_,
        v_idx_884_,
        v_h_885_,
        v_htip_886_,
    );
    lean_dec_ref(v_aig_882_);
    return v_res_887_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(
    mut v_aig_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
    mut v_state_890_: *mut LeanObject,
    mut v_idx_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cnf_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v_decls_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newCnf_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cnf_892_ = lean_ctor_get(v_state_890_, 0);
                v_cache_893_ = lean_ctor_get(v_state_890_, 1);
                v_isSharedCheck_906_ = (!lean_is_exclusive(v_state_890_)) as u8;
                if v_isSharedCheck_906_ == 0 {
                    v___x_895_ = v_state_890_;
                    v_isShared_896_ = v_isSharedCheck_906_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_cache_893_);
                    lean_inc(v_cnf_892_);
                    lean_dec(v_state_890_);
                    v___x_895_ = lean_box(0);
                    v_isShared_896_ = v_isSharedCheck_906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_897_ = lean_ctor_get(v_aig_888_, 0);
                v_val_898_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(
                        v_cache_893_,
                        v_idx_891_,
                    );
                v___x_899_ = lean_array_get_size(v_decls_897_);
                v___x_900_ = lean_nat_add(v_a_889_, v___x_899_);
                v_newCnf_901_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(
                    v_idx_891_, v___x_900_,
                );
                v___x_902_ = l_Array_append___redArg(v_cnf_892_, v_newCnf_901_);
                lean_dec_ref(v_newCnf_901_);
                if v_isShared_896_ == 0 {
                    lean_ctor_set(v___x_895_, 1, v_val_898_);
                    lean_ctor_set(v___x_895_, 0, v___x_902_);
                    v___x_904_ = v___x_895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
                    lean_ctor_set(v_reuseFailAlloc_905_, 1, v_val_898_);
                    v___x_904_ = v_reuseFailAlloc_905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(
    mut v_aig_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_state_909_: *mut LeanObject,
    mut v_idx_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_911_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(
        v_aig_907_,
        v_a_908_,
        v_state_909_,
        v_idx_910_,
    );
    lean_dec(v_a_908_);
    lean_dec_ref(v_aig_907_);
    return v_res_911_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(
    mut v_aig_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_state_914_: *mut LeanObject,
    mut v_idx_915_: *mut LeanObject,
    mut v_h_916_: *mut LeanObject,
    mut v_htip_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(
        v_aig_912_,
        v_a_913_,
        v_state_914_,
        v_idx_915_,
    );
    return v___x_918_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(
    mut v_aig_919_: *mut LeanObject,
    mut v_a_920_: *mut LeanObject,
    mut v_state_921_: *mut LeanObject,
    mut v_idx_922_: *mut LeanObject,
    mut v_h_923_: *mut LeanObject,
    mut v_htip_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_925_: *mut LeanObject = core::ptr::null_mut();
    v_res_925_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(
        v_aig_919_,
        v_a_920_,
        v_state_921_,
        v_idx_922_,
        v_h_923_,
        v_htip_924_,
    );
    lean_dec(v_a_920_);
    lean_dec_ref(v_aig_919_);
    return v_res_925_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(
    mut v_lhs_926_: *mut LeanObject,
    mut v_rhs_927_: *mut LeanObject,
    mut v_state_928_: *mut LeanObject,
    mut v_idx_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cnf_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_934_: u8 = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_939_: u8 = 0;
    let mut v___y_940_: u8 = 0;
    let mut v_val_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newCnf_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_948_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: u8 = 0;
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: u8 = 0;
    let mut v_isSharedCheck_959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cnf_930_ = lean_ctor_get(v_state_928_, 0);
                v_cache_931_ = lean_ctor_get(v_state_928_, 1);
                v_isSharedCheck_959_ = (!lean_is_exclusive(v_state_928_)) as u8;
                if v_isSharedCheck_959_ == 0 {
                    v___x_933_ = v_state_928_;
                    v_isShared_934_ = v_isSharedCheck_959_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_cache_931_);
                    lean_inc(v_cnf_930_);
                    lean_dec(v_state_928_);
                    v___x_933_ = lean_box(0);
                    v_isShared_934_ = v_isSharedCheck_959_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_935_ = lean_unsigned_to_nat(1);
                v___x_936_ = lean_nat_shiftr(v_lhs_926_, v___x_935_);
                v___x_937_ = lean_nat_shiftr(v_rhs_927_, v___x_935_);
                v___x_954_ = lean_nat_land(v___x_935_, v_lhs_926_);
                v___x_955_ = lean_unsigned_to_nat(0);
                v___x_956_ = lean_nat_dec_eq(v___x_954_, v___x_955_);
                lean_dec(v___x_954_);
                if v___x_956_ == 0 {
                    v___x_957_ = 1;
                    v___y_948_ = v___x_957_;
                    state = 4;
                    continue;
                } else {
                    v___x_958_ = 0;
                    v___y_948_ = v___x_958_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v_val_941_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(
                        v_lhs_926_,
                        v_rhs_927_,
                        v_cache_931_,
                        v_idx_929_,
                    );
                v_newCnf_942_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(
                    v_idx_929_, v___x_936_, v___x_937_, v___y_939_, v___y_940_,
                );
                v___x_943_ = l_Array_append___redArg(v_cnf_930_, v_newCnf_942_);
                lean_dec_ref(v_newCnf_942_);
                if v_isShared_934_ == 0 {
                    lean_ctor_set(v___x_933_, 1, v_val_941_);
                    lean_ctor_set(v___x_933_, 0, v___x_943_);
                    v___x_945_ = v___x_933_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
                    lean_ctor_set(v_reuseFailAlloc_946_, 1, v_val_941_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_945_;
            }
            4 => {
                v___x_949_ = lean_nat_land(v___x_935_, v_rhs_927_);
                v___x_950_ = lean_unsigned_to_nat(0);
                v___x_951_ = lean_nat_dec_eq(v___x_949_, v___x_950_);
                lean_dec(v___x_949_);
                if v___x_951_ == 0 {
                    v___x_952_ = 1;
                    v___y_939_ = v___y_948_;
                    v___y_940_ = v___x_952_;
                    state = 2;
                    continue;
                } else {
                    v___x_953_ = 0;
                    v___y_939_ = v___y_948_;
                    v___y_940_ = v___x_953_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(
    mut v_lhs_960_: *mut LeanObject,
    mut v_rhs_961_: *mut LeanObject,
    mut v_state_962_: *mut LeanObject,
    mut v_idx_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_964_: *mut LeanObject = core::ptr::null_mut();
    v_res_964_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(
        v_lhs_960_,
        v_rhs_961_,
        v_state_962_,
        v_idx_963_,
    );
    lean_dec(v_rhs_961_);
    lean_dec(v_lhs_960_);
    return v_res_964_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(
    mut v_aig_965_: *mut LeanObject,
    mut v_lhs_966_: *mut LeanObject,
    mut v_rhs_967_: *mut LeanObject,
    mut v_state_968_: *mut LeanObject,
    mut v_hlb_969_: *mut LeanObject,
    mut v_hrb_970_: *mut LeanObject,
    mut v_idx_971_: *mut LeanObject,
    mut v_h_972_: *mut LeanObject,
    mut v_htip_973_: *mut LeanObject,
    mut v_hl_974_: *mut LeanObject,
    mut v_hr_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(
        v_lhs_966_,
        v_rhs_967_,
        v_state_968_,
        v_idx_971_,
    );
    return v___x_976_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(
    mut v_aig_977_: *mut LeanObject,
    mut v_lhs_978_: *mut LeanObject,
    mut v_rhs_979_: *mut LeanObject,
    mut v_state_980_: *mut LeanObject,
    mut v_hlb_981_: *mut LeanObject,
    mut v_hrb_982_: *mut LeanObject,
    mut v_idx_983_: *mut LeanObject,
    mut v_h_984_: *mut LeanObject,
    mut v_htip_985_: *mut LeanObject,
    mut v_hl_986_: *mut LeanObject,
    mut v_hr_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_988_: *mut LeanObject = core::ptr::null_mut();
    v_res_988_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(
        v_aig_977_,
        v_lhs_978_,
        v_rhs_979_,
        v_state_980_,
        v_hlb_981_,
        v_hrb_982_,
        v_idx_983_,
        v_h_984_,
        v_htip_985_,
        v_hl_986_,
        v_hr_987_,
    );
    lean_dec(v_rhs_979_);
    lean_dec(v_lhs_978_);
    lean_dec_ref(v_aig_977_);
    return v_res_988_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(
    mut v_assign_989_: *mut LeanObject,
    mut v_state_990_: *mut LeanObject,
) -> u8 {
    let mut v_cnf_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    v_cnf_991_ = lean_ctor_get(v_state_990_, 0);
    v___x_992_ = l_Std_Sat_CNF_eval___redArg(v_assign_989_, v_cnf_991_);
    return v___x_992_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(
    mut v_assign_993_: *mut LeanObject,
    mut v_state_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_995_: u8 = 0;
    let mut v_r_996_: *mut LeanObject = core::ptr::null_mut();
    v_res_995_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(
        v_assign_993_,
        v_state_994_,
    );
    lean_dec_ref(v_state_994_);
    v_r_996_ = lean_box((v_res_995_) as usize);
    return v_r_996_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(
    mut v_aig_997_: *mut LeanObject,
    mut v_assign_998_: *mut LeanObject,
    mut v_state_999_: *mut LeanObject,
) -> u8 {
    let mut v___x_1000_: u8 = 0;
    v___x_1000_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(
        v_assign_998_,
        v_state_999_,
    );
    return v___x_1000_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(
    mut v_aig_1001_: *mut LeanObject,
    mut v_assign_1002_: *mut LeanObject,
    mut v_state_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: u8 = 0;
    let mut v_r_1005_: *mut LeanObject = core::ptr::null_mut();
    v_res_1004_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(
        v_aig_1001_,
        v_assign_1002_,
        v_state_1003_,
    );
    lean_dec_ref(v_state_1003_);
    lean_dec_ref(v_aig_1001_);
    v_r_1005_ = lean_box((v_res_1004_) as usize);
    return v_r_1005_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
    mut v_aig_1006_: *mut LeanObject,
    mut v_upper_1007_: *mut LeanObject,
    mut v_state_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cache_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: u8 = 0;
    v_cache_1009_ = lean_ctor_get(v_state_1008_, 1);
    v___x_1010_ = lean_array_fget_borrowed(v_cache_1009_, v_upper_1007_);
    v___x_1011_ = (lean_unbox(v___x_1010_) as u8);
    if v___x_1011_ == 0 {
        let mut v_decls_1012_: *mut LeanObject = core::ptr::null_mut();
        let mut v_decl_1013_: *mut LeanObject = core::ptr::null_mut();
        v_decls_1012_ = lean_ctor_get(v_aig_1006_, 0);
        v_decl_1013_ = lean_array_fget_borrowed(v_decls_1012_, v_upper_1007_);
        match lean_obj_tag(v_decl_1013_) {
            0 => {
                let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
                v___x_1014_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(
                        v_state_1008_,
                        v_upper_1007_,
                    );
                return v___x_1014_;
            }
            1 => {
                let mut v_idx_1015_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
                v_idx_1015_ = lean_ctor_get(v_decl_1013_, 0);
                v___x_1016_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(
                        v_aig_1006_,
                        v_idx_1015_,
                        v_state_1008_,
                        v_upper_1007_,
                    );
                return v___x_1016_;
            }
            _ => {
                let mut v_l_1017_: *mut LeanObject = core::ptr::null_mut();
                let mut v_r_1018_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
                let mut v_val_1021_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
                let mut v_val_1023_: *mut LeanObject = core::ptr::null_mut();
                let mut v_val_1024_: *mut LeanObject = core::ptr::null_mut();
                v_l_1017_ = lean_ctor_get(v_decl_1013_, 0);
                v_r_1018_ = lean_ctor_get(v_decl_1013_, 1);
                v___x_1019_ = lean_unsigned_to_nat(1);
                v___x_1020_ = lean_nat_shiftr(v_l_1017_, v___x_1019_);
                v_val_1021_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
                    v_aig_1006_,
                    v___x_1020_,
                    v_state_1008_,
                );
                v___x_1022_ = lean_nat_shiftr(v_r_1018_, v___x_1019_);
                v_val_1023_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
                    v_aig_1006_,
                    v___x_1022_,
                    v_val_1021_,
                );
                v_val_1024_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(
                        v_l_1017_,
                        v_r_1018_,
                        v_val_1023_,
                        v_upper_1007_,
                    );
                return v_val_1024_;
            }
        }
    } else {
        lean_dec(v_upper_1007_);
        return v_state_1008_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(
    mut v_aig_1025_: *mut LeanObject,
    mut v_upper_1026_: *mut LeanObject,
    mut v_state_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1028_: *mut LeanObject = core::ptr::null_mut();
    v_res_1028_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
        v_aig_1025_,
        v_upper_1026_,
        v_state_1027_,
    );
    lean_dec_ref(v_aig_1025_);
    return v_res_1028_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(
    mut v_aig_1029_: *mut LeanObject,
    mut v_upper_1030_: *mut LeanObject,
    mut v_h_1031_: *mut LeanObject,
    mut v_state_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    v___x_1033_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
        v_aig_1029_,
        v_upper_1030_,
        v_state_1032_,
    );
    return v___x_1033_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(
    mut v_aig_1034_: *mut LeanObject,
    mut v_upper_1035_: *mut LeanObject,
    mut v_h_1036_: *mut LeanObject,
    mut v_state_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1038_: *mut LeanObject = core::ptr::null_mut();
    v_res_1038_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(
        v_aig_1034_,
        v_upper_1035_,
        v_h_1036_,
        v_state_1037_,
    );
    lean_dec_ref(v_aig_1034_);
    return v_res_1038_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter___redArg(
    mut v_decl_1039_: *mut LeanObject,
    mut v_h__1_1040_: *mut LeanObject,
    mut v_h__2_1041_: *mut LeanObject,
    mut v_h__3_1042_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_1039_) {
        0 => {
            let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1042_);
            lean_dec(v_h__2_1041_);
            v___x_1043_ = lean_apply_1(v_h__1_1040_, lean_box(0));
            return v___x_1043_;
        }
        1 => {
            let mut v_idx_1044_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1042_);
            lean_dec(v_h__1_1040_);
            v_idx_1044_ = lean_ctor_get(v_decl_1039_, 0);
            lean_inc(v_idx_1044_);
            lean_dec_ref_known(v_decl_1039_, 1);
            v___x_1045_ = lean_apply_2(v_h__2_1041_, v_idx_1044_, lean_box(0));
            return v___x_1045_;
        }
        _ => {
            let mut v_l_1046_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_1047_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1041_);
            lean_dec(v_h__1_1040_);
            v_l_1046_ = lean_ctor_get(v_decl_1039_, 0);
            lean_inc(v_l_1046_);
            v_r_1047_ = lean_ctor_get(v_decl_1039_, 1);
            lean_inc(v_r_1047_);
            lean_dec_ref_known(v_decl_1039_, 2);
            v___x_1048_ = lean_apply_3(v_h__3_1042_, v_l_1046_, v_r_1047_, lean_box(0));
            return v___x_1048_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter(
    mut v_motive_1049_: *mut LeanObject,
    mut v_decl_1050_: *mut LeanObject,
    mut v_h__1_1051_: *mut LeanObject,
    mut v_h__2_1052_: *mut LeanObject,
    mut v_h__3_1053_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_1050_) {
        0 => {
            let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1053_);
            lean_dec(v_h__2_1052_);
            v___x_1054_ = lean_apply_1(v_h__1_1051_, lean_box(0));
            return v___x_1054_;
        }
        1 => {
            let mut v_idx_1055_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1053_);
            lean_dec(v_h__1_1051_);
            v_idx_1055_ = lean_ctor_get(v_decl_1050_, 0);
            lean_inc(v_idx_1055_);
            lean_dec_ref_known(v_decl_1050_, 1);
            v___x_1056_ = lean_apply_2(v_h__2_1052_, v_idx_1055_, lean_box(0));
            return v___x_1056_;
        }
        _ => {
            let mut v_l_1057_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_1058_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1052_);
            lean_dec(v_h__1_1051_);
            v_l_1057_ = lean_ctor_get(v_decl_1050_, 0);
            lean_inc(v_l_1057_);
            v_r_1058_ = lean_ctor_get(v_decl_1050_, 1);
            lean_inc(v_r_1058_);
            lean_dec_ref_known(v_decl_1050_, 2);
            v___x_1059_ = lean_apply_3(v_h__3_1053_, v_l_1057_, v_r_1058_, lean_box(0));
            return v___x_1059_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___redArg(
    mut v_x_1060_: *mut LeanObject,
    mut v_h__1_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    v___x_1062_ = lean_apply_2(v_h__1_1061_, v_x_1060_, lean_box(0));
    return v___x_1062_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(
    mut v_aig_1063_: *mut LeanObject,
    mut v_upper_1064_: *mut LeanObject,
    mut v_h_1065_: *mut LeanObject,
    mut v_state_1066_: *mut LeanObject,
    mut v_lhs_1067_: *mut LeanObject,
    mut v_rhs_1068_: *mut LeanObject,
    mut v_this_1069_: *mut LeanObject,
    mut v_motive_1070_: *mut LeanObject,
    mut v_x_1071_: *mut LeanObject,
    mut v_h__1_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1073_ = lean_apply_2(v_h__1_1072_, v_x_1071_, lean_box(0));
    return v___x_1073_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___boxed(
    mut v_aig_1074_: *mut LeanObject,
    mut v_upper_1075_: *mut LeanObject,
    mut v_h_1076_: *mut LeanObject,
    mut v_state_1077_: *mut LeanObject,
    mut v_lhs_1078_: *mut LeanObject,
    mut v_rhs_1079_: *mut LeanObject,
    mut v_this_1080_: *mut LeanObject,
    mut v_motive_1081_: *mut LeanObject,
    mut v_x_1082_: *mut LeanObject,
    mut v_h__1_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(
        v_aig_1074_,
        v_upper_1075_,
        v_h_1076_,
        v_state_1077_,
        v_lhs_1078_,
        v_rhs_1079_,
        v_this_1080_,
        v_motive_1081_,
        v_x_1082_,
        v_h__1_1083_,
    );
    lean_dec(v_rhs_1079_);
    lean_dec(v_lhs_1078_);
    lean_dec_ref(v_state_1077_);
    lean_dec(v_upper_1075_);
    lean_dec_ref(v_aig_1074_);
    return v_res_1084_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___redArg(
    mut v_x_1085_: *mut LeanObject,
    mut v_h__1_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_apply_2(v_h__1_1086_, v_x_1085_, lean_box(0));
    return v___x_1087_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(
    mut v_aig_1088_: *mut LeanObject,
    mut v_upper_1089_: *mut LeanObject,
    mut v_h_1090_: *mut LeanObject,
    mut v_lhs_1091_: *mut LeanObject,
    mut v_rhs_1092_: *mut LeanObject,
    mut v_this_1093_: *mut LeanObject,
    mut v_lstate_1094_: *mut LeanObject,
    mut v_motive_1095_: *mut LeanObject,
    mut v_x_1096_: *mut LeanObject,
    mut v_h__1_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_apply_2(v_h__1_1097_, v_x_1096_, lean_box(0));
    return v___x_1098_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___boxed(
    mut v_aig_1099_: *mut LeanObject,
    mut v_upper_1100_: *mut LeanObject,
    mut v_h_1101_: *mut LeanObject,
    mut v_lhs_1102_: *mut LeanObject,
    mut v_rhs_1103_: *mut LeanObject,
    mut v_this_1104_: *mut LeanObject,
    mut v_lstate_1105_: *mut LeanObject,
    mut v_motive_1106_: *mut LeanObject,
    mut v_x_1107_: *mut LeanObject,
    mut v_h__1_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(
        v_aig_1099_,
        v_upper_1100_,
        v_h_1101_,
        v_lhs_1102_,
        v_rhs_1103_,
        v_this_1104_,
        v_lstate_1105_,
        v_motive_1106_,
        v_x_1107_,
        v_h__1_1108_,
    );
    lean_dec_ref(v_lstate_1105_);
    lean_dec(v_rhs_1103_);
    lean_dec(v_lhs_1102_);
    lean_dec(v_upper_1100_);
    lean_dec_ref(v_aig_1099_);
    return v_res_1109_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___redArg(
    mut v_x_1110_: *mut LeanObject,
    mut v_h__1_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = lean_apply_2(v_h__1_1111_, v_x_1110_, lean_box(0));
    return v___x_1112_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(
    mut v_aig_1113_: *mut LeanObject,
    mut v_upper_1114_: *mut LeanObject,
    mut v_h_1115_: *mut LeanObject,
    mut v_rstate_1116_: *mut LeanObject,
    mut v_motive_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
    mut v_h__1_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = lean_apply_2(v_h__1_1119_, v_x_1118_, lean_box(0));
    return v___x_1120_;
}
pub unsafe fn l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___boxed(
    mut v_aig_1121_: *mut LeanObject,
    mut v_upper_1122_: *mut LeanObject,
    mut v_h_1123_: *mut LeanObject,
    mut v_rstate_1124_: *mut LeanObject,
    mut v_motive_1125_: *mut LeanObject,
    mut v_x_1126_: *mut LeanObject,
    mut v_h__1_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1128_: *mut LeanObject = core::ptr::null_mut();
    v_res_1128_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(
        v_aig_1121_,
        v_upper_1122_,
        v_h_1123_,
        v_rstate_1124_,
        v_motive_1125_,
        v_x_1126_,
        v_h__1_1127_,
    );
    lean_dec_ref(v_rstate_1124_);
    lean_dec(v_upper_1122_);
    lean_dec_ref(v_aig_1121_);
    return v_res_1128_;
}
pub unsafe fn l_Std_Sat_AIG_toCNF(mut v_entry_1129_: *mut LeanObject) -> *mut LeanObject {
    let mut v_ref_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v_gate_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_1136_: u8 = 0;
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: u8 = 0;
    let mut v_cnf_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v_unused_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: u8 = 0;
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1130_ = lean_ctor_get(v_entry_1129_, 1);
                v_aig_1131_ = lean_ctor_get(v_entry_1129_, 0);
                v_isSharedCheck_1158_ = (!lean_is_exclusive(v_entry_1129_)) as u8;
                if v_isSharedCheck_1158_ == 0 {
                    v___x_1133_ = v_entry_1129_;
                    v_isShared_1134_ = v_isSharedCheck_1158_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_1130_);
                    lean_inc(v_aig_1131_);
                    lean_dec(v_entry_1129_);
                    v___x_1133_ = lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1158_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_1135_ = lean_ctor_get(v_ref_1130_, 0);
                lean_inc_n(v_gate_1135_, 2);
                v_invert_1136_ = lean_ctor_get_uint8(
                    v_ref_1130_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_ref_1130_);
                lean_inc_ref(v_aig_1131_);
                v___x_1137_ =
                    l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_1131_);
                v_val_1138_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(
                    v_aig_1131_,
                    v_gate_1135_,
                    v___x_1137_,
                );
                lean_dec_ref(v_aig_1131_);
                if v_invert_1136_ == 0 {
                    v___x_1156_ = 1;
                    v___y_1140_ = v___x_1156_;
                    state = 2;
                    continue;
                } else {
                    v___x_1157_ = 0;
                    v___y_1140_ = v___x_1157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_cnf_1141_ = lean_ctor_get(v_val_1138_, 0);
                v_isSharedCheck_1154_ = (!lean_is_exclusive(v_val_1138_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v_unused_1155_ = lean_ctor_get(v_val_1138_, 1);
                    lean_dec(v_unused_1155_);
                    v___x_1143_ = v_val_1138_;
                    v_isShared_1144_ = v_isSharedCheck_1154_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_cnf_1141_);
                    lean_dec(v_val_1138_);
                    v___x_1143_ = lean_box(0);
                    v_isShared_1144_ = v_isSharedCheck_1154_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1145_ = lean_box((v___y_1140_) as usize);
                if v_isShared_1144_ == 0 {
                    lean_ctor_set(v___x_1143_, 1, v___x_1145_);
                    lean_ctor_set(v___x_1143_, 0, v_gate_1135_);
                    v___x_1147_ = v___x_1143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_gate_1135_);
                    lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1145_);
                    v___x_1147_ = v_reuseFailAlloc_1153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1148_ = lean_box(0);
                if v_isShared_1134_ == 0 {
                    lean_ctor_set_tag(v___x_1133_, 1);
                    lean_ctor_set(v___x_1133_, 1, v___x_1148_);
                    lean_ctor_set(v___x_1133_, 0, v___x_1147_);
                    v___x_1150_ = v___x_1133_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1147_);
                    lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1148_);
                    v___x_1150_ = v_reuseFailAlloc_1152_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1151_ = lean_array_push(v_cnf_1141_, v___x_1150_);
                return v___x_1151_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_CNF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_CNF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_CNF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_CNF(builtin);
}
