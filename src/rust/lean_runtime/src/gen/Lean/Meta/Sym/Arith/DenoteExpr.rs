// Lean compiler output
// Module: Lean.Meta.Sym.Arith.DenoteExpr
// Imports: Lean.Meta.Sym.Arith.Functions Lean.Meta.Sym.Arith.MonadVar
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkIntLit, l_Lean_mkNatLit, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Meta::Sym::Arith::Functions::{
    initialize_Lean_Meta_Sym_Arith_Functions, l_Lean_Meta_Sym_Arith_getAddFn___redArg,
    l_Lean_Meta_Sym_Arith_getIntCastFn___redArg, l_Lean_Meta_Sym_Arith_getMulFn___redArg,
    l_Lean_Meta_Sym_Arith_getNatCastFn___redArg, l_Lean_Meta_Sym_Arith_getNegFn___redArg,
    l_Lean_Meta_Sym_Arith_getPowFn___redArg, l_Lean_Meta_Sym_Arith_getSubFn___redArg,
    runtime_initialize_Lean_Meta_Sym_Arith_Functions,
};
use crate::r#gen::Lean::Meta::Sym::Arith::MonadVar::{
    initialize_Lean_Meta_Sym_Arith_MonadVar, runtime_initialize_Lean_Meta_Sym_Arith_MonadVar,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_borrowed, lean_nat_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value)
            as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value)
            as *mut LeanObject,
        12050285396929189622 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
            9341924117480681831 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            17636616155771105671 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__0(
    mut v_e_643_: *mut LeanObject,
    mut v_toPure_644_: *mut LeanObject,
    mut v_____do__lift_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Lean_Expr_app___override(v_____do__lift_645_, v_e_643_);
    v___x_647_ = lean_apply_2(v_toPure_644_, lean_box(0), v___x_646_);
    return v___x_647_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    v___x_649_ = lean_unsigned_to_nat(0);
    v___x_650_ = lean_nat_to_int(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1(
    mut v___x_651_: *mut LeanObject,
    mut v___x_652_: *mut LeanObject,
    mut v_type_653_: *mut LeanObject,
    mut v_n_654_: *mut LeanObject,
    mut v_k_655_: *mut LeanObject,
    mut v_toPure_656_: *mut LeanObject,
    mut v_inst_657_: *mut LeanObject,
    mut v_inst_658_: *mut LeanObject,
    mut v_inst_659_: *mut LeanObject,
    mut v_inst_660_: *mut LeanObject,
    mut v_inst_661_: *mut LeanObject,
    mut v_toBind_662_: *mut LeanObject,
    mut v_ofNatInst_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    v___x_664_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0;
    v___x_665_ = l_Lean_Name_mkStr2(v___x_651_, v___x_664_);
    v___x_666_ = l_Lean_mkConst(v___x_665_, v___x_652_);
    v_e_667_ = l_Lean_mkApp3(v___x_666_, v_type_653_, v_n_654_, v_ofNatInst_663_);
    v___x_668_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once),
        _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1,
    );
    v___x_669_ = lean_int_dec_lt(v_k_655_, v___x_668_);
    if v___x_669_ == 0 {
        let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_662_);
        lean_dec_ref(v_inst_661_);
        lean_dec_ref(v_inst_660_);
        lean_dec_ref(v_inst_659_);
        lean_dec_ref(v_inst_658_);
        lean_dec(v_inst_657_);
        v___x_670_ = lean_apply_2(v_toPure_656_, lean_box(0), v_e_667_);
        return v___x_670_;
    } else {
        let mut v___f_671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
        v___f_671_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_671_, 0, v_e_667_);
        lean_closure_set(v___f_671_, 1, v_toPure_656_);
        v___x_672_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(
            v_inst_657_,
            v_inst_658_,
            v_inst_659_,
            v_inst_660_,
            v_inst_661_,
        );
        v___x_673_ = lean_apply_4(
            v_toBind_662_,
            lean_box(0),
            lean_box(0),
            v___x_672_,
            v___f_671_,
        );
        return v___x_673_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___boxed(
    mut v___x_674_: *mut LeanObject,
    mut v___x_675_: *mut LeanObject,
    mut v_type_676_: *mut LeanObject,
    mut v_n_677_: *mut LeanObject,
    mut v_k_678_: *mut LeanObject,
    mut v_toPure_679_: *mut LeanObject,
    mut v_inst_680_: *mut LeanObject,
    mut v_inst_681_: *mut LeanObject,
    mut v_inst_682_: *mut LeanObject,
    mut v_inst_683_: *mut LeanObject,
    mut v_inst_684_: *mut LeanObject,
    mut v_toBind_685_: *mut LeanObject,
    mut v_ofNatInst_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_687_: *mut LeanObject = core::ptr::null_mut();
    v_res_687_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1(
        v___x_674_,
        v___x_675_,
        v_type_676_,
        v_n_677_,
        v_k_678_,
        v_toPure_679_,
        v_inst_680_,
        v_inst_681_,
        v_inst_682_,
        v_inst_683_,
        v_inst_684_,
        v_toBind_685_,
        v_ofNatInst_686_,
    );
    lean_dec(v_k_678_);
    return v_res_687_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__2(
    mut v___f_688_: *mut LeanObject,
    mut v_ofNatInst_689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = lean_apply_1(v___f_688_, v_ofNatInst_689_);
    return v___x_690_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4(
    mut v_toPure_699_: *mut LeanObject,
    mut v_toBind_700_: *mut LeanObject,
    mut v___f_701_: *mut LeanObject,
    mut v___x_702_: *mut LeanObject,
    mut v_type_703_: *mut LeanObject,
    mut v_semiringInst_704_: *mut LeanObject,
    mut v_n_705_: *mut LeanObject,
    mut v___f_706_: *mut LeanObject,
    mut v_____do__lift_707_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_707_) == 1 {
        let mut v_val_708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_706_);
        lean_dec_ref(v_n_705_);
        lean_dec_ref(v_semiringInst_704_);
        lean_dec_ref(v_type_703_);
        lean_dec(v___x_702_);
        v_val_708_ = lean_ctor_get(v_____do__lift_707_, 0);
        lean_inc(v_val_708_);
        lean_dec_ref_known(v_____do__lift_707_, 1);
        v___x_709_ = lean_apply_2(v_toPure_699_, lean_box(0), v_val_708_);
        v___x_710_ = lean_apply_4(
            v_toBind_700_,
            lean_box(0),
            lean_box(0),
            v___x_709_,
            v___f_701_,
        );
        return v___x_710_;
    } else {
        let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_707_);
        lean_dec(v___f_701_);
        v___x_711_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3;
        v___x_712_ = l_Lean_mkConst(v___x_711_, v___x_702_);
        v___x_713_ = l_Lean_mkApp3(v___x_712_, v_type_703_, v_semiringInst_704_, v_n_705_);
        v___x_714_ = lean_apply_2(v_toPure_699_, lean_box(0), v___x_713_);
        v___x_715_ = lean_apply_4(
            v_toBind_700_,
            lean_box(0),
            lean_box(0),
            v___x_714_,
            v___f_706_,
        );
        return v___x_715_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3(
    mut v_inst_719_: *mut LeanObject,
    mut v_k_720_: *mut LeanObject,
    mut v_toPure_721_: *mut LeanObject,
    mut v_inst_722_: *mut LeanObject,
    mut v_inst_723_: *mut LeanObject,
    mut v_inst_724_: *mut LeanObject,
    mut v_inst_725_: *mut LeanObject,
    mut v_toBind_726_: *mut LeanObject,
    mut v_ring_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthInstance_x3f_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v_synthInstance_x3f_728_ = lean_ctor_get(v_inst_719_, 1);
    lean_inc(v_synthInstance_x3f_728_);
    v_type_729_ = lean_ctor_get(v_ring_727_, 1);
    lean_inc_ref_n(v_type_729_, 3);
    v_u_730_ = lean_ctor_get(v_ring_727_, 2);
    lean_inc(v_u_730_);
    v_semiringInst_731_ = lean_ctor_get(v_ring_727_, 4);
    lean_inc_ref(v_semiringInst_731_);
    lean_dec_ref(v_ring_727_);
    v___x_732_ = lean_nat_abs(v_k_720_);
    v_n_733_ = l_Lean_mkRawNatLit(v___x_732_);
    v___x_734_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0;
    v___x_735_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1;
    v___x_736_ = lean_box(0);
    v___x_737_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_737_, 0, v_u_730_);
    lean_ctor_set(v___x_737_, 1, v___x_736_);
    lean_inc_n(v_toBind_726_, 2);
    lean_inc(v_toPure_721_);
    lean_inc_ref_n(v_n_733_, 2);
    lean_inc_ref_n(v___x_737_, 2);
    v___f_738_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_738_, 0, v___x_734_);
    lean_closure_set(v___f_738_, 1, v___x_737_);
    lean_closure_set(v___f_738_, 2, v_type_729_);
    lean_closure_set(v___f_738_, 3, v_n_733_);
    lean_closure_set(v___f_738_, 4, v_k_720_);
    lean_closure_set(v___f_738_, 5, v_toPure_721_);
    lean_closure_set(v___f_738_, 6, v_inst_722_);
    lean_closure_set(v___f_738_, 7, v_inst_723_);
    lean_closure_set(v___f_738_, 8, v_inst_724_);
    lean_closure_set(v___f_738_, 9, v_inst_719_);
    lean_closure_set(v___f_738_, 10, v_inst_725_);
    lean_closure_set(v___f_738_, 11, v_toBind_726_);
    v___f_739_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_739_, 0, v___f_738_);
    lean_inc_ref(v___f_739_);
    v___f_740_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_740_, 0, v_toPure_721_);
    lean_closure_set(v___f_740_, 1, v_toBind_726_);
    lean_closure_set(v___f_740_, 2, v___f_739_);
    lean_closure_set(v___f_740_, 3, v___x_737_);
    lean_closure_set(v___f_740_, 4, v_type_729_);
    lean_closure_set(v___f_740_, 5, v_semiringInst_731_);
    lean_closure_set(v___f_740_, 6, v_n_733_);
    lean_closure_set(v___f_740_, 7, v___f_739_);
    v___x_741_ = l_Lean_mkConst(v___x_735_, v___x_737_);
    v___x_742_ = l_Lean_mkAppB(v___x_741_, v_type_729_, v_n_733_);
    v___x_743_ = lean_apply_1(v_synthInstance_x3f_728_, v___x_742_);
    v___x_744_ = lean_apply_4(
        v_toBind_726_,
        lean_box(0),
        lean_box(0),
        v___x_743_,
        v___f_740_,
    );
    return v___x_744_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum___redArg(
    mut v_inst_745_: *mut LeanObject,
    mut v_inst_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
    mut v_inst_748_: *mut LeanObject,
    mut v_inst_749_: *mut LeanObject,
    mut v_k_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_751_ = lean_ctor_get(v_inst_745_, 0);
    v_toBind_752_ = lean_ctor_get(v_inst_745_, 1);
    lean_inc_n(v_toBind_752_, 2);
    v_getRing_753_ = lean_ctor_get(v_inst_749_, 0);
    lean_inc(v_getRing_753_);
    v_toPure_754_ = lean_ctor_get(v_toApplicative_751_, 1);
    lean_inc(v_toPure_754_);
    v___f_755_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_755_, 0, v_inst_748_);
    lean_closure_set(v___f_755_, 1, v_k_750_);
    lean_closure_set(v___f_755_, 2, v_toPure_754_);
    lean_closure_set(v___f_755_, 3, v_inst_747_);
    lean_closure_set(v___f_755_, 4, v_inst_746_);
    lean_closure_set(v___f_755_, 5, v_inst_745_);
    lean_closure_set(v___f_755_, 6, v_inst_749_);
    lean_closure_set(v___f_755_, 7, v_toBind_752_);
    v___x_756_ = lean_apply_4(
        v_toBind_752_,
        lean_box(0),
        lean_box(0),
        v_getRing_753_,
        v___f_755_,
    );
    return v___x_756_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteNum(
    mut v_m_757_: *mut LeanObject,
    mut v_inst_758_: *mut LeanObject,
    mut v_inst_759_: *mut LeanObject,
    mut v_inst_760_: *mut LeanObject,
    mut v_inst_761_: *mut LeanObject,
    mut v_inst_762_: *mut LeanObject,
    mut v_k_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
        v_inst_758_,
        v_inst_759_,
        v_inst_760_,
        v_inst_761_,
        v_inst_762_,
        v_k_763_,
    );
    return v___x_764_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0(
    mut v_toApplicative_765_: *mut LeanObject,
    mut v_k_766_: *mut LeanObject,
    mut v_x_767_: *mut LeanObject,
    mut v_____do__lift_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_769_ = lean_ctor_get(v_toApplicative_765_, 1);
    lean_inc(v_toPure_769_);
    lean_dec_ref(v_toApplicative_765_);
    v___x_770_ = l_Lean_mkNatLit(v_k_766_);
    v___x_771_ = l_Lean_mkAppB(v_____do__lift_768_, v_x_767_, v___x_770_);
    v___x_772_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1(
    mut v_k_773_: *mut LeanObject,
    mut v_toApplicative_774_: *mut LeanObject,
    mut v_inst_775_: *mut LeanObject,
    mut v_inst_776_: *mut LeanObject,
    mut v_inst_777_: *mut LeanObject,
    mut v_inst_778_: *mut LeanObject,
    mut v_inst_779_: *mut LeanObject,
    mut v_toBind_780_: *mut LeanObject,
    mut v_x_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    v___x_782_ = lean_unsigned_to_nat(1);
    v___x_783_ = lean_nat_dec_eq(v_k_773_, v___x_782_);
    if v___x_783_ == 0 {
        let mut v___f_784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
        v___f_784_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_784_, 0, v_toApplicative_774_);
        lean_closure_set(v___f_784_, 1, v_k_773_);
        lean_closure_set(v___f_784_, 2, v_x_781_);
        v___x_785_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(
            v_inst_775_,
            v_inst_776_,
            v_inst_777_,
            v_inst_778_,
            v_inst_779_,
        );
        v___x_786_ = lean_apply_4(
            v_toBind_780_,
            lean_box(0),
            lean_box(0),
            v___x_785_,
            v___f_784_,
        );
        return v___x_786_;
    } else {
        let mut v_toPure_787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_780_);
        lean_dec_ref(v_inst_779_);
        lean_dec_ref(v_inst_778_);
        lean_dec_ref(v_inst_777_);
        lean_dec_ref(v_inst_776_);
        lean_dec(v_inst_775_);
        lean_dec(v_k_773_);
        v_toPure_787_ = lean_ctor_get(v_toApplicative_774_, 1);
        lean_inc(v_toPure_787_);
        lean_dec_ref(v_toApplicative_774_);
        v___x_788_ = lean_apply_2(v_toPure_787_, lean_box(0), v_x_781_);
        return v___x_788_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePower___redArg(
    mut v_inst_789_: *mut LeanObject,
    mut v_inst_790_: *mut LeanObject,
    mut v_inst_791_: *mut LeanObject,
    mut v_inst_792_: *mut LeanObject,
    mut v_inst_793_: *mut LeanObject,
    mut v_inst_794_: *mut LeanObject,
    mut v_pw_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_796_ = lean_ctor_get(v_inst_789_, 0);
    lean_inc_ref(v_toApplicative_796_);
    v_toBind_797_ = lean_ctor_get(v_inst_789_, 1);
    lean_inc_n(v_toBind_797_, 2);
    v_x_798_ = lean_ctor_get(v_pw_795_, 0);
    lean_inc(v_x_798_);
    v_k_799_ = lean_ctor_get(v_pw_795_, 1);
    lean_inc(v_k_799_);
    lean_dec_ref(v_pw_795_);
    v___f_800_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_800_, 0, v_k_799_);
    lean_closure_set(v___f_800_, 1, v_toApplicative_796_);
    lean_closure_set(v___f_800_, 2, v_inst_791_);
    lean_closure_set(v___f_800_, 3, v_inst_790_);
    lean_closure_set(v___f_800_, 4, v_inst_789_);
    lean_closure_set(v___f_800_, 5, v_inst_792_);
    lean_closure_set(v___f_800_, 6, v_inst_793_);
    lean_closure_set(v___f_800_, 7, v_toBind_797_);
    v___x_801_ = lean_apply_1(v_inst_794_, v_x_798_);
    v___x_802_ = lean_apply_4(
        v_toBind_797_,
        lean_box(0),
        lean_box(0),
        v___x_801_,
        v___f_800_,
    );
    return v___x_802_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePower(
    mut v_m_803_: *mut LeanObject,
    mut v_inst_804_: *mut LeanObject,
    mut v_inst_805_: *mut LeanObject,
    mut v_inst_806_: *mut LeanObject,
    mut v_inst_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_inst_809_: *mut LeanObject,
    mut v_pw_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(
        v_inst_804_,
        v_inst_805_,
        v_inst_806_,
        v_inst_807_,
        v_inst_808_,
        v_inst_809_,
        v_pw_810_,
    );
    return v___x_811_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1(
    mut v_acc_812_: *mut LeanObject,
    mut v_inst_813_: *mut LeanObject,
    mut v_inst_814_: *mut LeanObject,
    mut v_inst_815_: *mut LeanObject,
    mut v_inst_816_: *mut LeanObject,
    mut v_inst_817_: *mut LeanObject,
    mut v_inst_818_: *mut LeanObject,
    mut v_m_819_: *mut LeanObject,
    mut v_p_820_: *mut LeanObject,
    mut v_toBind_821_: *mut LeanObject,
    mut v_____do__lift_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_818_);
    lean_inc_ref(v_inst_817_);
    lean_inc_ref(v_inst_816_);
    lean_inc(v_inst_815_);
    lean_inc_ref(v_inst_814_);
    lean_inc_ref(v_inst_813_);
    v___f_823_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0 as *mut core::ffi::c_void, 10, 9);
    lean_closure_set(v___f_823_, 0, v_____do__lift_822_);
    lean_closure_set(v___f_823_, 1, v_acc_812_);
    lean_closure_set(v___f_823_, 2, v_inst_813_);
    lean_closure_set(v___f_823_, 3, v_inst_814_);
    lean_closure_set(v___f_823_, 4, v_inst_815_);
    lean_closure_set(v___f_823_, 5, v_inst_816_);
    lean_closure_set(v___f_823_, 6, v_inst_817_);
    lean_closure_set(v___f_823_, 7, v_inst_818_);
    lean_closure_set(v___f_823_, 8, v_m_819_);
    v___x_824_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(
        v_inst_813_,
        v_inst_814_,
        v_inst_815_,
        v_inst_816_,
        v_inst_817_,
        v_inst_818_,
        v_p_820_,
    );
    v___x_825_ = lean_apply_4(
        v_toBind_821_,
        lean_box(0),
        lean_box(0),
        v___x_824_,
        v___f_823_,
    );
    return v___x_825_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(
    mut v_inst_826_: *mut LeanObject,
    mut v_inst_827_: *mut LeanObject,
    mut v_inst_828_: *mut LeanObject,
    mut v_inst_829_: *mut LeanObject,
    mut v_inst_830_: *mut LeanObject,
    mut v_inst_831_: *mut LeanObject,
    mut v_mn_832_: *mut LeanObject,
    mut v_acc_833_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_mn_832_) == 0 {
        let mut v_toApplicative_834_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_834_ = lean_ctor_get(v_inst_826_, 0);
        lean_inc_ref(v_toApplicative_834_);
        lean_dec(v_inst_831_);
        lean_dec_ref(v_inst_830_);
        lean_dec_ref(v_inst_829_);
        lean_dec(v_inst_828_);
        lean_dec_ref(v_inst_827_);
        lean_dec_ref(v_inst_826_);
        v_toPure_835_ = lean_ctor_get(v_toApplicative_834_, 1);
        lean_inc(v_toPure_835_);
        lean_dec_ref(v_toApplicative_834_);
        v___x_836_ = lean_apply_2(v_toPure_835_, lean_box(0), v_acc_833_);
        return v___x_836_;
    } else {
        let mut v_toBind_837_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_838_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_837_ = lean_ctor_get(v_inst_826_, 1);
        lean_inc_n(v_toBind_837_, 2);
        v_p_838_ = lean_ctor_get(v_mn_832_, 0);
        lean_inc_ref(v_p_838_);
        v_m_839_ = lean_ctor_get(v_mn_832_, 1);
        lean_inc(v_m_839_);
        lean_dec_ref_known(v_mn_832_, 2);
        lean_inc_ref(v_inst_830_);
        lean_inc_ref(v_inst_829_);
        lean_inc(v_inst_828_);
        lean_inc_ref(v_inst_827_);
        lean_inc_ref(v_inst_826_);
        v___f_840_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1 as *mut core::ffi::c_void, 11, 10);
        lean_closure_set(v___f_840_, 0, v_acc_833_);
        lean_closure_set(v___f_840_, 1, v_inst_826_);
        lean_closure_set(v___f_840_, 2, v_inst_827_);
        lean_closure_set(v___f_840_, 3, v_inst_828_);
        lean_closure_set(v___f_840_, 4, v_inst_829_);
        lean_closure_set(v___f_840_, 5, v_inst_830_);
        lean_closure_set(v___f_840_, 6, v_inst_831_);
        lean_closure_set(v___f_840_, 7, v_m_839_);
        lean_closure_set(v___f_840_, 8, v_p_838_);
        lean_closure_set(v___f_840_, 9, v_toBind_837_);
        v___x_841_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
            v_inst_828_,
            v_inst_827_,
            v_inst_826_,
            v_inst_829_,
            v_inst_830_,
        );
        v___x_842_ = lean_apply_4(
            v_toBind_837_,
            lean_box(0),
            lean_box(0),
            v___x_841_,
            v___f_840_,
        );
        return v___x_842_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0(
    mut v_____do__lift_843_: *mut LeanObject,
    mut v_acc_844_: *mut LeanObject,
    mut v_inst_845_: *mut LeanObject,
    mut v_inst_846_: *mut LeanObject,
    mut v_inst_847_: *mut LeanObject,
    mut v_inst_848_: *mut LeanObject,
    mut v_inst_849_: *mut LeanObject,
    mut v_inst_850_: *mut LeanObject,
    mut v_m_851_: *mut LeanObject,
    mut v_____do__lift_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Lean_mkAppB(v_____do__lift_843_, v_acc_844_, v_____do__lift_852_);
    v___x_854_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(
            v_inst_845_,
            v_inst_846_,
            v_inst_847_,
            v_inst_848_,
            v_inst_849_,
            v_inst_850_,
            v_m_851_,
            v___x_853_,
        );
    return v___x_854_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go(
    mut v_m_855_: *mut LeanObject,
    mut v_inst_856_: *mut LeanObject,
    mut v_inst_857_: *mut LeanObject,
    mut v_inst_858_: *mut LeanObject,
    mut v_inst_859_: *mut LeanObject,
    mut v_inst_860_: *mut LeanObject,
    mut v_inst_861_: *mut LeanObject,
    mut v_mn_862_: *mut LeanObject,
    mut v_acc_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(
            v_inst_856_,
            v_inst_857_,
            v_inst_858_,
            v_inst_859_,
            v_inst_860_,
            v_inst_861_,
            v_mn_862_,
            v_acc_863_,
        );
    return v___x_864_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0(
    mut v_inst_865_: *mut LeanObject,
    mut v_inst_866_: *mut LeanObject,
    mut v_inst_867_: *mut LeanObject,
    mut v_inst_868_: *mut LeanObject,
    mut v_inst_869_: *mut LeanObject,
    mut v_inst_870_: *mut LeanObject,
    mut v_m_871_: *mut LeanObject,
    mut v_____do__lift_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    v___x_873_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(
            v_inst_865_,
            v_inst_866_,
            v_inst_867_,
            v_inst_868_,
            v_inst_869_,
            v_inst_870_,
            v_m_871_,
            v_____do__lift_872_,
        );
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ = lean_unsigned_to_nat(1);
    v___x_875_ = lean_nat_to_int(v___x_874_);
    return v___x_875_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteMon___redArg(
    mut v_inst_876_: *mut LeanObject,
    mut v_inst_877_: *mut LeanObject,
    mut v_inst_878_: *mut LeanObject,
    mut v_inst_879_: *mut LeanObject,
    mut v_inst_880_: *mut LeanObject,
    mut v_inst_881_: *mut LeanObject,
    mut v_mn_882_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_mn_882_) == 0 {
        let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_881_);
        v___x_883_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once),
            _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0,
        );
        v___x_884_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
            v_inst_876_,
            v_inst_877_,
            v_inst_878_,
            v_inst_879_,
            v_inst_880_,
            v___x_883_,
        );
        return v___x_884_;
    } else {
        let mut v_toBind_885_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_886_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_885_ = lean_ctor_get(v_inst_876_, 1);
        lean_inc(v_toBind_885_);
        v_p_886_ = lean_ctor_get(v_mn_882_, 0);
        lean_inc_ref(v_p_886_);
        v_m_887_ = lean_ctor_get(v_mn_882_, 1);
        lean_inc(v_m_887_);
        lean_dec_ref_known(v_mn_882_, 2);
        lean_inc(v_inst_881_);
        lean_inc_ref(v_inst_880_);
        lean_inc_ref(v_inst_879_);
        lean_inc(v_inst_878_);
        lean_inc_ref(v_inst_877_);
        lean_inc_ref(v_inst_876_);
        v___f_888_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0 as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_888_, 0, v_inst_876_);
        lean_closure_set(v___f_888_, 1, v_inst_877_);
        lean_closure_set(v___f_888_, 2, v_inst_878_);
        lean_closure_set(v___f_888_, 3, v_inst_879_);
        lean_closure_set(v___f_888_, 4, v_inst_880_);
        lean_closure_set(v___f_888_, 5, v_inst_881_);
        lean_closure_set(v___f_888_, 6, v_m_887_);
        v___x_889_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(
            v_inst_876_,
            v_inst_877_,
            v_inst_878_,
            v_inst_879_,
            v_inst_880_,
            v_inst_881_,
            v_p_886_,
        );
        v___x_890_ = lean_apply_4(
            v_toBind_885_,
            lean_box(0),
            lean_box(0),
            v___x_889_,
            v___f_888_,
        );
        return v___x_890_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteMon(
    mut v_m_891_: *mut LeanObject,
    mut v_inst_892_: *mut LeanObject,
    mut v_inst_893_: *mut LeanObject,
    mut v_inst_894_: *mut LeanObject,
    mut v_inst_895_: *mut LeanObject,
    mut v_inst_896_: *mut LeanObject,
    mut v_inst_897_: *mut LeanObject,
    mut v_mn_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(
        v_inst_892_,
        v_inst_893_,
        v_inst_894_,
        v_inst_895_,
        v_inst_896_,
        v_inst_897_,
        v_mn_898_,
    );
    return v___x_899_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0(
    mut v_toApplicative_900_: *mut LeanObject,
    mut v_____do__lift_901_: *mut LeanObject,
    mut v_____do__lift_902_: *mut LeanObject,
    mut v_____do__lift_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_904_ = lean_ctor_get(v_toApplicative_900_, 1);
    lean_inc(v_toPure_904_);
    lean_dec_ref(v_toApplicative_900_);
    v___x_905_ = l_Lean_mkAppB(
        v_____do__lift_901_,
        v_____do__lift_902_,
        v_____do__lift_903_,
    );
    v___x_906_ = lean_apply_2(v_toPure_904_, lean_box(0), v___x_905_);
    return v___x_906_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1(
    mut v_toApplicative_907_: *mut LeanObject,
    mut v_____do__lift_908_: *mut LeanObject,
    mut v_inst_909_: *mut LeanObject,
    mut v_inst_910_: *mut LeanObject,
    mut v_inst_911_: *mut LeanObject,
    mut v_inst_912_: *mut LeanObject,
    mut v_inst_913_: *mut LeanObject,
    mut v_inst_914_: *mut LeanObject,
    mut v_mn_915_: *mut LeanObject,
    mut v_toBind_916_: *mut LeanObject,
    mut v_____do__lift_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___f_918_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___f_918_, 0, v_toApplicative_907_);
    lean_closure_set(v___f_918_, 1, v_____do__lift_908_);
    lean_closure_set(v___f_918_, 2, v_____do__lift_917_);
    v___x_919_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(
        v_inst_909_,
        v_inst_910_,
        v_inst_911_,
        v_inst_912_,
        v_inst_913_,
        v_inst_914_,
        v_mn_915_,
    );
    v___x_920_ = lean_apply_4(
        v_toBind_916_,
        lean_box(0),
        lean_box(0),
        v___x_919_,
        v___f_918_,
    );
    return v___x_920_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2(
    mut v_toApplicative_921_: *mut LeanObject,
    mut v_inst_922_: *mut LeanObject,
    mut v_inst_923_: *mut LeanObject,
    mut v_inst_924_: *mut LeanObject,
    mut v_inst_925_: *mut LeanObject,
    mut v_inst_926_: *mut LeanObject,
    mut v_inst_927_: *mut LeanObject,
    mut v_mn_928_: *mut LeanObject,
    mut v_toBind_929_: *mut LeanObject,
    mut v_k_930_: *mut LeanObject,
    mut v_____do__lift_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_929_);
    lean_inc_ref(v_inst_926_);
    lean_inc_ref(v_inst_925_);
    lean_inc(v_inst_924_);
    lean_inc_ref(v_inst_923_);
    lean_inc_ref(v_inst_922_);
    v___f_932_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1 as *mut core::ffi::c_void, 11, 10);
    lean_closure_set(v___f_932_, 0, v_toApplicative_921_);
    lean_closure_set(v___f_932_, 1, v_____do__lift_931_);
    lean_closure_set(v___f_932_, 2, v_inst_922_);
    lean_closure_set(v___f_932_, 3, v_inst_923_);
    lean_closure_set(v___f_932_, 4, v_inst_924_);
    lean_closure_set(v___f_932_, 5, v_inst_925_);
    lean_closure_set(v___f_932_, 6, v_inst_926_);
    lean_closure_set(v___f_932_, 7, v_inst_927_);
    lean_closure_set(v___f_932_, 8, v_mn_928_);
    lean_closure_set(v___f_932_, 9, v_toBind_929_);
    v___x_933_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
        v_inst_922_,
        v_inst_923_,
        v_inst_924_,
        v_inst_925_,
        v_inst_926_,
        v_k_930_,
    );
    v___x_934_ = lean_apply_4(
        v_toBind_929_,
        lean_box(0),
        lean_box(0),
        v___x_933_,
        v___f_932_,
    );
    return v___x_934_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(
    mut v_inst_935_: *mut LeanObject,
    mut v_inst_936_: *mut LeanObject,
    mut v_inst_937_: *mut LeanObject,
    mut v_inst_938_: *mut LeanObject,
    mut v_inst_939_: *mut LeanObject,
    mut v_inst_940_: *mut LeanObject,
    mut v_k_941_: *mut LeanObject,
    mut v_mn_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: u8 = 0;
    v___x_943_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once),
        _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0,
    );
    v___x_944_ = lean_int_dec_eq(v_k_941_, v___x_943_);
    if v___x_944_ == 0 {
        let mut v_toApplicative_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_945_ = lean_ctor_get(v_inst_935_, 0);
        v_toBind_946_ = lean_ctor_get(v_inst_935_, 1);
        lean_inc_n(v_toBind_946_, 2);
        lean_inc_ref(v_inst_939_);
        lean_inc_ref(v_inst_938_);
        lean_inc(v_inst_937_);
        lean_inc_ref(v_inst_936_);
        lean_inc_ref(v_inst_935_);
        lean_inc_ref(v_toApplicative_945_);
        v___f_947_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2 as *mut core::ffi::c_void, 11, 10);
        lean_closure_set(v___f_947_, 0, v_toApplicative_945_);
        lean_closure_set(v___f_947_, 1, v_inst_935_);
        lean_closure_set(v___f_947_, 2, v_inst_936_);
        lean_closure_set(v___f_947_, 3, v_inst_937_);
        lean_closure_set(v___f_947_, 4, v_inst_938_);
        lean_closure_set(v___f_947_, 5, v_inst_939_);
        lean_closure_set(v___f_947_, 6, v_inst_940_);
        lean_closure_set(v___f_947_, 7, v_mn_942_);
        lean_closure_set(v___f_947_, 8, v_toBind_946_);
        lean_closure_set(v___f_947_, 9, v_k_941_);
        v___x_948_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
            v_inst_937_,
            v_inst_936_,
            v_inst_935_,
            v_inst_938_,
            v_inst_939_,
        );
        v___x_949_ = lean_apply_4(
            v_toBind_946_,
            lean_box(0),
            lean_box(0),
            v___x_948_,
            v___f_947_,
        );
        return v___x_949_;
    } else {
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_941_);
        v___x_950_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(
            v_inst_935_,
            v_inst_936_,
            v_inst_937_,
            v_inst_938_,
            v_inst_939_,
            v_inst_940_,
            v_mn_942_,
        );
        return v___x_950_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm(
    mut v_m_951_: *mut LeanObject,
    mut v_inst_952_: *mut LeanObject,
    mut v_inst_953_: *mut LeanObject,
    mut v_inst_954_: *mut LeanObject,
    mut v_inst_955_: *mut LeanObject,
    mut v_inst_956_: *mut LeanObject,
    mut v_inst_957_: *mut LeanObject,
    mut v_k_958_: *mut LeanObject,
    mut v_mn_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    v___x_960_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_952_, v_inst_953_, v_inst_954_, v_inst_955_, v_inst_956_, v_inst_957_, v_k_958_, v_mn_959_);
    return v___x_960_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0(
    mut v_____do__lift_961_: *mut LeanObject,
    mut v_acc_962_: *mut LeanObject,
    mut v_toPure_963_: *mut LeanObject,
    mut v_____do__lift_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = l_Lean_mkAppB(v_____do__lift_961_, v_acc_962_, v_____do__lift_964_);
    v___x_966_ = lean_apply_2(v_toPure_963_, lean_box(0), v___x_965_);
    return v___x_966_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1(
    mut v_acc_967_: *mut LeanObject,
    mut v_toPure_968_: *mut LeanObject,
    mut v_inst_969_: *mut LeanObject,
    mut v_inst_970_: *mut LeanObject,
    mut v_inst_971_: *mut LeanObject,
    mut v_inst_972_: *mut LeanObject,
    mut v_inst_973_: *mut LeanObject,
    mut v_k_974_: *mut LeanObject,
    mut v_toBind_975_: *mut LeanObject,
    mut v_____do__lift_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    v___f_977_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___f_977_, 0, v_____do__lift_976_);
    lean_closure_set(v___f_977_, 1, v_acc_967_);
    lean_closure_set(v___f_977_, 2, v_toPure_968_);
    v___x_978_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
        v_inst_969_,
        v_inst_970_,
        v_inst_971_,
        v_inst_972_,
        v_inst_973_,
        v_k_974_,
    );
    v___x_979_ = lean_apply_4(
        v_toBind_975_,
        lean_box(0),
        lean_box(0),
        v___x_978_,
        v___f_977_,
    );
    return v___x_979_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3(
    mut v_acc_980_: *mut LeanObject,
    mut v_inst_981_: *mut LeanObject,
    mut v_inst_982_: *mut LeanObject,
    mut v_inst_983_: *mut LeanObject,
    mut v_inst_984_: *mut LeanObject,
    mut v_inst_985_: *mut LeanObject,
    mut v_inst_986_: *mut LeanObject,
    mut v_p_987_: *mut LeanObject,
    mut v_k_988_: *mut LeanObject,
    mut v_v_989_: *mut LeanObject,
    mut v_toBind_990_: *mut LeanObject,
    mut v_____do__lift_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_986_);
    lean_inc_ref(v_inst_985_);
    lean_inc_ref(v_inst_984_);
    lean_inc(v_inst_983_);
    lean_inc_ref(v_inst_982_);
    lean_inc_ref(v_inst_981_);
    v___f_992_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2 as *mut core::ffi::c_void, 10, 9);
    lean_closure_set(v___f_992_, 0, v_____do__lift_991_);
    lean_closure_set(v___f_992_, 1, v_acc_980_);
    lean_closure_set(v___f_992_, 2, v_inst_981_);
    lean_closure_set(v___f_992_, 3, v_inst_982_);
    lean_closure_set(v___f_992_, 4, v_inst_983_);
    lean_closure_set(v___f_992_, 5, v_inst_984_);
    lean_closure_set(v___f_992_, 6, v_inst_985_);
    lean_closure_set(v___f_992_, 7, v_inst_986_);
    lean_closure_set(v___f_992_, 8, v_p_987_);
    v___x_993_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_981_, v_inst_982_, v_inst_983_, v_inst_984_, v_inst_985_, v_inst_986_, v_k_988_, v_v_989_);
    v___x_994_ = lean_apply_4(
        v_toBind_990_,
        lean_box(0),
        lean_box(0),
        v___x_993_,
        v___f_992_,
    );
    return v___x_994_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(
    mut v_inst_995_: *mut LeanObject,
    mut v_inst_996_: *mut LeanObject,
    mut v_inst_997_: *mut LeanObject,
    mut v_inst_998_: *mut LeanObject,
    mut v_inst_999_: *mut LeanObject,
    mut v_inst_1000_: *mut LeanObject,
    mut v_p_1001_: *mut LeanObject,
    mut v_acc_1002_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_1001_) == 0 {
        let mut v_toApplicative_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_toApplicative_1003_ = lean_ctor_get(v_inst_995_, 0);
        lean_dec(v_inst_1000_);
        v_toBind_1004_ = lean_ctor_get(v_inst_995_, 1);
        lean_inc(v_toBind_1004_);
        v_toPure_1005_ = lean_ctor_get(v_toApplicative_1003_, 1);
        v_k_1006_ = lean_ctor_get(v_p_1001_, 0);
        lean_inc(v_k_1006_);
        lean_dec_ref_known(v_p_1001_, 1);
        v___x_1007_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1,
        );
        v___x_1008_ = lean_int_dec_eq(v_k_1006_, v___x_1007_);
        if v___x_1008_ == 0 {
            let mut v___f_1009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toBind_1004_);
            lean_inc_ref(v_inst_999_);
            lean_inc_ref(v_inst_998_);
            lean_inc(v_inst_997_);
            lean_inc_ref(v_inst_996_);
            lean_inc_ref(v_inst_995_);
            lean_inc(v_toPure_1005_);
            v___f_1009_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
            lean_closure_set(v___f_1009_, 0, v_acc_1002_);
            lean_closure_set(v___f_1009_, 1, v_toPure_1005_);
            lean_closure_set(v___f_1009_, 2, v_inst_995_);
            lean_closure_set(v___f_1009_, 3, v_inst_996_);
            lean_closure_set(v___f_1009_, 4, v_inst_997_);
            lean_closure_set(v___f_1009_, 5, v_inst_998_);
            lean_closure_set(v___f_1009_, 6, v_inst_999_);
            lean_closure_set(v___f_1009_, 7, v_k_1006_);
            lean_closure_set(v___f_1009_, 8, v_toBind_1004_);
            v___x_1010_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
                v_inst_997_,
                v_inst_996_,
                v_inst_995_,
                v_inst_998_,
                v_inst_999_,
            );
            v___x_1011_ = lean_apply_4(
                v_toBind_1004_,
                lean_box(0),
                lean_box(0),
                v___x_1010_,
                v___f_1009_,
            );
            return v___x_1011_;
        } else {
            let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toPure_1005_);
            lean_dec(v_k_1006_);
            lean_dec(v_toBind_1004_);
            lean_dec_ref(v_inst_999_);
            lean_dec_ref(v_inst_998_);
            lean_dec(v_inst_997_);
            lean_dec_ref(v_inst_996_);
            lean_dec_ref(v_inst_995_);
            v___x_1012_ = lean_apply_2(v_toPure_1005_, lean_box(0), v_acc_1002_);
            return v___x_1012_;
        }
    } else {
        let mut v_toBind_1013_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1014_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1015_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1013_ = lean_ctor_get(v_inst_995_, 1);
        lean_inc_n(v_toBind_1013_, 2);
        v_k_1014_ = lean_ctor_get(v_p_1001_, 0);
        lean_inc(v_k_1014_);
        v_v_1015_ = lean_ctor_get(v_p_1001_, 1);
        lean_inc(v_v_1015_);
        v_p_1016_ = lean_ctor_get(v_p_1001_, 2);
        lean_inc_ref(v_p_1016_);
        lean_dec_ref_known(v_p_1001_, 3);
        lean_inc_ref(v_inst_999_);
        lean_inc_ref(v_inst_998_);
        lean_inc(v_inst_997_);
        lean_inc_ref(v_inst_996_);
        lean_inc_ref(v_inst_995_);
        v___f_1017_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3 as *mut core::ffi::c_void, 12, 11);
        lean_closure_set(v___f_1017_, 0, v_acc_1002_);
        lean_closure_set(v___f_1017_, 1, v_inst_995_);
        lean_closure_set(v___f_1017_, 2, v_inst_996_);
        lean_closure_set(v___f_1017_, 3, v_inst_997_);
        lean_closure_set(v___f_1017_, 4, v_inst_998_);
        lean_closure_set(v___f_1017_, 5, v_inst_999_);
        lean_closure_set(v___f_1017_, 6, v_inst_1000_);
        lean_closure_set(v___f_1017_, 7, v_p_1016_);
        lean_closure_set(v___f_1017_, 8, v_k_1014_);
        lean_closure_set(v___f_1017_, 9, v_v_1015_);
        lean_closure_set(v___f_1017_, 10, v_toBind_1013_);
        v___x_1018_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
            v_inst_997_,
            v_inst_996_,
            v_inst_995_,
            v_inst_998_,
            v_inst_999_,
        );
        v___x_1019_ = lean_apply_4(
            v_toBind_1013_,
            lean_box(0),
            lean_box(0),
            v___x_1018_,
            v___f_1017_,
        );
        return v___x_1019_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2(
    mut v_____do__lift_1020_: *mut LeanObject,
    mut v_acc_1021_: *mut LeanObject,
    mut v_inst_1022_: *mut LeanObject,
    mut v_inst_1023_: *mut LeanObject,
    mut v_inst_1024_: *mut LeanObject,
    mut v_inst_1025_: *mut LeanObject,
    mut v_inst_1026_: *mut LeanObject,
    mut v_inst_1027_: *mut LeanObject,
    mut v_p_1028_: *mut LeanObject,
    mut v_____do__lift_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = l_Lean_mkAppB(v_____do__lift_1020_, v_acc_1021_, v_____do__lift_1029_);
    v___x_1031_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(
            v_inst_1022_,
            v_inst_1023_,
            v_inst_1024_,
            v_inst_1025_,
            v_inst_1026_,
            v_inst_1027_,
            v_p_1028_,
            v___x_1030_,
        );
    return v___x_1031_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go(
    mut v_m_1032_: *mut LeanObject,
    mut v_inst_1033_: *mut LeanObject,
    mut v_inst_1034_: *mut LeanObject,
    mut v_inst_1035_: *mut LeanObject,
    mut v_inst_1036_: *mut LeanObject,
    mut v_inst_1037_: *mut LeanObject,
    mut v_inst_1038_: *mut LeanObject,
    mut v_p_1039_: *mut LeanObject,
    mut v_acc_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    v___x_1041_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(
            v_inst_1033_,
            v_inst_1034_,
            v_inst_1035_,
            v_inst_1036_,
            v_inst_1037_,
            v_inst_1038_,
            v_p_1039_,
            v_acc_1040_,
        );
    return v___x_1041_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0(
    mut v_inst_1042_: *mut LeanObject,
    mut v_inst_1043_: *mut LeanObject,
    mut v_inst_1044_: *mut LeanObject,
    mut v_inst_1045_: *mut LeanObject,
    mut v_inst_1046_: *mut LeanObject,
    mut v_inst_1047_: *mut LeanObject,
    mut v_p_1048_: *mut LeanObject,
    mut v_____do__lift_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1050_ =
        l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(
            v_inst_1042_,
            v_inst_1043_,
            v_inst_1044_,
            v_inst_1045_,
            v_inst_1046_,
            v_inst_1047_,
            v_p_1048_,
            v_____do__lift_1049_,
        );
    return v___x_1050_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePoly___redArg(
    mut v_inst_1051_: *mut LeanObject,
    mut v_inst_1052_: *mut LeanObject,
    mut v_inst_1053_: *mut LeanObject,
    mut v_inst_1054_: *mut LeanObject,
    mut v_inst_1055_: *mut LeanObject,
    mut v_inst_1056_: *mut LeanObject,
    mut v_p_1057_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_1057_) == 0 {
        let mut v_k_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1056_);
        v_k_1058_ = lean_ctor_get(v_p_1057_, 0);
        lean_inc(v_k_1058_);
        lean_dec_ref_known(v_p_1057_, 1);
        v___x_1059_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
            v_inst_1051_,
            v_inst_1052_,
            v_inst_1053_,
            v_inst_1054_,
            v_inst_1055_,
            v_k_1058_,
        );
        return v___x_1059_;
    } else {
        let mut v_toBind_1060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1062_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1060_ = lean_ctor_get(v_inst_1051_, 1);
        lean_inc(v_toBind_1060_);
        v_k_1061_ = lean_ctor_get(v_p_1057_, 0);
        lean_inc(v_k_1061_);
        v_v_1062_ = lean_ctor_get(v_p_1057_, 1);
        lean_inc(v_v_1062_);
        v_p_1063_ = lean_ctor_get(v_p_1057_, 2);
        lean_inc_ref(v_p_1063_);
        lean_dec_ref_known(v_p_1057_, 3);
        lean_inc(v_inst_1056_);
        lean_inc_ref(v_inst_1055_);
        lean_inc_ref(v_inst_1054_);
        lean_inc(v_inst_1053_);
        lean_inc_ref(v_inst_1052_);
        lean_inc_ref(v_inst_1051_);
        v___f_1064_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0 as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_1064_, 0, v_inst_1051_);
        lean_closure_set(v___f_1064_, 1, v_inst_1052_);
        lean_closure_set(v___f_1064_, 2, v_inst_1053_);
        lean_closure_set(v___f_1064_, 3, v_inst_1054_);
        lean_closure_set(v___f_1064_, 4, v_inst_1055_);
        lean_closure_set(v___f_1064_, 5, v_inst_1056_);
        lean_closure_set(v___f_1064_, 6, v_p_1063_);
        v___x_1065_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_1051_, v_inst_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_, v_inst_1056_, v_k_1061_, v_v_1062_);
        v___x_1066_ = lean_apply_4(
            v_toBind_1060_,
            lean_box(0),
            lean_box(0),
            v___x_1065_,
            v___f_1064_,
        );
        return v___x_1066_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denotePoly(
    mut v_m_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_inst_1069_: *mut LeanObject,
    mut v_inst_1070_: *mut LeanObject,
    mut v_inst_1071_: *mut LeanObject,
    mut v_inst_1072_: *mut LeanObject,
    mut v_inst_1073_: *mut LeanObject,
    mut v_p_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lean_Meta_Sym_Arith_denotePoly___redArg(
        v_inst_1068_,
        v_inst_1069_,
        v_inst_1070_,
        v_inst_1071_,
        v_inst_1072_,
        v_inst_1073_,
        v_p_1074_,
    );
    return v___x_1075_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0(
    mut v_k_1076_: *mut LeanObject,
    mut v_toPure_1077_: *mut LeanObject,
    mut v_____do__lift_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1079_ = l_Lean_mkNatLit(v_k_1076_);
    v___x_1080_ = l_Lean_Expr_app___override(v_____do__lift_1078_, v___x_1079_);
    v___x_1081_ = lean_apply_2(v_toPure_1077_, lean_box(0), v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(
    mut v_k_1082_: *mut LeanObject,
    mut v_toPure_1083_: *mut LeanObject,
    mut v_____do__lift_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_mkIntLit(v_k_1082_);
    v___x_1086_ = l_Lean_Expr_app___override(v_____do__lift_1084_, v___x_1085_);
    v___x_1087_ = lean_apply_2(v_toPure_1083_, lean_box(0), v___x_1086_);
    return v___x_1087_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed(
    mut v_k_1088_: *mut LeanObject,
    mut v_toPure_1089_: *mut LeanObject,
    mut v_____do__lift_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1091_: *mut LeanObject = core::ptr::null_mut();
    v_res_1091_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(v_k_1088_, v_toPure_1089_, v_____do__lift_1090_);
    lean_dec(v_k_1088_);
    return v_res_1091_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2(
    mut v_____do__lift_1092_: *mut LeanObject,
    mut v_toPure_1093_: *mut LeanObject,
    mut v_____do__lift_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v___x_1095_ = l_Lean_Expr_app___override(v_____do__lift_1092_, v_____do__lift_1094_);
    v___x_1096_ = lean_apply_2(v_toPure_1093_, lean_box(0), v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4(
    mut v_____do__lift_1097_: *mut LeanObject,
    mut v_____do__lift_1098_: *mut LeanObject,
    mut v_toPure_1099_: *mut LeanObject,
    mut v_____do__lift_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_mkAppB(
        v_____do__lift_1097_,
        v_____do__lift_1098_,
        v_____do__lift_1100_,
    );
    v___x_1102_ = lean_apply_2(v_toPure_1099_, lean_box(0), v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__13(
    mut v_k_1103_: *mut LeanObject,
    mut v_____do__lift_1104_: *mut LeanObject,
    mut v_toPure_1105_: *mut LeanObject,
    mut v_____do__lift_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lean_mkNatLit(v_k_1103_);
    v___x_1108_ = l_Lean_mkAppB(v_____do__lift_1104_, v_____do__lift_1106_, v___x_1107_);
    v___x_1109_ = lean_apply_2(v_toPure_1105_, lean_box(0), v___x_1108_);
    return v___x_1109_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5(
    mut v_____do__lift_1110_: *mut LeanObject,
    mut v_toPure_1111_: *mut LeanObject,
    mut v_inst_1112_: *mut LeanObject,
    mut v_inst_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_inst_1116_: *mut LeanObject,
    mut v_getVarExpr_1117_: *mut LeanObject,
    mut v_b_1118_: *mut LeanObject,
    mut v_toBind_1119_: *mut LeanObject,
    mut v_____do__lift_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___f_1121_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4 as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___f_1121_, 0, v_____do__lift_1110_);
    lean_closure_set(v___f_1121_, 1, v_____do__lift_1120_);
    lean_closure_set(v___f_1121_, 2, v_toPure_1111_);
    v___x_1122_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1112_, v_inst_1113_, v_inst_1114_, v_inst_1115_, v_inst_1116_, v_getVarExpr_1117_, v_b_1118_);
    v___x_1123_ = lean_apply_4(
        v_toBind_1119_,
        lean_box(0),
        lean_box(0),
        v___x_1122_,
        v___f_1121_,
    );
    return v___x_1123_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6(
    mut v_toPure_1124_: *mut LeanObject,
    mut v_inst_1125_: *mut LeanObject,
    mut v_inst_1126_: *mut LeanObject,
    mut v_inst_1127_: *mut LeanObject,
    mut v_inst_1128_: *mut LeanObject,
    mut v_inst_1129_: *mut LeanObject,
    mut v_getVarExpr_1130_: *mut LeanObject,
    mut v_b_1131_: *mut LeanObject,
    mut v_toBind_1132_: *mut LeanObject,
    mut v_a_1133_: *mut LeanObject,
    mut v_____do__lift_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_1132_);
    lean_inc_ref(v_getVarExpr_1130_);
    lean_inc_ref(v_inst_1129_);
    lean_inc_ref(v_inst_1128_);
    lean_inc(v_inst_1127_);
    lean_inc_ref(v_inst_1126_);
    lean_inc_ref(v_inst_1125_);
    v___f_1135_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5 as *mut core::ffi::c_void, 11, 10);
    lean_closure_set(v___f_1135_, 0, v_____do__lift_1134_);
    lean_closure_set(v___f_1135_, 1, v_toPure_1124_);
    lean_closure_set(v___f_1135_, 2, v_inst_1125_);
    lean_closure_set(v___f_1135_, 3, v_inst_1126_);
    lean_closure_set(v___f_1135_, 4, v_inst_1127_);
    lean_closure_set(v___f_1135_, 5, v_inst_1128_);
    lean_closure_set(v___f_1135_, 6, v_inst_1129_);
    lean_closure_set(v___f_1135_, 7, v_getVarExpr_1130_);
    lean_closure_set(v___f_1135_, 8, v_b_1131_);
    lean_closure_set(v___f_1135_, 9, v_toBind_1132_);
    v___x_1136_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_getVarExpr_1130_, v_a_1133_);
    v___x_1137_ = lean_apply_4(
        v_toBind_1132_,
        lean_box(0),
        lean_box(0),
        v___x_1136_,
        v___f_1135_,
    );
    return v___x_1137_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__7(
    mut v_k_1138_: *mut LeanObject,
    mut v_toPure_1139_: *mut LeanObject,
    mut v_inst_1140_: *mut LeanObject,
    mut v_inst_1141_: *mut LeanObject,
    mut v_inst_1142_: *mut LeanObject,
    mut v_inst_1143_: *mut LeanObject,
    mut v_inst_1144_: *mut LeanObject,
    mut v_getVarExpr_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_toBind_1147_: *mut LeanObject,
    mut v_____do__lift_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___f_1149_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__13 as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___f_1149_, 0, v_k_1138_);
    lean_closure_set(v___f_1149_, 1, v_____do__lift_1148_);
    lean_closure_set(v___f_1149_, 2, v_toPure_1139_);
    v___x_1150_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1140_, v_inst_1141_, v_inst_1142_, v_inst_1143_, v_inst_1144_, v_getVarExpr_1145_, v_a_1146_);
    v___x_1151_ = lean_apply_4(
        v_toBind_1147_,
        lean_box(0),
        lean_box(0),
        v___x_1150_,
        v___f_1149_,
    );
    return v___x_1151_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(
    mut v_inst_1152_: *mut LeanObject,
    mut v_inst_1153_: *mut LeanObject,
    mut v_inst_1154_: *mut LeanObject,
    mut v_inst_1155_: *mut LeanObject,
    mut v_inst_1156_: *mut LeanObject,
    mut v_getVarExpr_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_1158_) {
        0 => {
            let mut v_k_1159_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_getVarExpr_1157_);
            v_k_1159_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc(v_k_1159_);
            lean_dec_ref_known(v_a_1158_, 1);
            v___x_1160_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(
                v_inst_1152_,
                v_inst_1153_,
                v_inst_1154_,
                v_inst_1155_,
                v_inst_1156_,
                v_k_1159_,
            );
            return v___x_1160_;
        }
        1 => {
            let mut v_toApplicative_1161_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1162_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1163_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1165_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1161_ = lean_ctor_get(v_inst_1152_, 0);
            lean_dec_ref(v_getVarExpr_1157_);
            lean_dec_ref(v_inst_1153_);
            v_toBind_1162_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc(v_toBind_1162_);
            v_toPure_1163_ = lean_ctor_get(v_toApplicative_1161_, 1);
            v_k_1164_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc(v_k_1164_);
            lean_dec_ref_known(v_a_1158_, 1);
            lean_inc(v_toPure_1163_);
            v___f_1165_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
            lean_closure_set(v___f_1165_, 0, v_k_1164_);
            lean_closure_set(v___f_1165_, 1, v_toPure_1163_);
            v___x_1166_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
                v_inst_1154_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1167_ = lean_apply_4(
                v_toBind_1162_,
                lean_box(0),
                lean_box(0),
                v___x_1166_,
                v___f_1165_,
            );
            return v___x_1167_;
        }
        2 => {
            let mut v_toApplicative_1168_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1169_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1170_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1172_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1168_ = lean_ctor_get(v_inst_1152_, 0);
            lean_dec_ref(v_getVarExpr_1157_);
            lean_dec_ref(v_inst_1153_);
            v_toBind_1169_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc(v_toBind_1169_);
            v_toPure_1170_ = lean_ctor_get(v_toApplicative_1168_, 1);
            v_k_1171_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc(v_k_1171_);
            lean_dec_ref_known(v_a_1158_, 1);
            lean_inc(v_toPure_1170_);
            v___f_1172_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
            lean_closure_set(v___f_1172_, 0, v_k_1171_);
            lean_closure_set(v___f_1172_, 1, v_toPure_1170_);
            v___x_1173_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
                v_inst_1154_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1174_ = lean_apply_4(
                v_toBind_1169_,
                lean_box(0),
                lean_box(0),
                v___x_1173_,
                v___f_1172_,
            );
            return v___x_1174_;
        }
        3 => {
            let mut v_toApplicative_1175_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1176_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_1177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1175_ = lean_ctor_get(v_inst_1152_, 0);
            lean_inc_ref(v_toApplicative_1175_);
            lean_dec_ref(v_inst_1156_);
            lean_dec_ref(v_inst_1155_);
            lean_dec(v_inst_1154_);
            lean_dec_ref(v_inst_1153_);
            lean_dec_ref(v_inst_1152_);
            v_toPure_1176_ = lean_ctor_get(v_toApplicative_1175_, 1);
            lean_inc(v_toPure_1176_);
            lean_dec_ref(v_toApplicative_1175_);
            v_i_1177_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc(v_i_1177_);
            lean_dec_ref_known(v_a_1158_, 1);
            v___x_1178_ = lean_apply_1(v_getVarExpr_1157_, v_i_1177_);
            v___x_1179_ = lean_apply_2(v_toPure_1176_, lean_box(0), v___x_1178_);
            return v___x_1179_;
        }
        4 => {
            let mut v_toApplicative_1180_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1181_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1182_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1183_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1180_ = lean_ctor_get(v_inst_1152_, 0);
            v_toBind_1181_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc_n(v_toBind_1181_, 2);
            v_toPure_1182_ = lean_ctor_get(v_toApplicative_1180_, 1);
            v_a_1183_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc_ref(v_a_1183_);
            lean_dec_ref_known(v_a_1158_, 1);
            lean_inc_ref(v_inst_1156_);
            lean_inc_ref(v_inst_1155_);
            lean_inc(v_inst_1154_);
            lean_inc_ref(v_inst_1153_);
            lean_inc_ref(v_inst_1152_);
            lean_inc(v_toPure_1182_);
            v___f_1184_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3 as *mut core::ffi::c_void, 10, 9);
            lean_closure_set(v___f_1184_, 0, v_toPure_1182_);
            lean_closure_set(v___f_1184_, 1, v_inst_1152_);
            lean_closure_set(v___f_1184_, 2, v_inst_1153_);
            lean_closure_set(v___f_1184_, 3, v_inst_1154_);
            lean_closure_set(v___f_1184_, 4, v_inst_1155_);
            lean_closure_set(v___f_1184_, 5, v_inst_1156_);
            lean_closure_set(v___f_1184_, 6, v_getVarExpr_1157_);
            lean_closure_set(v___f_1184_, 7, v_a_1183_);
            lean_closure_set(v___f_1184_, 8, v_toBind_1181_);
            v___x_1185_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(
                v_inst_1154_,
                v_inst_1153_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1186_ = lean_apply_4(
                v_toBind_1181_,
                lean_box(0),
                lean_box(0),
                v___x_1185_,
                v___f_1184_,
            );
            return v___x_1186_;
        }
        5 => {
            let mut v_toApplicative_1187_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1188_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1189_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1190_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1191_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1192_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1187_ = lean_ctor_get(v_inst_1152_, 0);
            v_toBind_1188_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc_n(v_toBind_1188_, 2);
            v_toPure_1189_ = lean_ctor_get(v_toApplicative_1187_, 1);
            v_a_1190_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc_ref(v_a_1190_);
            v_b_1191_ = lean_ctor_get(v_a_1158_, 1);
            lean_inc_ref(v_b_1191_);
            lean_dec_ref_known(v_a_1158_, 2);
            lean_inc_ref(v_inst_1156_);
            lean_inc_ref(v_inst_1155_);
            lean_inc(v_inst_1154_);
            lean_inc_ref(v_inst_1153_);
            lean_inc_ref(v_inst_1152_);
            lean_inc(v_toPure_1189_);
            v___f_1192_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            lean_closure_set(v___f_1192_, 0, v_toPure_1189_);
            lean_closure_set(v___f_1192_, 1, v_inst_1152_);
            lean_closure_set(v___f_1192_, 2, v_inst_1153_);
            lean_closure_set(v___f_1192_, 3, v_inst_1154_);
            lean_closure_set(v___f_1192_, 4, v_inst_1155_);
            lean_closure_set(v___f_1192_, 5, v_inst_1156_);
            lean_closure_set(v___f_1192_, 6, v_getVarExpr_1157_);
            lean_closure_set(v___f_1192_, 7, v_b_1191_);
            lean_closure_set(v___f_1192_, 8, v_toBind_1188_);
            lean_closure_set(v___f_1192_, 9, v_a_1190_);
            v___x_1193_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
                v_inst_1154_,
                v_inst_1153_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1194_ = lean_apply_4(
                v_toBind_1188_,
                lean_box(0),
                lean_box(0),
                v___x_1193_,
                v___f_1192_,
            );
            return v___x_1194_;
        }
        6 => {
            let mut v_toApplicative_1195_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1196_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1197_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1198_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1199_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1195_ = lean_ctor_get(v_inst_1152_, 0);
            v_toBind_1196_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc_n(v_toBind_1196_, 2);
            v_toPure_1197_ = lean_ctor_get(v_toApplicative_1195_, 1);
            v_a_1198_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc_ref(v_a_1198_);
            v_b_1199_ = lean_ctor_get(v_a_1158_, 1);
            lean_inc_ref(v_b_1199_);
            lean_dec_ref_known(v_a_1158_, 2);
            lean_inc_ref(v_inst_1156_);
            lean_inc_ref(v_inst_1155_);
            lean_inc(v_inst_1154_);
            lean_inc_ref(v_inst_1153_);
            lean_inc_ref(v_inst_1152_);
            lean_inc(v_toPure_1197_);
            v___f_1200_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            lean_closure_set(v___f_1200_, 0, v_toPure_1197_);
            lean_closure_set(v___f_1200_, 1, v_inst_1152_);
            lean_closure_set(v___f_1200_, 2, v_inst_1153_);
            lean_closure_set(v___f_1200_, 3, v_inst_1154_);
            lean_closure_set(v___f_1200_, 4, v_inst_1155_);
            lean_closure_set(v___f_1200_, 5, v_inst_1156_);
            lean_closure_set(v___f_1200_, 6, v_getVarExpr_1157_);
            lean_closure_set(v___f_1200_, 7, v_b_1199_);
            lean_closure_set(v___f_1200_, 8, v_toBind_1196_);
            lean_closure_set(v___f_1200_, 9, v_a_1198_);
            v___x_1201_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(
                v_inst_1154_,
                v_inst_1153_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1202_ = lean_apply_4(
                v_toBind_1196_,
                lean_box(0),
                lean_box(0),
                v___x_1201_,
                v___f_1200_,
            );
            return v___x_1202_;
        }
        7 => {
            let mut v_toApplicative_1203_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1204_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1205_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1207_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1203_ = lean_ctor_get(v_inst_1152_, 0);
            v_toBind_1204_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc_n(v_toBind_1204_, 2);
            v_toPure_1205_ = lean_ctor_get(v_toApplicative_1203_, 1);
            v_a_1206_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc_ref(v_a_1206_);
            v_b_1207_ = lean_ctor_get(v_a_1158_, 1);
            lean_inc_ref(v_b_1207_);
            lean_dec_ref_known(v_a_1158_, 2);
            lean_inc_ref(v_inst_1156_);
            lean_inc_ref(v_inst_1155_);
            lean_inc(v_inst_1154_);
            lean_inc_ref(v_inst_1153_);
            lean_inc_ref(v_inst_1152_);
            lean_inc(v_toPure_1205_);
            v___f_1208_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            lean_closure_set(v___f_1208_, 0, v_toPure_1205_);
            lean_closure_set(v___f_1208_, 1, v_inst_1152_);
            lean_closure_set(v___f_1208_, 2, v_inst_1153_);
            lean_closure_set(v___f_1208_, 3, v_inst_1154_);
            lean_closure_set(v___f_1208_, 4, v_inst_1155_);
            lean_closure_set(v___f_1208_, 5, v_inst_1156_);
            lean_closure_set(v___f_1208_, 6, v_getVarExpr_1157_);
            lean_closure_set(v___f_1208_, 7, v_b_1207_);
            lean_closure_set(v___f_1208_, 8, v_toBind_1204_);
            lean_closure_set(v___f_1208_, 9, v_a_1206_);
            v___x_1209_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
                v_inst_1154_,
                v_inst_1153_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1210_ = lean_apply_4(
                v_toBind_1204_,
                lean_box(0),
                lean_box(0),
                v___x_1209_,
                v___f_1208_,
            );
            return v___x_1210_;
        }
        _ => {
            let mut v_toApplicative_1211_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_1212_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1213_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1214_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_1211_ = lean_ctor_get(v_inst_1152_, 0);
            v_toBind_1212_ = lean_ctor_get(v_inst_1152_, 1);
            lean_inc_n(v_toBind_1212_, 2);
            v_toPure_1213_ = lean_ctor_get(v_toApplicative_1211_, 1);
            v_a_1214_ = lean_ctor_get(v_a_1158_, 0);
            lean_inc_ref(v_a_1214_);
            v_k_1215_ = lean_ctor_get(v_a_1158_, 1);
            lean_inc(v_k_1215_);
            lean_dec_ref_known(v_a_1158_, 2);
            lean_inc_ref(v_inst_1156_);
            lean_inc_ref(v_inst_1155_);
            lean_inc(v_inst_1154_);
            lean_inc_ref(v_inst_1153_);
            lean_inc_ref(v_inst_1152_);
            lean_inc(v_toPure_1213_);
            v___f_1216_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__7 as *mut core::ffi::c_void, 11, 10);
            lean_closure_set(v___f_1216_, 0, v_k_1215_);
            lean_closure_set(v___f_1216_, 1, v_toPure_1213_);
            lean_closure_set(v___f_1216_, 2, v_inst_1152_);
            lean_closure_set(v___f_1216_, 3, v_inst_1153_);
            lean_closure_set(v___f_1216_, 4, v_inst_1154_);
            lean_closure_set(v___f_1216_, 5, v_inst_1155_);
            lean_closure_set(v___f_1216_, 6, v_inst_1156_);
            lean_closure_set(v___f_1216_, 7, v_getVarExpr_1157_);
            lean_closure_set(v___f_1216_, 8, v_a_1214_);
            lean_closure_set(v___f_1216_, 9, v_toBind_1212_);
            v___x_1217_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(
                v_inst_1154_,
                v_inst_1153_,
                v_inst_1152_,
                v_inst_1155_,
                v_inst_1156_,
            );
            v___x_1218_ = lean_apply_4(
                v_toBind_1212_,
                lean_box(0),
                lean_box(0),
                v___x_1217_,
                v___f_1216_,
            );
            return v___x_1218_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3(
    mut v_toPure_1219_: *mut LeanObject,
    mut v_inst_1220_: *mut LeanObject,
    mut v_inst_1221_: *mut LeanObject,
    mut v_inst_1222_: *mut LeanObject,
    mut v_inst_1223_: *mut LeanObject,
    mut v_inst_1224_: *mut LeanObject,
    mut v_getVarExpr_1225_: *mut LeanObject,
    mut v_a_1226_: *mut LeanObject,
    mut v_toBind_1227_: *mut LeanObject,
    mut v_____do__lift_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    v___f_1229_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_1229_, 0, v_____do__lift_1228_);
    lean_closure_set(v___f_1229_, 1, v_toPure_1219_);
    v___x_1230_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1220_, v_inst_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_getVarExpr_1225_, v_a_1226_);
    v___x_1231_ = lean_apply_4(
        v_toBind_1227_,
        lean_box(0),
        lean_box(0),
        v___x_1230_,
        v___f_1229_,
    );
    return v___x_1231_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go(
    mut v_m_1232_: *mut LeanObject,
    mut v_inst_1233_: *mut LeanObject,
    mut v_inst_1234_: *mut LeanObject,
    mut v_inst_1235_: *mut LeanObject,
    mut v_inst_1236_: *mut LeanObject,
    mut v_inst_1237_: *mut LeanObject,
    mut v_getVarExpr_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    v___x_1240_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_inst_1237_, v_getVarExpr_1238_, v_a_1239_);
    return v___x_1240_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore___redArg(
    mut v_inst_1241_: *mut LeanObject,
    mut v_inst_1242_: *mut LeanObject,
    mut v_inst_1243_: *mut LeanObject,
    mut v_inst_1244_: *mut LeanObject,
    mut v_inst_1245_: *mut LeanObject,
    mut v_getVarExpr_1246_: *mut LeanObject,
    mut v_e_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1248_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_getVarExpr_1246_, v_e_1247_);
    return v___x_1248_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore(
    mut v_m_1249_: *mut LeanObject,
    mut v_inst_1250_: *mut LeanObject,
    mut v_inst_1251_: *mut LeanObject,
    mut v_inst_1252_: *mut LeanObject,
    mut v_inst_1253_: *mut LeanObject,
    mut v_inst_1254_: *mut LeanObject,
    mut v_getVarExpr_1255_: *mut LeanObject,
    mut v_e_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1257_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_inst_1254_, v_getVarExpr_1255_, v_e_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(
    mut v___x_1258_: *mut LeanObject,
    mut v_vars_1259_: *mut LeanObject,
    mut v_x_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = lean_array_get_borrowed(v___x_1258_, v_vars_1259_, v_x_1260_);
    lean_inc(v___x_1261_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed(
    mut v___x_1262_: *mut LeanObject,
    mut v_vars_1263_: *mut LeanObject,
    mut v_x_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(
        v___x_1262_,
        v_vars_1263_,
        v_x_1264_,
    );
    lean_dec(v_x_1264_);
    lean_dec_ref(v_vars_1263_);
    lean_dec_ref(v___x_1262_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(
    mut v_inst_1266_: *mut LeanObject,
    mut v_inst_1267_: *mut LeanObject,
    mut v_inst_1268_: *mut LeanObject,
    mut v_inst_1269_: *mut LeanObject,
    mut v_inst_1270_: *mut LeanObject,
    mut v_vars_1271_: *mut LeanObject,
    mut v_e_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lean_instInhabitedExpr;
    v___f_1274_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1274_, 0, v___x_1273_);
    lean_closure_set(v___f_1274_, 1, v_vars_1271_);
    v___x_1275_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_1266_, v_inst_1267_, v_inst_1268_, v_inst_1269_, v_inst_1270_, v___f_1274_, v_e_1272_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_denoteRingExpr(
    mut v_m_1276_: *mut LeanObject,
    mut v_inst_1277_: *mut LeanObject,
    mut v_inst_1278_: *mut LeanObject,
    mut v_inst_1279_: *mut LeanObject,
    mut v_inst_1280_: *mut LeanObject,
    mut v_inst_1281_: *mut LeanObject,
    mut v_vars_1282_: *mut LeanObject,
    mut v_e_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(
        v_inst_1277_,
        v_inst_1278_,
        v_inst_1279_,
        v_inst_1280_,
        v_inst_1281_,
        v_vars_1282_,
        v_e_1283_,
    );
    return v___x_1284_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
}
