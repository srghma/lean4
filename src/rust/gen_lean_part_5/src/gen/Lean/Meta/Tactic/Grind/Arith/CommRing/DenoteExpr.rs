// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
use crate::ffi::{
    lean_array_get_borrowed, lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_to_int,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkIntLit, l_Lean_mkNatLit, l_Lean_mkNot, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f___boxed;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        9341924117480681831 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        17636616155771105671 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__0(
    mut v_n_844_: *mut leanh::LeanObject,
    mut v_toPure_845_: *mut leanh::LeanObject,
    mut v_____do__lift_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Expr_app___override(v_____do__lift_846_, v_n_844_);
    v___x_848_ = leanh::lean_apply_2(v_toPure_845_, leanh::lean_box(0), v___x_847_);
    return v___x_848_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = leanh::lean_unsigned_to_nat(0);
    v___x_851_ = lean_nat_to_int(v___x_850_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1(
    mut v___x_852_: *mut leanh::LeanObject,
    mut v___x_853_: *mut leanh::LeanObject,
    mut v_type_854_: *mut leanh::LeanObject,
    mut v_n_855_: *mut leanh::LeanObject,
    mut v_k_856_: *mut leanh::LeanObject,
    mut v_toPure_857_: *mut leanh::LeanObject,
    mut v_inst_858_: *mut leanh::LeanObject,
    mut v_inst_859_: *mut leanh::LeanObject,
    mut v_inst_860_: *mut leanh::LeanObject,
    mut v_inst_861_: *mut leanh::LeanObject,
    mut v_inst_862_: *mut leanh::LeanObject,
    mut v_toBind_863_: *mut leanh::LeanObject,
    mut v_ofNatInst_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    v___x_865_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0;
    v___x_866_ = l_Lean_Name_mkStr2(v___x_852_, v___x_865_);
    v___x_867_ = l_Lean_mkConst(v___x_866_, v___x_853_);
    v_n_868_ = l_Lean_mkApp3(v___x_867_, v_type_854_, v_n_855_, v_ofNatInst_864_);
    v___x_869_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1,
    );
    v___x_870_ = lean_int_dec_lt(v_k_856_, v___x_869_);
    if v___x_870_ == 0 {
        let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_863_);
        leanh::lean_dec_ref(v_inst_862_);
        leanh::lean_dec_ref(v_inst_861_);
        leanh::lean_dec_ref(v_inst_860_);
        leanh::lean_dec_ref(v_inst_859_);
        leanh::lean_dec(v_inst_858_);
        v___x_871_ = leanh::lean_apply_2(v_toPure_857_, leanh::lean_box(0), v_n_868_);
        return v___x_871_;
    } else {
        let mut v___f_872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_872_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_872_, 0, v_n_868_);
        leanh::lean_closure_set(v___f_872_, 1, v_toPure_857_);
        v___x_873_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
            v_inst_858_,
            v_inst_859_,
            v_inst_860_,
            v_inst_861_,
            v_inst_862_,
        );
        v___x_874_ = leanh::lean_apply_4(
            v_toBind_863_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_873_,
            v___f_872_,
        );
        return v___x_874_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___boxed(
    mut v___x_875_: *mut leanh::LeanObject,
    mut v___x_876_: *mut leanh::LeanObject,
    mut v_type_877_: *mut leanh::LeanObject,
    mut v_n_878_: *mut leanh::LeanObject,
    mut v_k_879_: *mut leanh::LeanObject,
    mut v_toPure_880_: *mut leanh::LeanObject,
    mut v_inst_881_: *mut leanh::LeanObject,
    mut v_inst_882_: *mut leanh::LeanObject,
    mut v_inst_883_: *mut leanh::LeanObject,
    mut v_inst_884_: *mut leanh::LeanObject,
    mut v_inst_885_: *mut leanh::LeanObject,
    mut v_toBind_886_: *mut leanh::LeanObject,
    mut v_ofNatInst_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1(
        v___x_875_,
        v___x_876_,
        v_type_877_,
        v_n_878_,
        v_k_879_,
        v_toPure_880_,
        v_inst_881_,
        v_inst_882_,
        v_inst_883_,
        v_inst_884_,
        v_inst_885_,
        v_toBind_886_,
        v_ofNatInst_887_,
    );
    leanh::lean_dec(v_k_879_);
    return v_res_888_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__2(
    mut v___f_889_: *mut leanh::LeanObject,
    mut v_ofNatInst_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = leanh::lean_apply_1(v___f_889_, v_ofNatInst_890_);
    return v___x_891_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4(
    mut v_toPure_900_: *mut leanh::LeanObject,
    mut v_toBind_901_: *mut leanh::LeanObject,
    mut v___f_902_: *mut leanh::LeanObject,
    mut v___x_903_: *mut leanh::LeanObject,
    mut v_type_904_: *mut leanh::LeanObject,
    mut v_semiringInst_905_: *mut leanh::LeanObject,
    mut v_n_906_: *mut leanh::LeanObject,
    mut v___f_907_: *mut leanh::LeanObject,
    mut v_____do__lift_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_908_) == 1 {
        let mut v_val_909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_907_);
        leanh::lean_dec_ref(v_n_906_);
        leanh::lean_dec_ref(v_semiringInst_905_);
        leanh::lean_dec_ref(v_type_904_);
        leanh::lean_dec(v___x_903_);
        v_val_909_ = leanh::lean_ctor_get(v_____do__lift_908_, 0);
        leanh::lean_inc(v_val_909_);
        leanh::lean_dec_ref_known(v_____do__lift_908_, 1);
        v___x_910_ =
            leanh::lean_apply_2(v_toPure_900_, leanh::lean_box(0), v_val_909_);
        v___x_911_ = leanh::lean_apply_4(
            v_toBind_901_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_910_,
            v___f_902_,
        );
        return v___x_911_;
    } else {
        let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____do__lift_908_);
        leanh::lean_dec(v___f_902_);
        v___x_912_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3;
        v___x_913_ = l_Lean_mkConst(v___x_912_, v___x_903_);
        v___x_914_ = l_Lean_mkApp3(v___x_913_, v_type_904_, v_semiringInst_905_, v_n_906_);
        v___x_915_ =
            leanh::lean_apply_2(v_toPure_900_, leanh::lean_box(0), v___x_914_);
        v___x_916_ = leanh::lean_apply_4(
            v_toBind_901_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_915_,
            v___f_907_,
        );
        return v___x_916_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3(
    mut v_k_920_: *mut leanh::LeanObject,
    mut v_toPure_921_: *mut leanh::LeanObject,
    mut v_inst_922_: *mut leanh::LeanObject,
    mut v_inst_923_: *mut leanh::LeanObject,
    mut v_inst_924_: *mut leanh::LeanObject,
    mut v_inst_925_: *mut leanh::LeanObject,
    mut v_inst_926_: *mut leanh::LeanObject,
    mut v_toBind_927_: *mut leanh::LeanObject,
    mut v_ring_928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_929_ = leanh::lean_ctor_get(v_ring_928_, 1);
    leanh::lean_inc_ref_n(v_type_929_, 3);
    v_u_930_ = leanh::lean_ctor_get(v_ring_928_, 2);
    leanh::lean_inc(v_u_930_);
    v_semiringInst_931_ = leanh::lean_ctor_get(v_ring_928_, 4);
    leanh::lean_inc_ref(v_semiringInst_931_);
    leanh::lean_dec_ref(v_ring_928_);
    v___x_932_ = lean_nat_abs(v_k_920_);
    v_n_933_ = l_Lean_mkRawNatLit(v___x_932_);
    v___x_934_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0;
    v___x_935_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1;
    v___x_936_ = leanh::lean_box(0);
    v___x_937_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_937_, 0, v_u_930_);
    leanh::lean_ctor_set(v___x_937_, 1, v___x_936_);
    leanh::lean_inc_n(v_toBind_927_, 2);
    leanh::lean_inc(v_inst_922_);
    leanh::lean_inc(v_toPure_921_);
    leanh::lean_inc_ref_n(v_n_933_, 2);
    leanh::lean_inc_ref_n(v___x_937_, 2);
    v___f_938_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_938_, 0, v___x_934_);
    leanh::lean_closure_set(v___f_938_, 1, v___x_937_);
    leanh::lean_closure_set(v___f_938_, 2, v_type_929_);
    leanh::lean_closure_set(v___f_938_, 3, v_n_933_);
    leanh::lean_closure_set(v___f_938_, 4, v_k_920_);
    leanh::lean_closure_set(v___f_938_, 5, v_toPure_921_);
    leanh::lean_closure_set(v___f_938_, 6, v_inst_922_);
    leanh::lean_closure_set(v___f_938_, 7, v_inst_923_);
    leanh::lean_closure_set(v___f_938_, 8, v_inst_924_);
    leanh::lean_closure_set(v___f_938_, 9, v_inst_925_);
    leanh::lean_closure_set(v___f_938_, 10, v_inst_926_);
    leanh::lean_closure_set(v___f_938_, 11, v_toBind_927_);
    v___f_939_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_939_, 0, v___f_938_);
    leanh::lean_inc_ref(v___f_939_);
    v___f_940_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_940_, 0, v_toPure_921_);
    leanh::lean_closure_set(v___f_940_, 1, v_toBind_927_);
    leanh::lean_closure_set(v___f_940_, 2, v___f_939_);
    leanh::lean_closure_set(v___f_940_, 3, v___x_937_);
    leanh::lean_closure_set(v___f_940_, 4, v_type_929_);
    leanh::lean_closure_set(v___f_940_, 5, v_semiringInst_931_);
    leanh::lean_closure_set(v___f_940_, 6, v_n_933_);
    leanh::lean_closure_set(v___f_940_, 7, v___f_939_);
    v___x_941_ = l_Lean_mkConst(v___x_935_, v___x_937_);
    v___x_942_ = l_Lean_mkAppB(v___x_941_, v_type_929_, v_n_933_);
    v___x_943_ = leanh::lean_box(0);
    v___x_944_ = leanh::lean_alloc_closure(
        l_Lean_Meta_synthInstance_x3f___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_944_, 0, v___x_942_);
    leanh::lean_closure_set(v___x_944_, 1, v___x_943_);
    v___x_945_ = leanh::lean_apply_2(v_inst_922_, leanh::lean_box(0), v___x_944_);
    v___x_946_ = leanh::lean_apply_4(
        v_toBind_927_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_945_,
        v___f_940_,
    );
    return v___x_946_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
    mut v_inst_947_: *mut leanh::LeanObject,
    mut v_inst_948_: *mut leanh::LeanObject,
    mut v_inst_949_: *mut leanh::LeanObject,
    mut v_inst_950_: *mut leanh::LeanObject,
    mut v_inst_951_: *mut leanh::LeanObject,
    mut v_k_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_953_ = leanh::lean_ctor_get(v_inst_947_, 0);
    v_toBind_954_ = leanh::lean_ctor_get(v_inst_947_, 1);
    leanh::lean_inc_n(v_toBind_954_, 2);
    v_getRing_955_ = leanh::lean_ctor_get(v_inst_951_, 0);
    leanh::lean_inc(v_getRing_955_);
    v_toPure_956_ = leanh::lean_ctor_get(v_toApplicative_953_, 1);
    leanh::lean_inc(v_toPure_956_);
    v___f_957_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_957_, 0, v_k_952_);
    leanh::lean_closure_set(v___f_957_, 1, v_toPure_956_);
    leanh::lean_closure_set(v___f_957_, 2, v_inst_949_);
    leanh::lean_closure_set(v___f_957_, 3, v_inst_948_);
    leanh::lean_closure_set(v___f_957_, 4, v_inst_947_);
    leanh::lean_closure_set(v___f_957_, 5, v_inst_950_);
    leanh::lean_closure_set(v___f_957_, 6, v_inst_951_);
    leanh::lean_closure_set(v___f_957_, 7, v_toBind_954_);
    v___x_958_ = leanh::lean_apply_4(
        v_toBind_954_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_955_,
        v___f_957_,
    );
    return v___x_958_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum(
    mut v_M_959_: *mut leanh::LeanObject,
    mut v_inst_960_: *mut leanh::LeanObject,
    mut v_inst_961_: *mut leanh::LeanObject,
    mut v_inst_962_: *mut leanh::LeanObject,
    mut v_inst_963_: *mut leanh::LeanObject,
    mut v_inst_964_: *mut leanh::LeanObject,
    mut v_k_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_960_,
        v_inst_961_,
        v_inst_962_,
        v_inst_963_,
        v_inst_964_,
        v_k_965_,
    );
    return v___x_966_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__0(
    mut v_toApplicative_967_: *mut leanh::LeanObject,
    mut v_k_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v_____do__lift_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_971_ = leanh::lean_ctor_get(v_toApplicative_967_, 1);
    leanh::lean_inc(v_toPure_971_);
    leanh::lean_dec_ref(v_toApplicative_967_);
    v___x_972_ = l_Lean_mkNatLit(v_k_968_);
    v___x_973_ = l_Lean_mkAppB(v_____do__lift_970_, v___y_969_, v___x_972_);
    v___x_974_ = leanh::lean_apply_2(v_toPure_971_, leanh::lean_box(0), v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1(
    mut v_pw_975_: *mut leanh::LeanObject,
    mut v_toApplicative_976_: *mut leanh::LeanObject,
    mut v_inst_977_: *mut leanh::LeanObject,
    mut v_inst_978_: *mut leanh::LeanObject,
    mut v_inst_979_: *mut leanh::LeanObject,
    mut v_inst_980_: *mut leanh::LeanObject,
    mut v_inst_981_: *mut leanh::LeanObject,
    mut v_toBind_982_: *mut leanh::LeanObject,
    mut v___x_983_: *mut leanh::LeanObject,
    mut v_____do__lift_984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut v___f_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_985_ = leanh::lean_ctor_get(v_____do__lift_984_, 14);
                v_x_986_ = leanh::lean_ctor_get(v_pw_975_, 0);
                leanh::lean_inc(v_x_986_);
                v_k_987_ = leanh::lean_ctor_get(v_pw_975_, 1);
                leanh::lean_inc(v_k_987_);
                leanh::lean_dec_ref(v_pw_975_);
                v_size_997_ = leanh::lean_ctor_get(v_vars_985_, 2);
                v___x_998_ = lean_nat_dec_lt(v_x_986_, v_size_997_);
                if v___x_998_ == 0 {
                    leanh::lean_dec(v_x_986_);
                    v___x_999_ = l_outOfBounds___redArg(v___x_983_);
                    v___y_989_ = v___x_999_;
                    state = 1;
                    continue;
                } else {
                    v___x_1000_ =
                        l_Lean_PersistentArray_get_x21___redArg(v___x_983_, v_vars_985_, v_x_986_);
                    leanh::lean_dec(v_x_986_);
                    v___y_989_ = v___x_1000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_990_ = leanh::lean_unsigned_to_nat(1);
                v___x_991_ = lean_nat_dec_eq(v_k_987_, v___x_990_);
                if v___x_991_ == 0 {
                    v___f_992_ = leanh::lean_alloc_closure(
                        l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__0
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_992_, 0, v_toApplicative_976_);
                    leanh::lean_closure_set(v___f_992_, 1, v_k_987_);
                    leanh::lean_closure_set(v___f_992_, 2, v___y_989_);
                    v___x_993_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
                        v_inst_977_,
                        v_inst_978_,
                        v_inst_979_,
                        v_inst_980_,
                        v_inst_981_,
                    );
                    v___x_994_ = leanh::lean_apply_4(
                        v_toBind_982_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_993_,
                        v___f_992_,
                    );
                    return v___x_994_;
                } else {
                    leanh::lean_dec(v_k_987_);
                    leanh::lean_dec(v_toBind_982_);
                    leanh::lean_dec_ref(v_inst_981_);
                    leanh::lean_dec_ref(v_inst_980_);
                    leanh::lean_dec_ref(v_inst_979_);
                    leanh::lean_dec_ref(v_inst_978_);
                    leanh::lean_dec(v_inst_977_);
                    v_toPure_995_ = leanh::lean_ctor_get(v_toApplicative_976_, 1);
                    leanh::lean_inc(v_toPure_995_);
                    leanh::lean_dec_ref(v_toApplicative_976_);
                    v___x_996_ = leanh::lean_apply_2(
                        v_toPure_995_,
                        leanh::lean_box(0),
                        v___y_989_,
                    );
                    return v___x_996_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1___boxed(
    mut v_pw_1001_: *mut leanh::LeanObject,
    mut v_toApplicative_1002_: *mut leanh::LeanObject,
    mut v_inst_1003_: *mut leanh::LeanObject,
    mut v_inst_1004_: *mut leanh::LeanObject,
    mut v_inst_1005_: *mut leanh::LeanObject,
    mut v_inst_1006_: *mut leanh::LeanObject,
    mut v_inst_1007_: *mut leanh::LeanObject,
    mut v_toBind_1008_: *mut leanh::LeanObject,
    mut v___x_1009_: *mut leanh::LeanObject,
    mut v_____do__lift_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1(
        v_pw_1001_,
        v_toApplicative_1002_,
        v_inst_1003_,
        v_inst_1004_,
        v_inst_1005_,
        v_inst_1006_,
        v_inst_1007_,
        v_toBind_1008_,
        v___x_1009_,
        v_____do__lift_1010_,
    );
    leanh::lean_dec_ref(v_____do__lift_1010_);
    leanh::lean_dec_ref(v___x_1009_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
    mut v_inst_1012_: *mut leanh::LeanObject,
    mut v_inst_1013_: *mut leanh::LeanObject,
    mut v_inst_1014_: *mut leanh::LeanObject,
    mut v_inst_1015_: *mut leanh::LeanObject,
    mut v_inst_1016_: *mut leanh::LeanObject,
    mut v_pw_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1018_ = leanh::lean_ctor_get(v_inst_1012_, 0);
    leanh::lean_inc_ref(v_toApplicative_1018_);
    v_toBind_1019_ = leanh::lean_ctor_get(v_inst_1012_, 1);
    leanh::lean_inc_n(v_toBind_1019_, 2);
    v_getRing_1020_ = leanh::lean_ctor_get(v_inst_1016_, 0);
    leanh::lean_inc(v_getRing_1020_);
    v___x_1021_ = l_Lean_instInhabitedExpr;
    v___f_1022_ = leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1022_, 0, v_pw_1017_);
    leanh::lean_closure_set(v___f_1022_, 1, v_toApplicative_1018_);
    leanh::lean_closure_set(v___f_1022_, 2, v_inst_1014_);
    leanh::lean_closure_set(v___f_1022_, 3, v_inst_1013_);
    leanh::lean_closure_set(v___f_1022_, 4, v_inst_1012_);
    leanh::lean_closure_set(v___f_1022_, 5, v_inst_1015_);
    leanh::lean_closure_set(v___f_1022_, 6, v_inst_1016_);
    leanh::lean_closure_set(v___f_1022_, 7, v_toBind_1019_);
    leanh::lean_closure_set(v___f_1022_, 8, v___x_1021_);
    v___x_1023_ = leanh::lean_apply_4(
        v_toBind_1019_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1020_,
        v___f_1022_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr(
    mut v_M_1024_: *mut leanh::LeanObject,
    mut v_inst_1025_: *mut leanh::LeanObject,
    mut v_inst_1026_: *mut leanh::LeanObject,
    mut v_inst_1027_: *mut leanh::LeanObject,
    mut v_inst_1028_: *mut leanh::LeanObject,
    mut v_inst_1029_: *mut leanh::LeanObject,
    mut v_pw_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
        v_inst_1025_,
        v_inst_1026_,
        v_inst_1027_,
        v_inst_1028_,
        v_inst_1029_,
        v_pw_1030_,
    );
    return v___x_1031_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__1(
    mut v_acc_1032_: *mut leanh::LeanObject,
    mut v_inst_1033_: *mut leanh::LeanObject,
    mut v_inst_1034_: *mut leanh::LeanObject,
    mut v_inst_1035_: *mut leanh::LeanObject,
    mut v_inst_1036_: *mut leanh::LeanObject,
    mut v_inst_1037_: *mut leanh::LeanObject,
    mut v_m_1038_: *mut leanh::LeanObject,
    mut v_p_1039_: *mut leanh::LeanObject,
    mut v_toBind_1040_: *mut leanh::LeanObject,
    mut v_____do__lift_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1037_);
    leanh::lean_inc_ref(v_inst_1036_);
    leanh::lean_inc(v_inst_1035_);
    leanh::lean_inc_ref(v_inst_1034_);
    leanh::lean_inc_ref(v_inst_1033_);
    v___f_1042_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 9, 8);
    leanh::lean_closure_set(v___f_1042_, 0, v_____do__lift_1041_);
    leanh::lean_closure_set(v___f_1042_, 1, v_acc_1032_);
    leanh::lean_closure_set(v___f_1042_, 2, v_inst_1033_);
    leanh::lean_closure_set(v___f_1042_, 3, v_inst_1034_);
    leanh::lean_closure_set(v___f_1042_, 4, v_inst_1035_);
    leanh::lean_closure_set(v___f_1042_, 5, v_inst_1036_);
    leanh::lean_closure_set(v___f_1042_, 6, v_inst_1037_);
    leanh::lean_closure_set(v___f_1042_, 7, v_m_1038_);
    v___x_1043_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
        v_inst_1033_,
        v_inst_1034_,
        v_inst_1035_,
        v_inst_1036_,
        v_inst_1037_,
        v_p_1039_,
    );
    v___x_1044_ = leanh::lean_apply_4(
        v_toBind_1040_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1043_,
        v___f_1042_,
    );
    return v___x_1044_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(
    mut v_inst_1045_: *mut leanh::LeanObject,
    mut v_inst_1046_: *mut leanh::LeanObject,
    mut v_inst_1047_: *mut leanh::LeanObject,
    mut v_inst_1048_: *mut leanh::LeanObject,
    mut v_inst_1049_: *mut leanh::LeanObject,
    mut v_m_1050_: *mut leanh::LeanObject,
    mut v_acc_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_1050_) == 0 {
        let mut v_toApplicative_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1052_ = leanh::lean_ctor_get(v_inst_1045_, 0);
        leanh::lean_inc_ref(v_toApplicative_1052_);
        leanh::lean_dec_ref(v_inst_1049_);
        leanh::lean_dec_ref(v_inst_1048_);
        leanh::lean_dec(v_inst_1047_);
        leanh::lean_dec_ref(v_inst_1046_);
        leanh::lean_dec_ref(v_inst_1045_);
        v_toPure_1053_ = leanh::lean_ctor_get(v_toApplicative_1052_, 1);
        leanh::lean_inc(v_toPure_1053_);
        leanh::lean_dec_ref(v_toApplicative_1052_);
        v___x_1054_ =
            leanh::lean_apply_2(v_toPure_1053_, leanh::lean_box(0), v_acc_1051_);
        return v___x_1054_;
    } else {
        let mut v_toBind_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1055_ = leanh::lean_ctor_get(v_inst_1045_, 1);
        leanh::lean_inc_n(v_toBind_1055_, 2);
        v_p_1056_ = leanh::lean_ctor_get(v_m_1050_, 0);
        leanh::lean_inc_ref(v_p_1056_);
        v_m_1057_ = leanh::lean_ctor_get(v_m_1050_, 1);
        leanh::lean_inc(v_m_1057_);
        leanh::lean_dec_ref_known(v_m_1050_, 2);
        leanh::lean_inc_ref(v_inst_1049_);
        leanh::lean_inc_ref(v_inst_1048_);
        leanh::lean_inc(v_inst_1047_);
        leanh::lean_inc_ref(v_inst_1046_);
        leanh::lean_inc_ref(v_inst_1045_);
        v___f_1058_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
        leanh::lean_closure_set(v___f_1058_, 0, v_acc_1051_);
        leanh::lean_closure_set(v___f_1058_, 1, v_inst_1045_);
        leanh::lean_closure_set(v___f_1058_, 2, v_inst_1046_);
        leanh::lean_closure_set(v___f_1058_, 3, v_inst_1047_);
        leanh::lean_closure_set(v___f_1058_, 4, v_inst_1048_);
        leanh::lean_closure_set(v___f_1058_, 5, v_inst_1049_);
        leanh::lean_closure_set(v___f_1058_, 6, v_m_1057_);
        leanh::lean_closure_set(v___f_1058_, 7, v_p_1056_);
        leanh::lean_closure_set(v___f_1058_, 8, v_toBind_1055_);
        v___x_1059_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
            v_inst_1047_,
            v_inst_1046_,
            v_inst_1045_,
            v_inst_1048_,
            v_inst_1049_,
        );
        v___x_1060_ = leanh::lean_apply_4(
            v_toBind_1055_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1059_,
            v___f_1058_,
        );
        return v___x_1060_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1061_: *mut leanh::LeanObject,
    mut v_acc_1062_: *mut leanh::LeanObject,
    mut v_inst_1063_: *mut leanh::LeanObject,
    mut v_inst_1064_: *mut leanh::LeanObject,
    mut v_inst_1065_: *mut leanh::LeanObject,
    mut v_inst_1066_: *mut leanh::LeanObject,
    mut v_inst_1067_: *mut leanh::LeanObject,
    mut v_m_1068_: *mut leanh::LeanObject,
    mut v_____do__lift_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lean_mkAppB(v_____do__lift_1061_, v_acc_1062_, v_____do__lift_1069_);
    v___x_1071_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_inst_1067_, v_m_1068_, v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go(
    mut v_M_1072_: *mut leanh::LeanObject,
    mut v_inst_1073_: *mut leanh::LeanObject,
    mut v_inst_1074_: *mut leanh::LeanObject,
    mut v_inst_1075_: *mut leanh::LeanObject,
    mut v_inst_1076_: *mut leanh::LeanObject,
    mut v_inst_1077_: *mut leanh::LeanObject,
    mut v_m_1078_: *mut leanh::LeanObject,
    mut v_acc_1079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1073_, v_inst_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_m_1078_, v_acc_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___lam__0(
    mut v_inst_1081_: *mut leanh::LeanObject,
    mut v_inst_1082_: *mut leanh::LeanObject,
    mut v_inst_1083_: *mut leanh::LeanObject,
    mut v_inst_1084_: *mut leanh::LeanObject,
    mut v_inst_1085_: *mut leanh::LeanObject,
    mut v_m_1086_: *mut leanh::LeanObject,
    mut v_____do__lift_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1081_, v_inst_1082_, v_inst_1083_, v_inst_1084_, v_inst_1085_, v_m_1086_, v_____do__lift_1087_);
    return v___x_1088_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = leanh::lean_unsigned_to_nat(1);
    v___x_1090_ = lean_nat_to_int(v___x_1089_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
    mut v_inst_1091_: *mut leanh::LeanObject,
    mut v_inst_1092_: *mut leanh::LeanObject,
    mut v_inst_1093_: *mut leanh::LeanObject,
    mut v_inst_1094_: *mut leanh::LeanObject,
    mut v_inst_1095_: *mut leanh::LeanObject,
    mut v_m_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_1096_) == 0 {
        let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1097_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0_once),
            _init_l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0,
        );
        v___x_1098_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
            v_inst_1091_,
            v_inst_1092_,
            v_inst_1093_,
            v_inst_1094_,
            v_inst_1095_,
            v___x_1097_,
        );
        return v___x_1098_;
    } else {
        let mut v_toBind_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1099_ = leanh::lean_ctor_get(v_inst_1091_, 1);
        leanh::lean_inc(v_toBind_1099_);
        v_p_1100_ = leanh::lean_ctor_get(v_m_1096_, 0);
        leanh::lean_inc_ref(v_p_1100_);
        v_m_1101_ = leanh::lean_ctor_get(v_m_1096_, 1);
        leanh::lean_inc(v_m_1101_);
        leanh::lean_dec_ref_known(v_m_1096_, 2);
        leanh::lean_inc_ref(v_inst_1095_);
        leanh::lean_inc_ref(v_inst_1094_);
        leanh::lean_inc(v_inst_1093_);
        leanh::lean_inc_ref(v_inst_1092_);
        leanh::lean_inc_ref(v_inst_1091_);
        v___f_1102_ = leanh::lean_alloc_closure(
            l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_1102_, 0, v_inst_1091_);
        leanh::lean_closure_set(v___f_1102_, 1, v_inst_1092_);
        leanh::lean_closure_set(v___f_1102_, 2, v_inst_1093_);
        leanh::lean_closure_set(v___f_1102_, 3, v_inst_1094_);
        leanh::lean_closure_set(v___f_1102_, 4, v_inst_1095_);
        leanh::lean_closure_set(v___f_1102_, 5, v_m_1101_);
        v___x_1103_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
            v_inst_1091_,
            v_inst_1092_,
            v_inst_1093_,
            v_inst_1094_,
            v_inst_1095_,
            v_p_1100_,
        );
        v___x_1104_ = leanh::lean_apply_4(
            v_toBind_1099_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1103_,
            v___f_1102_,
        );
        return v___x_1104_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr(
    mut v_M_1105_: *mut leanh::LeanObject,
    mut v_inst_1106_: *mut leanh::LeanObject,
    mut v_inst_1107_: *mut leanh::LeanObject,
    mut v_inst_1108_: *mut leanh::LeanObject,
    mut v_inst_1109_: *mut leanh::LeanObject,
    mut v_inst_1110_: *mut leanh::LeanObject,
    mut v_m_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
        v_inst_1106_,
        v_inst_1107_,
        v_inst_1108_,
        v_inst_1109_,
        v_inst_1110_,
        v_m_1111_,
    );
    return v___x_1112_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__0(
    mut v_toApplicative_1113_: *mut leanh::LeanObject,
    mut v_____do__lift_1114_: *mut leanh::LeanObject,
    mut v_____do__lift_1115_: *mut leanh::LeanObject,
    mut v_____do__lift_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_1117_ = leanh::lean_ctor_get(v_toApplicative_1113_, 1);
    leanh::lean_inc(v_toPure_1117_);
    leanh::lean_dec_ref(v_toApplicative_1113_);
    v___x_1118_ = l_Lean_mkAppB(
        v_____do__lift_1114_,
        v_____do__lift_1115_,
        v_____do__lift_1116_,
    );
    v___x_1119_ =
        leanh::lean_apply_2(v_toPure_1117_, leanh::lean_box(0), v___x_1118_);
    return v___x_1119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__1(
    mut v_toApplicative_1120_: *mut leanh::LeanObject,
    mut v_____do__lift_1121_: *mut leanh::LeanObject,
    mut v_inst_1122_: *mut leanh::LeanObject,
    mut v_inst_1123_: *mut leanh::LeanObject,
    mut v_inst_1124_: *mut leanh::LeanObject,
    mut v_inst_1125_: *mut leanh::LeanObject,
    mut v_inst_1126_: *mut leanh::LeanObject,
    mut v_m_1127_: *mut leanh::LeanObject,
    mut v_toBind_1128_: *mut leanh::LeanObject,
    mut v_____do__lift_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1130_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_1130_, 0, v_toApplicative_1120_);
    leanh::lean_closure_set(v___f_1130_, 1, v_____do__lift_1121_);
    leanh::lean_closure_set(v___f_1130_, 2, v_____do__lift_1129_);
    v___x_1131_ = l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
        v_inst_1122_,
        v_inst_1123_,
        v_inst_1124_,
        v_inst_1125_,
        v_inst_1126_,
        v_m_1127_,
    );
    v___x_1132_ = leanh::lean_apply_4(
        v_toBind_1128_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1131_,
        v___f_1130_,
    );
    return v___x_1132_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__2(
    mut v_toApplicative_1133_: *mut leanh::LeanObject,
    mut v_inst_1134_: *mut leanh::LeanObject,
    mut v_inst_1135_: *mut leanh::LeanObject,
    mut v_inst_1136_: *mut leanh::LeanObject,
    mut v_inst_1137_: *mut leanh::LeanObject,
    mut v_inst_1138_: *mut leanh::LeanObject,
    mut v_m_1139_: *mut leanh::LeanObject,
    mut v_toBind_1140_: *mut leanh::LeanObject,
    mut v_k_1141_: *mut leanh::LeanObject,
    mut v_____do__lift_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1140_);
    leanh::lean_inc_ref(v_inst_1138_);
    leanh::lean_inc_ref(v_inst_1137_);
    leanh::lean_inc(v_inst_1136_);
    leanh::lean_inc_ref(v_inst_1135_);
    leanh::lean_inc_ref(v_inst_1134_);
    v___f_1143_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
    leanh::lean_closure_set(v___f_1143_, 0, v_toApplicative_1133_);
    leanh::lean_closure_set(v___f_1143_, 1, v_____do__lift_1142_);
    leanh::lean_closure_set(v___f_1143_, 2, v_inst_1134_);
    leanh::lean_closure_set(v___f_1143_, 3, v_inst_1135_);
    leanh::lean_closure_set(v___f_1143_, 4, v_inst_1136_);
    leanh::lean_closure_set(v___f_1143_, 5, v_inst_1137_);
    leanh::lean_closure_set(v___f_1143_, 6, v_inst_1138_);
    leanh::lean_closure_set(v___f_1143_, 7, v_m_1139_);
    leanh::lean_closure_set(v___f_1143_, 8, v_toBind_1140_);
    v___x_1144_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1134_,
        v_inst_1135_,
        v_inst_1136_,
        v_inst_1137_,
        v_inst_1138_,
        v_k_1141_,
    );
    v___x_1145_ = leanh::lean_apply_4(
        v_toBind_1140_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1144_,
        v___f_1143_,
    );
    return v___x_1145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(
    mut v_inst_1146_: *mut leanh::LeanObject,
    mut v_inst_1147_: *mut leanh::LeanObject,
    mut v_inst_1148_: *mut leanh::LeanObject,
    mut v_inst_1149_: *mut leanh::LeanObject,
    mut v_inst_1150_: *mut leanh::LeanObject,
    mut v_k_1151_: *mut leanh::LeanObject,
    mut v_m_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0,
    );
    v___x_1154_ = lean_int_dec_eq(v_k_1151_, v___x_1153_);
    if v___x_1154_ == 0 {
        let mut v_toApplicative_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1155_ = leanh::lean_ctor_get(v_inst_1146_, 0);
        v_toBind_1156_ = leanh::lean_ctor_get(v_inst_1146_, 1);
        leanh::lean_inc_n(v_toBind_1156_, 2);
        leanh::lean_inc_ref(v_inst_1150_);
        leanh::lean_inc_ref(v_inst_1149_);
        leanh::lean_inc(v_inst_1148_);
        leanh::lean_inc_ref(v_inst_1147_);
        leanh::lean_inc_ref(v_inst_1146_);
        leanh::lean_inc_ref(v_toApplicative_1155_);
        v___f_1157_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__2 as *mut core::ffi::c_void, 10, 9);
        leanh::lean_closure_set(v___f_1157_, 0, v_toApplicative_1155_);
        leanh::lean_closure_set(v___f_1157_, 1, v_inst_1146_);
        leanh::lean_closure_set(v___f_1157_, 2, v_inst_1147_);
        leanh::lean_closure_set(v___f_1157_, 3, v_inst_1148_);
        leanh::lean_closure_set(v___f_1157_, 4, v_inst_1149_);
        leanh::lean_closure_set(v___f_1157_, 5, v_inst_1150_);
        leanh::lean_closure_set(v___f_1157_, 6, v_m_1152_);
        leanh::lean_closure_set(v___f_1157_, 7, v_toBind_1156_);
        leanh::lean_closure_set(v___f_1157_, 8, v_k_1151_);
        v___x_1158_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
            v_inst_1148_,
            v_inst_1147_,
            v_inst_1146_,
            v_inst_1149_,
            v_inst_1150_,
        );
        v___x_1159_ = leanh::lean_apply_4(
            v_toBind_1156_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1158_,
            v___f_1157_,
        );
        return v___x_1159_;
    } else {
        let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_1151_);
        v___x_1160_ = l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
            v_inst_1146_,
            v_inst_1147_,
            v_inst_1148_,
            v_inst_1149_,
            v_inst_1150_,
            v_m_1152_,
        );
        return v___x_1160_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm(
    mut v_M_1161_: *mut leanh::LeanObject,
    mut v_inst_1162_: *mut leanh::LeanObject,
    mut v_inst_1163_: *mut leanh::LeanObject,
    mut v_inst_1164_: *mut leanh::LeanObject,
    mut v_inst_1165_: *mut leanh::LeanObject,
    mut v_inst_1166_: *mut leanh::LeanObject,
    mut v_k_1167_: *mut leanh::LeanObject,
    mut v_m_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_k_1167_, v_m_1168_);
    return v___x_1169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1170_: *mut leanh::LeanObject,
    mut v_acc_1171_: *mut leanh::LeanObject,
    mut v_toPure_1172_: *mut leanh::LeanObject,
    mut v_____do__lift_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_mkAppB(v_____do__lift_1170_, v_acc_1171_, v_____do__lift_1173_);
    v___x_1175_ =
        leanh::lean_apply_2(v_toPure_1172_, leanh::lean_box(0), v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__1(
    mut v_acc_1176_: *mut leanh::LeanObject,
    mut v_toPure_1177_: *mut leanh::LeanObject,
    mut v_inst_1178_: *mut leanh::LeanObject,
    mut v_inst_1179_: *mut leanh::LeanObject,
    mut v_inst_1180_: *mut leanh::LeanObject,
    mut v_inst_1181_: *mut leanh::LeanObject,
    mut v_inst_1182_: *mut leanh::LeanObject,
    mut v_k_1183_: *mut leanh::LeanObject,
    mut v_toBind_1184_: *mut leanh::LeanObject,
    mut v_____do__lift_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1186_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_1186_, 0, v_____do__lift_1185_);
    leanh::lean_closure_set(v___f_1186_, 1, v_acc_1176_);
    leanh::lean_closure_set(v___f_1186_, 2, v_toPure_1177_);
    v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1178_,
        v_inst_1179_,
        v_inst_1180_,
        v_inst_1181_,
        v_inst_1182_,
        v_k_1183_,
    );
    v___x_1188_ = leanh::lean_apply_4(
        v_toBind_1184_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1187_,
        v___f_1186_,
    );
    return v___x_1188_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__3(
    mut v_acc_1189_: *mut leanh::LeanObject,
    mut v_inst_1190_: *mut leanh::LeanObject,
    mut v_inst_1191_: *mut leanh::LeanObject,
    mut v_inst_1192_: *mut leanh::LeanObject,
    mut v_inst_1193_: *mut leanh::LeanObject,
    mut v_inst_1194_: *mut leanh::LeanObject,
    mut v_p_1195_: *mut leanh::LeanObject,
    mut v_k_1196_: *mut leanh::LeanObject,
    mut v_v_1197_: *mut leanh::LeanObject,
    mut v_toBind_1198_: *mut leanh::LeanObject,
    mut v_____do__lift_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1194_);
    leanh::lean_inc_ref(v_inst_1193_);
    leanh::lean_inc(v_inst_1192_);
    leanh::lean_inc_ref(v_inst_1191_);
    leanh::lean_inc_ref(v_inst_1190_);
    v___f_1200_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__2 as *mut core::ffi::c_void, 9, 8);
    leanh::lean_closure_set(v___f_1200_, 0, v_____do__lift_1199_);
    leanh::lean_closure_set(v___f_1200_, 1, v_acc_1189_);
    leanh::lean_closure_set(v___f_1200_, 2, v_inst_1190_);
    leanh::lean_closure_set(v___f_1200_, 3, v_inst_1191_);
    leanh::lean_closure_set(v___f_1200_, 4, v_inst_1192_);
    leanh::lean_closure_set(v___f_1200_, 5, v_inst_1193_);
    leanh::lean_closure_set(v___f_1200_, 6, v_inst_1194_);
    leanh::lean_closure_set(v___f_1200_, 7, v_p_1195_);
    v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_k_1196_, v_v_1197_);
    v___x_1202_ = leanh::lean_apply_4(
        v_toBind_1198_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1201_,
        v___f_1200_,
    );
    return v___x_1202_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(
    mut v_inst_1203_: *mut leanh::LeanObject,
    mut v_inst_1204_: *mut leanh::LeanObject,
    mut v_inst_1205_: *mut leanh::LeanObject,
    mut v_inst_1206_: *mut leanh::LeanObject,
    mut v_inst_1207_: *mut leanh::LeanObject,
    mut v_p_1208_: *mut leanh::LeanObject,
    mut v_acc_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_1208_) == 0 {
        let mut v_toApplicative_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1215_: u8 = 0;
        v_toApplicative_1210_ = leanh::lean_ctor_get(v_inst_1203_, 0);
        v_toBind_1211_ = leanh::lean_ctor_get(v_inst_1203_, 1);
        leanh::lean_inc(v_toBind_1211_);
        v_toPure_1212_ = leanh::lean_ctor_get(v_toApplicative_1210_, 1);
        v_k_1213_ = leanh::lean_ctor_get(v_p_1208_, 0);
        leanh::lean_inc(v_k_1213_);
        leanh::lean_dec_ref_known(v_p_1208_, 1);
        v___x_1214_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1,
        );
        v___x_1215_ = lean_int_dec_eq(v_k_1213_, v___x_1214_);
        if v___x_1215_ == 0 {
            let mut v___f_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_toBind_1211_);
            leanh::lean_inc_ref(v_inst_1207_);
            leanh::lean_inc_ref(v_inst_1206_);
            leanh::lean_inc(v_inst_1205_);
            leanh::lean_inc_ref(v_inst_1204_);
            leanh::lean_inc_ref(v_inst_1203_);
            leanh::lean_inc(v_toPure_1212_);
            v___f_1216_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
            leanh::lean_closure_set(v___f_1216_, 0, v_acc_1209_);
            leanh::lean_closure_set(v___f_1216_, 1, v_toPure_1212_);
            leanh::lean_closure_set(v___f_1216_, 2, v_inst_1203_);
            leanh::lean_closure_set(v___f_1216_, 3, v_inst_1204_);
            leanh::lean_closure_set(v___f_1216_, 4, v_inst_1205_);
            leanh::lean_closure_set(v___f_1216_, 5, v_inst_1206_);
            leanh::lean_closure_set(v___f_1216_, 6, v_inst_1207_);
            leanh::lean_closure_set(v___f_1216_, 7, v_k_1213_);
            leanh::lean_closure_set(v___f_1216_, 8, v_toBind_1211_);
            v___x_1217_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
                v_inst_1205_,
                v_inst_1204_,
                v_inst_1203_,
                v_inst_1206_,
                v_inst_1207_,
            );
            v___x_1218_ = leanh::lean_apply_4(
                v_toBind_1211_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1217_,
                v___f_1216_,
            );
            return v___x_1218_;
        } else {
            let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_toPure_1212_);
            leanh::lean_dec(v_k_1213_);
            leanh::lean_dec(v_toBind_1211_);
            leanh::lean_dec_ref(v_inst_1207_);
            leanh::lean_dec_ref(v_inst_1206_);
            leanh::lean_dec(v_inst_1205_);
            leanh::lean_dec_ref(v_inst_1204_);
            leanh::lean_dec_ref(v_inst_1203_);
            v___x_1219_ =
                leanh::lean_apply_2(v_toPure_1212_, leanh::lean_box(0), v_acc_1209_);
            return v___x_1219_;
        }
    } else {
        let mut v_toBind_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1220_ = leanh::lean_ctor_get(v_inst_1203_, 1);
        leanh::lean_inc_n(v_toBind_1220_, 2);
        v_k_1221_ = leanh::lean_ctor_get(v_p_1208_, 0);
        leanh::lean_inc(v_k_1221_);
        v_v_1222_ = leanh::lean_ctor_get(v_p_1208_, 1);
        leanh::lean_inc(v_v_1222_);
        v_p_1223_ = leanh::lean_ctor_get(v_p_1208_, 2);
        leanh::lean_inc_ref(v_p_1223_);
        leanh::lean_dec_ref_known(v_p_1208_, 3);
        leanh::lean_inc_ref(v_inst_1207_);
        leanh::lean_inc_ref(v_inst_1206_);
        leanh::lean_inc(v_inst_1205_);
        leanh::lean_inc_ref(v_inst_1204_);
        leanh::lean_inc_ref(v_inst_1203_);
        v___f_1224_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__3 as *mut core::ffi::c_void, 11, 10);
        leanh::lean_closure_set(v___f_1224_, 0, v_acc_1209_);
        leanh::lean_closure_set(v___f_1224_, 1, v_inst_1203_);
        leanh::lean_closure_set(v___f_1224_, 2, v_inst_1204_);
        leanh::lean_closure_set(v___f_1224_, 3, v_inst_1205_);
        leanh::lean_closure_set(v___f_1224_, 4, v_inst_1206_);
        leanh::lean_closure_set(v___f_1224_, 5, v_inst_1207_);
        leanh::lean_closure_set(v___f_1224_, 6, v_p_1223_);
        leanh::lean_closure_set(v___f_1224_, 7, v_k_1221_);
        leanh::lean_closure_set(v___f_1224_, 8, v_v_1222_);
        leanh::lean_closure_set(v___f_1224_, 9, v_toBind_1220_);
        v___x_1225_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
            v_inst_1205_,
            v_inst_1204_,
            v_inst_1203_,
            v_inst_1206_,
            v_inst_1207_,
        );
        v___x_1226_ = leanh::lean_apply_4(
            v_toBind_1220_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1225_,
            v___f_1224_,
        );
        return v___x_1226_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__2(
    mut v_____do__lift_1227_: *mut leanh::LeanObject,
    mut v_acc_1228_: *mut leanh::LeanObject,
    mut v_inst_1229_: *mut leanh::LeanObject,
    mut v_inst_1230_: *mut leanh::LeanObject,
    mut v_inst_1231_: *mut leanh::LeanObject,
    mut v_inst_1232_: *mut leanh::LeanObject,
    mut v_inst_1233_: *mut leanh::LeanObject,
    mut v_p_1234_: *mut leanh::LeanObject,
    mut v_____do__lift_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = l_Lean_mkAppB(v_____do__lift_1227_, v_acc_1228_, v_____do__lift_1235_);
    v___x_1237_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_p_1234_, v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go(
    mut v_M_1238_: *mut leanh::LeanObject,
    mut v_inst_1239_: *mut leanh::LeanObject,
    mut v_inst_1240_: *mut leanh::LeanObject,
    mut v_inst_1241_: *mut leanh::LeanObject,
    mut v_inst_1242_: *mut leanh::LeanObject,
    mut v_inst_1243_: *mut leanh::LeanObject,
    mut v_p_1244_: *mut leanh::LeanObject,
    mut v_acc_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v_inst_1243_, v_p_1244_, v_acc_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___redArg___lam__0(
    mut v_inst_1247_: *mut leanh::LeanObject,
    mut v_inst_1248_: *mut leanh::LeanObject,
    mut v_inst_1249_: *mut leanh::LeanObject,
    mut v_inst_1250_: *mut leanh::LeanObject,
    mut v_inst_1251_: *mut leanh::LeanObject,
    mut v_p_1252_: *mut leanh::LeanObject,
    mut v_____do__lift_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_p_1252_, v_____do__lift_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
    mut v_inst_1255_: *mut leanh::LeanObject,
    mut v_inst_1256_: *mut leanh::LeanObject,
    mut v_inst_1257_: *mut leanh::LeanObject,
    mut v_inst_1258_: *mut leanh::LeanObject,
    mut v_inst_1259_: *mut leanh::LeanObject,
    mut v_p_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_1260_) == 0 {
        let mut v_k_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_1261_ = leanh::lean_ctor_get(v_p_1260_, 0);
        leanh::lean_inc(v_k_1261_);
        leanh::lean_dec_ref_known(v_p_1260_, 1);
        v___x_1262_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
            v_inst_1255_,
            v_inst_1256_,
            v_inst_1257_,
            v_inst_1258_,
            v_inst_1259_,
            v_k_1261_,
        );
        return v___x_1262_;
    } else {
        let mut v_toBind_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1263_ = leanh::lean_ctor_get(v_inst_1255_, 1);
        leanh::lean_inc(v_toBind_1263_);
        v_k_1264_ = leanh::lean_ctor_get(v_p_1260_, 0);
        leanh::lean_inc(v_k_1264_);
        v_v_1265_ = leanh::lean_ctor_get(v_p_1260_, 1);
        leanh::lean_inc(v_v_1265_);
        v_p_1266_ = leanh::lean_ctor_get(v_p_1260_, 2);
        leanh::lean_inc_ref(v_p_1266_);
        leanh::lean_dec_ref_known(v_p_1260_, 3);
        leanh::lean_inc_ref(v_inst_1259_);
        leanh::lean_inc_ref(v_inst_1258_);
        leanh::lean_inc(v_inst_1257_);
        leanh::lean_inc_ref(v_inst_1256_);
        leanh::lean_inc_ref(v_inst_1255_);
        v___f_1267_ = leanh::lean_alloc_closure(
            l_Lean_Grind_CommRing_Poly_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_1267_, 0, v_inst_1255_);
        leanh::lean_closure_set(v___f_1267_, 1, v_inst_1256_);
        leanh::lean_closure_set(v___f_1267_, 2, v_inst_1257_);
        leanh::lean_closure_set(v___f_1267_, 3, v_inst_1258_);
        leanh::lean_closure_set(v___f_1267_, 4, v_inst_1259_);
        leanh::lean_closure_set(v___f_1267_, 5, v_p_1266_);
        v___x_1268_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_k_1264_, v_v_1265_);
        v___x_1269_ = leanh::lean_apply_4(
            v_toBind_1263_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1268_,
            v___f_1267_,
        );
        return v___x_1269_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr(
    mut v_M_1270_: *mut leanh::LeanObject,
    mut v_inst_1271_: *mut leanh::LeanObject,
    mut v_inst_1272_: *mut leanh::LeanObject,
    mut v_inst_1273_: *mut leanh::LeanObject,
    mut v_inst_1274_: *mut leanh::LeanObject,
    mut v_inst_1275_: *mut leanh::LeanObject,
    mut v_p_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
        v_inst_1271_,
        v_inst_1272_,
        v_inst_1273_,
        v_inst_1274_,
        v_inst_1275_,
        v_p_1276_,
    );
    return v___x_1277_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__0(
    mut v_k_1278_: *mut leanh::LeanObject,
    mut v_toPure_1279_: *mut leanh::LeanObject,
    mut v_____do__lift_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_mkNatLit(v_k_1278_);
    v___x_1282_ = l_Lean_Expr_app___override(v_____do__lift_1280_, v___x_1281_);
    v___x_1283_ =
        leanh::lean_apply_2(v_toPure_1279_, leanh::lean_box(0), v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1(
    mut v_k_1284_: *mut leanh::LeanObject,
    mut v_toPure_1285_: *mut leanh::LeanObject,
    mut v_____do__lift_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = l_Lean_mkIntLit(v_k_1284_);
    v___x_1288_ = l_Lean_Expr_app___override(v_____do__lift_1286_, v___x_1287_);
    v___x_1289_ =
        leanh::lean_apply_2(v_toPure_1285_, leanh::lean_box(0), v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1___boxed(
    mut v_k_1290_: *mut leanh::LeanObject,
    mut v_toPure_1291_: *mut leanh::LeanObject,
    mut v_____do__lift_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1(v_k_1290_, v_toPure_1291_, v_____do__lift_1292_);
    leanh::lean_dec(v_k_1290_);
    return v_res_1293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__2(
    mut v_____do__lift_1294_: *mut leanh::LeanObject,
    mut v_toPure_1295_: *mut leanh::LeanObject,
    mut v_____do__lift_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Expr_app___override(v_____do__lift_1294_, v_____do__lift_1296_);
    v___x_1298_ =
        leanh::lean_apply_2(v_toPure_1295_, leanh::lean_box(0), v___x_1297_);
    return v___x_1298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__13(
    mut v_k_1299_: *mut leanh::LeanObject,
    mut v_____do__lift_1300_: *mut leanh::LeanObject,
    mut v_toPure_1301_: *mut leanh::LeanObject,
    mut v_____do__lift_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1303_ = l_Lean_mkNatLit(v_k_1299_);
    v___x_1304_ = l_Lean_mkAppB(v_____do__lift_1300_, v_____do__lift_1302_, v___x_1303_);
    v___x_1305_ =
        leanh::lean_apply_2(v_toPure_1301_, leanh::lean_box(0), v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__4(
    mut v_____do__lift_1306_: *mut leanh::LeanObject,
    mut v_____do__lift_1307_: *mut leanh::LeanObject,
    mut v_toPure_1308_: *mut leanh::LeanObject,
    mut v_____do__lift_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Lean_mkAppB(
        v_____do__lift_1306_,
        v_____do__lift_1307_,
        v_____do__lift_1309_,
    );
    v___x_1311_ =
        leanh::lean_apply_2(v_toPure_1308_, leanh::lean_box(0), v___x_1310_);
    return v___x_1311_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__5(
    mut v_____do__lift_1312_: *mut leanh::LeanObject,
    mut v_toPure_1313_: *mut leanh::LeanObject,
    mut v_inst_1314_: *mut leanh::LeanObject,
    mut v_inst_1315_: *mut leanh::LeanObject,
    mut v_inst_1316_: *mut leanh::LeanObject,
    mut v_inst_1317_: *mut leanh::LeanObject,
    mut v_inst_1318_: *mut leanh::LeanObject,
    mut v_getVar_1319_: *mut leanh::LeanObject,
    mut v_b_1320_: *mut leanh::LeanObject,
    mut v_toBind_1321_: *mut leanh::LeanObject,
    mut v_____do__lift_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1323_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__4 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_1323_, 0, v_____do__lift_1312_);
    leanh::lean_closure_set(v___f_1323_, 1, v_____do__lift_1322_);
    leanh::lean_closure_set(v___f_1323_, 2, v_toPure_1313_);
    v___x_1324_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_getVar_1319_, v_b_1320_);
    v___x_1325_ = leanh::lean_apply_4(
        v_toBind_1321_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1324_,
        v___f_1323_,
    );
    return v___x_1325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6(
    mut v_toPure_1326_: *mut leanh::LeanObject,
    mut v_inst_1327_: *mut leanh::LeanObject,
    mut v_inst_1328_: *mut leanh::LeanObject,
    mut v_inst_1329_: *mut leanh::LeanObject,
    mut v_inst_1330_: *mut leanh::LeanObject,
    mut v_inst_1331_: *mut leanh::LeanObject,
    mut v_getVar_1332_: *mut leanh::LeanObject,
    mut v_b_1333_: *mut leanh::LeanObject,
    mut v_toBind_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_____do__lift_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1334_);
    leanh::lean_inc_ref(v_getVar_1332_);
    leanh::lean_inc_ref(v_inst_1331_);
    leanh::lean_inc_ref(v_inst_1330_);
    leanh::lean_inc(v_inst_1329_);
    leanh::lean_inc_ref(v_inst_1328_);
    leanh::lean_inc_ref(v_inst_1327_);
    v___f_1337_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__5 as *mut core::ffi::c_void, 11, 10);
    leanh::lean_closure_set(v___f_1337_, 0, v_____do__lift_1336_);
    leanh::lean_closure_set(v___f_1337_, 1, v_toPure_1326_);
    leanh::lean_closure_set(v___f_1337_, 2, v_inst_1327_);
    leanh::lean_closure_set(v___f_1337_, 3, v_inst_1328_);
    leanh::lean_closure_set(v___f_1337_, 4, v_inst_1329_);
    leanh::lean_closure_set(v___f_1337_, 5, v_inst_1330_);
    leanh::lean_closure_set(v___f_1337_, 6, v_inst_1331_);
    leanh::lean_closure_set(v___f_1337_, 7, v_getVar_1332_);
    leanh::lean_closure_set(v___f_1337_, 8, v_b_1333_);
    leanh::lean_closure_set(v___f_1337_, 9, v_toBind_1334_);
    v___x_1338_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_getVar_1332_, v_a_1335_);
    v___x_1339_ = leanh::lean_apply_4(
        v_toBind_1334_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1338_,
        v___f_1337_,
    );
    return v___x_1339_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__7(
    mut v_k_1340_: *mut leanh::LeanObject,
    mut v_toPure_1341_: *mut leanh::LeanObject,
    mut v_inst_1342_: *mut leanh::LeanObject,
    mut v_inst_1343_: *mut leanh::LeanObject,
    mut v_inst_1344_: *mut leanh::LeanObject,
    mut v_inst_1345_: *mut leanh::LeanObject,
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_getVar_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_toBind_1349_: *mut leanh::LeanObject,
    mut v_____do__lift_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1351_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__13 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_1351_, 0, v_k_1340_);
    leanh::lean_closure_set(v___f_1351_, 1, v_____do__lift_1350_);
    leanh::lean_closure_set(v___f_1351_, 2, v_toPure_1341_);
    v___x_1352_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_getVar_1347_, v_a_1348_);
    v___x_1353_ = leanh::lean_apply_4(
        v_toBind_1349_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1352_,
        v___f_1351_,
    );
    return v___x_1353_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(
    mut v_inst_1354_: *mut leanh::LeanObject,
    mut v_inst_1355_: *mut leanh::LeanObject,
    mut v_inst_1356_: *mut leanh::LeanObject,
    mut v_inst_1357_: *mut leanh::LeanObject,
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_getVar_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_a_1360_) {
        0 => {
            let mut v_k_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_getVar_1359_);
            v_k_1361_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc(v_k_1361_);
            leanh::lean_dec_ref_known(v_a_1360_, 1);
            v___x_1362_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
                v_inst_1354_,
                v_inst_1355_,
                v_inst_1356_,
                v_inst_1357_,
                v_inst_1358_,
                v_k_1361_,
            );
            return v___x_1362_;
        }
        1 => {
            let mut v_toApplicative_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1363_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            leanh::lean_dec_ref(v_getVar_1359_);
            leanh::lean_dec_ref(v_inst_1355_);
            v_toBind_1364_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc(v_toBind_1364_);
            v_toPure_1365_ = leanh::lean_ctor_get(v_toApplicative_1363_, 1);
            v_k_1366_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc(v_k_1366_);
            leanh::lean_dec_ref_known(v_a_1360_, 1);
            leanh::lean_inc(v_toPure_1365_);
            v___f_1367_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
            leanh::lean_closure_set(v___f_1367_, 0, v_k_1366_);
            leanh::lean_closure_set(v___f_1367_, 1, v_toPure_1365_);
            v___x_1368_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
                v_inst_1356_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1369_ = leanh::lean_apply_4(
                v_toBind_1364_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1368_,
                v___f_1367_,
            );
            return v___x_1369_;
        }
        2 => {
            let mut v_toApplicative_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1370_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            leanh::lean_dec_ref(v_getVar_1359_);
            leanh::lean_dec_ref(v_inst_1355_);
            v_toBind_1371_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc(v_toBind_1371_);
            v_toPure_1372_ = leanh::lean_ctor_get(v_toApplicative_1370_, 1);
            v_k_1373_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc(v_k_1373_);
            leanh::lean_dec_ref_known(v_a_1360_, 1);
            leanh::lean_inc(v_toPure_1372_);
            v___f_1374_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
            leanh::lean_closure_set(v___f_1374_, 0, v_k_1373_);
            leanh::lean_closure_set(v___f_1374_, 1, v_toPure_1372_);
            v___x_1375_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
                v_inst_1356_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1376_ = leanh::lean_apply_4(
                v_toBind_1371_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1375_,
                v___f_1374_,
            );
            return v___x_1376_;
        }
        3 => {
            let mut v_toApplicative_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1377_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            leanh::lean_inc_ref(v_toApplicative_1377_);
            leanh::lean_dec_ref(v_inst_1358_);
            leanh::lean_dec_ref(v_inst_1357_);
            leanh::lean_dec(v_inst_1356_);
            leanh::lean_dec_ref(v_inst_1355_);
            leanh::lean_dec_ref(v_inst_1354_);
            v_toPure_1378_ = leanh::lean_ctor_get(v_toApplicative_1377_, 1);
            leanh::lean_inc(v_toPure_1378_);
            leanh::lean_dec_ref(v_toApplicative_1377_);
            v_i_1379_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc(v_i_1379_);
            leanh::lean_dec_ref_known(v_a_1360_, 1);
            v___x_1380_ = leanh::lean_apply_1(v_getVar_1359_, v_i_1379_);
            v___x_1381_ =
                leanh::lean_apply_2(v_toPure_1378_, leanh::lean_box(0), v___x_1380_);
            return v___x_1381_;
        }
        4 => {
            let mut v_toApplicative_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1382_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1383_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc_n(v_toBind_1383_, 2);
            v_toPure_1384_ = leanh::lean_ctor_get(v_toApplicative_1382_, 1);
            v_a_1385_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc_ref(v_a_1385_);
            leanh::lean_dec_ref_known(v_a_1360_, 1);
            leanh::lean_inc_ref(v_inst_1358_);
            leanh::lean_inc_ref(v_inst_1357_);
            leanh::lean_inc(v_inst_1356_);
            leanh::lean_inc_ref(v_inst_1355_);
            leanh::lean_inc_ref(v_inst_1354_);
            leanh::lean_inc(v_toPure_1384_);
            v___f_1386_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__3 as *mut core::ffi::c_void, 10, 9);
            leanh::lean_closure_set(v___f_1386_, 0, v_toPure_1384_);
            leanh::lean_closure_set(v___f_1386_, 1, v_inst_1354_);
            leanh::lean_closure_set(v___f_1386_, 2, v_inst_1355_);
            leanh::lean_closure_set(v___f_1386_, 3, v_inst_1356_);
            leanh::lean_closure_set(v___f_1386_, 4, v_inst_1357_);
            leanh::lean_closure_set(v___f_1386_, 5, v_inst_1358_);
            leanh::lean_closure_set(v___f_1386_, 6, v_getVar_1359_);
            leanh::lean_closure_set(v___f_1386_, 7, v_a_1385_);
            leanh::lean_closure_set(v___f_1386_, 8, v_toBind_1383_);
            v___x_1387_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1388_ = leanh::lean_apply_4(
                v_toBind_1383_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1387_,
                v___f_1386_,
            );
            return v___x_1388_;
        }
        5 => {
            let mut v_toApplicative_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1389_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1390_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc_n(v_toBind_1390_, 2);
            v_toPure_1391_ = leanh::lean_ctor_get(v_toApplicative_1389_, 1);
            v_a_1392_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc_ref(v_a_1392_);
            v_b_1393_ = leanh::lean_ctor_get(v_a_1360_, 1);
            leanh::lean_inc_ref(v_b_1393_);
            leanh::lean_dec_ref_known(v_a_1360_, 2);
            leanh::lean_inc_ref(v_inst_1358_);
            leanh::lean_inc_ref(v_inst_1357_);
            leanh::lean_inc(v_inst_1356_);
            leanh::lean_inc_ref(v_inst_1355_);
            leanh::lean_inc_ref(v_inst_1354_);
            leanh::lean_inc(v_toPure_1391_);
            v___f_1394_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            leanh::lean_closure_set(v___f_1394_, 0, v_toPure_1391_);
            leanh::lean_closure_set(v___f_1394_, 1, v_inst_1354_);
            leanh::lean_closure_set(v___f_1394_, 2, v_inst_1355_);
            leanh::lean_closure_set(v___f_1394_, 3, v_inst_1356_);
            leanh::lean_closure_set(v___f_1394_, 4, v_inst_1357_);
            leanh::lean_closure_set(v___f_1394_, 5, v_inst_1358_);
            leanh::lean_closure_set(v___f_1394_, 6, v_getVar_1359_);
            leanh::lean_closure_set(v___f_1394_, 7, v_b_1393_);
            leanh::lean_closure_set(v___f_1394_, 8, v_toBind_1390_);
            leanh::lean_closure_set(v___f_1394_, 9, v_a_1392_);
            v___x_1395_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1396_ = leanh::lean_apply_4(
                v_toBind_1390_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1395_,
                v___f_1394_,
            );
            return v___x_1396_;
        }
        6 => {
            let mut v_toApplicative_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1397_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1398_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc_n(v_toBind_1398_, 2);
            v_toPure_1399_ = leanh::lean_ctor_get(v_toApplicative_1397_, 1);
            v_a_1400_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc_ref(v_a_1400_);
            v_b_1401_ = leanh::lean_ctor_get(v_a_1360_, 1);
            leanh::lean_inc_ref(v_b_1401_);
            leanh::lean_dec_ref_known(v_a_1360_, 2);
            leanh::lean_inc_ref(v_inst_1358_);
            leanh::lean_inc_ref(v_inst_1357_);
            leanh::lean_inc(v_inst_1356_);
            leanh::lean_inc_ref(v_inst_1355_);
            leanh::lean_inc_ref(v_inst_1354_);
            leanh::lean_inc(v_toPure_1399_);
            v___f_1402_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            leanh::lean_closure_set(v___f_1402_, 0, v_toPure_1399_);
            leanh::lean_closure_set(v___f_1402_, 1, v_inst_1354_);
            leanh::lean_closure_set(v___f_1402_, 2, v_inst_1355_);
            leanh::lean_closure_set(v___f_1402_, 3, v_inst_1356_);
            leanh::lean_closure_set(v___f_1402_, 4, v_inst_1357_);
            leanh::lean_closure_set(v___f_1402_, 5, v_inst_1358_);
            leanh::lean_closure_set(v___f_1402_, 6, v_getVar_1359_);
            leanh::lean_closure_set(v___f_1402_, 7, v_b_1401_);
            leanh::lean_closure_set(v___f_1402_, 8, v_toBind_1398_);
            leanh::lean_closure_set(v___f_1402_, 9, v_a_1400_);
            v___x_1403_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1404_ = leanh::lean_apply_4(
                v_toBind_1398_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1403_,
                v___f_1402_,
            );
            return v___x_1404_;
        }
        7 => {
            let mut v_toApplicative_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1405_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1406_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc_n(v_toBind_1406_, 2);
            v_toPure_1407_ = leanh::lean_ctor_get(v_toApplicative_1405_, 1);
            v_a_1408_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc_ref(v_a_1408_);
            v_b_1409_ = leanh::lean_ctor_get(v_a_1360_, 1);
            leanh::lean_inc_ref(v_b_1409_);
            leanh::lean_dec_ref_known(v_a_1360_, 2);
            leanh::lean_inc_ref(v_inst_1358_);
            leanh::lean_inc_ref(v_inst_1357_);
            leanh::lean_inc(v_inst_1356_);
            leanh::lean_inc_ref(v_inst_1355_);
            leanh::lean_inc_ref(v_inst_1354_);
            leanh::lean_inc(v_toPure_1407_);
            v___f_1410_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            leanh::lean_closure_set(v___f_1410_, 0, v_toPure_1407_);
            leanh::lean_closure_set(v___f_1410_, 1, v_inst_1354_);
            leanh::lean_closure_set(v___f_1410_, 2, v_inst_1355_);
            leanh::lean_closure_set(v___f_1410_, 3, v_inst_1356_);
            leanh::lean_closure_set(v___f_1410_, 4, v_inst_1357_);
            leanh::lean_closure_set(v___f_1410_, 5, v_inst_1358_);
            leanh::lean_closure_set(v___f_1410_, 6, v_getVar_1359_);
            leanh::lean_closure_set(v___f_1410_, 7, v_b_1409_);
            leanh::lean_closure_set(v___f_1410_, 8, v_toBind_1406_);
            leanh::lean_closure_set(v___f_1410_, 9, v_a_1408_);
            v___x_1411_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1412_ = leanh::lean_apply_4(
                v_toBind_1406_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1411_,
                v___f_1410_,
            );
            return v___x_1412_;
        }
        _ => {
            let mut v_toApplicative_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1413_ = leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1414_ = leanh::lean_ctor_get(v_inst_1354_, 1);
            leanh::lean_inc_n(v_toBind_1414_, 2);
            v_toPure_1415_ = leanh::lean_ctor_get(v_toApplicative_1413_, 1);
            v_a_1416_ = leanh::lean_ctor_get(v_a_1360_, 0);
            leanh::lean_inc_ref(v_a_1416_);
            v_k_1417_ = leanh::lean_ctor_get(v_a_1360_, 1);
            leanh::lean_inc(v_k_1417_);
            leanh::lean_dec_ref_known(v_a_1360_, 2);
            leanh::lean_inc_ref(v_inst_1358_);
            leanh::lean_inc_ref(v_inst_1357_);
            leanh::lean_inc(v_inst_1356_);
            leanh::lean_inc_ref(v_inst_1355_);
            leanh::lean_inc_ref(v_inst_1354_);
            leanh::lean_inc(v_toPure_1415_);
            v___f_1418_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__7 as *mut core::ffi::c_void, 11, 10);
            leanh::lean_closure_set(v___f_1418_, 0, v_k_1417_);
            leanh::lean_closure_set(v___f_1418_, 1, v_toPure_1415_);
            leanh::lean_closure_set(v___f_1418_, 2, v_inst_1354_);
            leanh::lean_closure_set(v___f_1418_, 3, v_inst_1355_);
            leanh::lean_closure_set(v___f_1418_, 4, v_inst_1356_);
            leanh::lean_closure_set(v___f_1418_, 5, v_inst_1357_);
            leanh::lean_closure_set(v___f_1418_, 6, v_inst_1358_);
            leanh::lean_closure_set(v___f_1418_, 7, v_getVar_1359_);
            leanh::lean_closure_set(v___f_1418_, 8, v_a_1416_);
            leanh::lean_closure_set(v___f_1418_, 9, v_toBind_1414_);
            v___x_1419_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1420_ = leanh::lean_apply_4(
                v_toBind_1414_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1419_,
                v___f_1418_,
            );
            return v___x_1420_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__3(
    mut v_toPure_1421_: *mut leanh::LeanObject,
    mut v_inst_1422_: *mut leanh::LeanObject,
    mut v_inst_1423_: *mut leanh::LeanObject,
    mut v_inst_1424_: *mut leanh::LeanObject,
    mut v_inst_1425_: *mut leanh::LeanObject,
    mut v_inst_1426_: *mut leanh::LeanObject,
    mut v_getVar_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
    mut v_toBind_1429_: *mut leanh::LeanObject,
    mut v_____do__lift_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1431_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1431_, 0, v_____do__lift_1430_);
    leanh::lean_closure_set(v___f_1431_, 1, v_toPure_1421_);
    v___x_1432_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1422_, v_inst_1423_, v_inst_1424_, v_inst_1425_, v_inst_1426_, v_getVar_1427_, v_a_1428_);
    v___x_1433_ = leanh::lean_apply_4(
        v_toBind_1429_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1432_,
        v___f_1431_,
    );
    return v___x_1433_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go(
    mut v_M_1434_: *mut leanh::LeanObject,
    mut v_inst_1435_: *mut leanh::LeanObject,
    mut v_inst_1436_: *mut leanh::LeanObject,
    mut v_inst_1437_: *mut leanh::LeanObject,
    mut v_inst_1438_: *mut leanh::LeanObject,
    mut v_inst_1439_: *mut leanh::LeanObject,
    mut v_getVar_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1435_, v_inst_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_getVar_1440_, v_a_1441_);
    return v___x_1442_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore___redArg(
    mut v_inst_1443_: *mut leanh::LeanObject,
    mut v_inst_1444_: *mut leanh::LeanObject,
    mut v_inst_1445_: *mut leanh::LeanObject,
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_getVar_1448_: *mut leanh::LeanObject,
    mut v_e_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_getVar_1448_, v_e_1449_);
    return v___x_1450_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore(
    mut v_M_1451_: *mut leanh::LeanObject,
    mut v_inst_1452_: *mut leanh::LeanObject,
    mut v_inst_1453_: *mut leanh::LeanObject,
    mut v_inst_1454_: *mut leanh::LeanObject,
    mut v_inst_1455_: *mut leanh::LeanObject,
    mut v_inst_1456_: *mut leanh::LeanObject,
    mut v_getVar_1457_: *mut leanh::LeanObject,
    mut v_e_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_inst_1456_, v_getVar_1457_, v_e_1458_);
    return v___x_1459_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0(
    mut v_ring_1460_: *mut leanh::LeanObject,
    mut v___x_1461_: *mut leanh::LeanObject,
    mut v_x_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    v_vars_1463_ = leanh::lean_ctor_get(v_ring_1460_, 14);
    v_size_1464_ = leanh::lean_ctor_get(v_vars_1463_, 2);
    v___x_1465_ = lean_nat_dec_lt(v_x_1462_, v_size_1464_);
    if v___x_1465_ == 0 {
        let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1466_ = l_outOfBounds___redArg(v___x_1461_);
        return v___x_1466_;
    } else {
        let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1467_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1461_, v_vars_1463_, v_x_1462_);
        return v___x_1467_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0___boxed(
    mut v_ring_1468_: *mut leanh::LeanObject,
    mut v___x_1469_: *mut leanh::LeanObject,
    mut v_x_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0(
        v_ring_1468_,
        v___x_1469_,
        v_x_1470_,
    );
    leanh::lean_dec(v_x_1470_);
    leanh::lean_dec_ref(v___x_1469_);
    leanh::lean_dec_ref(v_ring_1468_);
    return v_res_1471_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__1(
    mut v___x_1472_: *mut leanh::LeanObject,
    mut v_inst_1473_: *mut leanh::LeanObject,
    mut v_inst_1474_: *mut leanh::LeanObject,
    mut v_inst_1475_: *mut leanh::LeanObject,
    mut v_inst_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_e_1478_: *mut leanh::LeanObject,
    mut v_ring_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1480_ = leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1480_, 0, v_ring_1479_);
    leanh::lean_closure_set(v___f_1480_, 1, v___x_1472_);
    v___x_1481_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1473_, v_inst_1474_, v_inst_1475_, v_inst_1476_, v_inst_1477_, v___f_1480_, v_e_1478_);
    return v___x_1481_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg(
    mut v_inst_1482_: *mut leanh::LeanObject,
    mut v_inst_1483_: *mut leanh::LeanObject,
    mut v_inst_1484_: *mut leanh::LeanObject,
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_e_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1488_ = leanh::lean_ctor_get(v_inst_1482_, 1);
    leanh::lean_inc(v_toBind_1488_);
    v_getRing_1489_ = leanh::lean_ctor_get(v_inst_1486_, 0);
    leanh::lean_inc(v_getRing_1489_);
    v___x_1490_ = l_Lean_instInhabitedExpr;
    v___f_1491_ = leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1491_, 0, v___x_1490_);
    leanh::lean_closure_set(v___f_1491_, 1, v_inst_1482_);
    leanh::lean_closure_set(v___f_1491_, 2, v_inst_1483_);
    leanh::lean_closure_set(v___f_1491_, 3, v_inst_1484_);
    leanh::lean_closure_set(v___f_1491_, 4, v_inst_1485_);
    leanh::lean_closure_set(v___f_1491_, 5, v_inst_1486_);
    leanh::lean_closure_set(v___f_1491_, 6, v_e_1487_);
    v___x_1492_ = leanh::lean_apply_4(
        v_toBind_1488_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1489_,
        v___f_1491_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr(
    mut v_M_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_inst_1495_: *mut leanh::LeanObject,
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_inst_1497_: *mut leanh::LeanObject,
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_e_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Lean_Grind_CommRing_Expr_denoteExpr___redArg(
        v_inst_1494_,
        v_inst_1495_,
        v_inst_1496_,
        v_inst_1497_,
        v_inst_1498_,
        v_e_1499_,
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0(
    mut v___x_1501_: *mut leanh::LeanObject,
    mut v_vars_1502_: *mut leanh::LeanObject,
    mut v_x_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = lean_array_get_borrowed(v___x_1501_, v_vars_1502_, v_x_1503_);
    leanh::lean_inc(v___x_1504_);
    return v___x_1504_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0___boxed(
    mut v___x_1505_: *mut leanh::LeanObject,
    mut v_vars_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0(
        v___x_1505_,
        v_vars_1506_,
        v_x_1507_,
    );
    leanh::lean_dec(v_x_1507_);
    leanh::lean_dec_ref(v_vars_1506_);
    leanh::lean_dec_ref(v___x_1505_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg(
    mut v_inst_1509_: *mut leanh::LeanObject,
    mut v_inst_1510_: *mut leanh::LeanObject,
    mut v_inst_1511_: *mut leanh::LeanObject,
    mut v_inst_1512_: *mut leanh::LeanObject,
    mut v_inst_1513_: *mut leanh::LeanObject,
    mut v_vars_1514_: *mut leanh::LeanObject,
    mut v_e_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_instInhabitedExpr;
    v___f_1517_ = leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1517_, 0, v___x_1516_);
    leanh::lean_closure_set(v___f_1517_, 1, v_vars_1514_);
    v___x_1518_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_inst_1513_, v___f_1517_, v_e_1515_);
    return v___x_1518_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27(
    mut v_M_1519_: *mut leanh::LeanObject,
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_inst_1522_: *mut leanh::LeanObject,
    mut v_inst_1523_: *mut leanh::LeanObject,
    mut v_inst_1524_: *mut leanh::LeanObject,
    mut v_vars_1525_: *mut leanh::LeanObject,
    mut v_e_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg(
        v_inst_1520_,
        v_inst_1521_,
        v_inst_1522_,
        v_inst_1523_,
        v_inst_1524_,
        v_vars_1525_,
        v_e_1526_,
    );
    return v___x_1527_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0(
    mut v_a_1531_: *mut leanh::LeanObject,
    mut v_b_1532_: *mut leanh::LeanObject,
    mut v_toPure_1533_: *mut leanh::LeanObject,
    mut v_r_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_1535_ = leanh::lean_ctor_get(v_r_1534_, 1);
    leanh::lean_inc_ref(v_type_1535_);
    v_u_1536_ = leanh::lean_ctor_get(v_r_1534_, 2);
    leanh::lean_inc(v_u_1536_);
    leanh::lean_dec_ref(v_r_1534_);
    v___x_1537_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1;
    v___x_1538_ = l_Lean_Level_succ___override(v_u_1536_);
    v___x_1539_ = leanh::lean_box(0);
    v___x_1540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1540_, 0, v___x_1538_);
    leanh::lean_ctor_set(v___x_1540_, 1, v___x_1539_);
    v___x_1541_ = l_Lean_mkConst(v___x_1537_, v___x_1540_);
    v___x_1542_ = l_Lean_mkApp3(v___x_1541_, v_type_1535_, v_a_1531_, v_b_1532_);
    v___x_1543_ =
        leanh::lean_apply_2(v_toPure_1533_, leanh::lean_box(0), v___x_1542_);
    return v___x_1543_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_inst_1545_: *mut leanh::LeanObject,
    mut v_a_1546_: *mut leanh::LeanObject,
    mut v_b_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1548_ = leanh::lean_ctor_get(v_inst_1544_, 0);
    leanh::lean_inc_ref(v_toApplicative_1548_);
    v_toBind_1549_ = leanh::lean_ctor_get(v_inst_1544_, 1);
    leanh::lean_inc(v_toBind_1549_);
    leanh::lean_dec_ref(v_inst_1544_);
    v_getRing_1550_ = leanh::lean_ctor_get(v_inst_1545_, 0);
    leanh::lean_inc(v_getRing_1550_);
    leanh::lean_dec_ref(v_inst_1545_);
    v_toPure_1551_ = leanh::lean_ctor_get(v_toApplicative_1548_, 1);
    leanh::lean_inc(v_toPure_1551_);
    leanh::lean_dec_ref(v_toApplicative_1548_);
    v___f_1552_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_1552_, 0, v_a_1546_);
    leanh::lean_closure_set(v___f_1552_, 1, v_b_1547_);
    leanh::lean_closure_set(v___f_1552_, 2, v_toPure_1551_);
    v___x_1553_ = leanh::lean_apply_4(
        v_toBind_1549_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1550_,
        v___f_1552_,
    );
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq(
    mut v_M_1554_: *mut leanh::LeanObject,
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
    mut v_a_1557_: *mut leanh::LeanObject,
    mut v_b_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1555_, v_inst_1556_, v_a_1557_, v_b_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__0(
    mut v_inst_1560_: *mut leanh::LeanObject,
    mut v_inst_1561_: *mut leanh::LeanObject,
    mut v_____do__lift_1562_: *mut leanh::LeanObject,
    mut v_____do__lift_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1560_, v_inst_1561_, v_____do__lift_1562_, v_____do__lift_1563_);
    return v___x_1564_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_1565_: *mut leanh::LeanObject,
    mut v_inst_1566_: *mut leanh::LeanObject,
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_inst_1568_: *mut leanh::LeanObject,
    mut v_inst_1569_: *mut leanh::LeanObject,
    mut v_toBind_1570_: *mut leanh::LeanObject,
    mut v_____do__lift_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1566_);
    leanh::lean_inc_ref(v_inst_1565_);
    v___f_1572_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1572_, 0, v_inst_1565_);
    leanh::lean_closure_set(v___f_1572_, 1, v_inst_1566_);
    leanh::lean_closure_set(v___f_1572_, 2, v_____do__lift_1571_);
    v___x_1573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1,
    );
    v___x_1574_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1565_,
        v_inst_1567_,
        v_inst_1568_,
        v_inst_1569_,
        v_inst_1566_,
        v___x_1573_,
    );
    v___x_1575_ = leanh::lean_apply_4(
        v_toBind_1570_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1574_,
        v___f_1572_,
    );
    return v___x_1575_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg(
    mut v_inst_1576_: *mut leanh::LeanObject,
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_inst_1579_: *mut leanh::LeanObject,
    mut v_inst_1580_: *mut leanh::LeanObject,
    mut v_c_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1582_ = leanh::lean_ctor_get(v_inst_1576_, 1);
    leanh::lean_inc_n(v_toBind_1582_, 2);
    v_p_1583_ = leanh::lean_ctor_get(v_c_1581_, 0);
    leanh::lean_inc_ref(v_p_1583_);
    leanh::lean_dec_ref(v_c_1581_);
    leanh::lean_inc_ref(v_inst_1579_);
    leanh::lean_inc(v_inst_1578_);
    leanh::lean_inc_ref(v_inst_1577_);
    leanh::lean_inc_ref(v_inst_1580_);
    leanh::lean_inc_ref(v_inst_1576_);
    v___f_1584_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1584_, 0, v_inst_1576_);
    leanh::lean_closure_set(v___f_1584_, 1, v_inst_1580_);
    leanh::lean_closure_set(v___f_1584_, 2, v_inst_1577_);
    leanh::lean_closure_set(v___f_1584_, 3, v_inst_1578_);
    leanh::lean_closure_set(v___f_1584_, 4, v_inst_1579_);
    leanh::lean_closure_set(v___f_1584_, 5, v_toBind_1582_);
    v___x_1585_ = l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
        v_inst_1576_,
        v_inst_1577_,
        v_inst_1578_,
        v_inst_1579_,
        v_inst_1580_,
        v_p_1583_,
    );
    v___x_1586_ = leanh::lean_apply_4(
        v_toBind_1582_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1585_,
        v___f_1584_,
    );
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr(
    mut v_M_1587_: *mut leanh::LeanObject,
    mut v_inst_1588_: *mut leanh::LeanObject,
    mut v_inst_1589_: *mut leanh::LeanObject,
    mut v_inst_1590_: *mut leanh::LeanObject,
    mut v_inst_1591_: *mut leanh::LeanObject,
    mut v_inst_1592_: *mut leanh::LeanObject,
    mut v_c_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg(
        v_inst_1588_,
        v_inst_1589_,
        v_inst_1590_,
        v_inst_1591_,
        v_inst_1592_,
        v_c_1593_,
    );
    return v___x_1594_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
    mut v_inst_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
    mut v_inst_1597_: *mut leanh::LeanObject,
    mut v_inst_1598_: *mut leanh::LeanObject,
    mut v_inst_1599_: *mut leanh::LeanObject,
    mut v_d_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1600_);
    v___x_1602_ = l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
        v_inst_1595_,
        v_inst_1596_,
        v_inst_1597_,
        v_inst_1598_,
        v_inst_1599_,
        v___x_1601_,
    );
    return v___x_1602_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg___boxed(
    mut v_inst_1603_: *mut leanh::LeanObject,
    mut v_inst_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_inst_1607_: *mut leanh::LeanObject,
    mut v_d_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
        v_inst_1603_,
        v_inst_1604_,
        v_inst_1605_,
        v_inst_1606_,
        v_inst_1607_,
        v_d_1608_,
    );
    leanh::lean_dec_ref(v_d_1608_);
    return v_res_1609_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr(
    mut v_M_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
    mut v_inst_1612_: *mut leanh::LeanObject,
    mut v_inst_1613_: *mut leanh::LeanObject,
    mut v_inst_1614_: *mut leanh::LeanObject,
    mut v_inst_1615_: *mut leanh::LeanObject,
    mut v_d_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
        v_inst_1611_,
        v_inst_1612_,
        v_inst_1613_,
        v_inst_1614_,
        v_inst_1615_,
        v_d_1616_,
    );
    return v___x_1617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___boxed(
    mut v_M_1618_: *mut leanh::LeanObject,
    mut v_inst_1619_: *mut leanh::LeanObject,
    mut v_inst_1620_: *mut leanh::LeanObject,
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v_inst_1623_: *mut leanh::LeanObject,
    mut v_d_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr(
        v_M_1618_,
        v_inst_1619_,
        v_inst_1620_,
        v_inst_1621_,
        v_inst_1622_,
        v_inst_1623_,
        v_d_1624_,
    );
    leanh::lean_dec_ref(v_d_1624_);
    return v_res_1625_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__0(
    mut v_toPure_1626_: *mut leanh::LeanObject,
    mut v_____do__lift_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = l_Lean_mkNot(v_____do__lift_1627_);
    v___x_1629_ =
        leanh::lean_apply_2(v_toPure_1626_, leanh::lean_box(0), v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_inst_1631_: *mut leanh::LeanObject,
    mut v_____do__lift_1632_: *mut leanh::LeanObject,
    mut v_toBind_1633_: *mut leanh::LeanObject,
    mut v___f_1634_: *mut leanh::LeanObject,
    mut v_____do__lift_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1636_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1630_, v_inst_1631_, v_____do__lift_1632_, v_____do__lift_1635_);
    v___x_1637_ = leanh::lean_apply_4(
        v_toBind_1633_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1636_,
        v___f_1634_,
    );
    return v___x_1637_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__2(
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_toBind_1640_: *mut leanh::LeanObject,
    mut v___f_1641_: *mut leanh::LeanObject,
    mut v_inst_1642_: *mut leanh::LeanObject,
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_inst_1644_: *mut leanh::LeanObject,
    mut v_____do__lift_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1640_);
    leanh::lean_inc_ref(v_inst_1639_);
    leanh::lean_inc_ref(v_inst_1638_);
    v___f_1646_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1646_, 0, v_inst_1638_);
    leanh::lean_closure_set(v___f_1646_, 1, v_inst_1639_);
    leanh::lean_closure_set(v___f_1646_, 2, v_____do__lift_1645_);
    leanh::lean_closure_set(v___f_1646_, 3, v_toBind_1640_);
    leanh::lean_closure_set(v___f_1646_, 4, v___f_1641_);
    v___x_1647_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1,
    );
    v___x_1648_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1638_,
        v_inst_1642_,
        v_inst_1643_,
        v_inst_1644_,
        v_inst_1639_,
        v___x_1647_,
    );
    v___x_1649_ = leanh::lean_apply_4(
        v_toBind_1640_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1648_,
        v___f_1646_,
    );
    return v___x_1649_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg(
    mut v_inst_1650_: *mut leanh::LeanObject,
    mut v_inst_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_inst_1653_: *mut leanh::LeanObject,
    mut v_inst_1654_: *mut leanh::LeanObject,
    mut v_c_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1656_ = leanh::lean_ctor_get(v_inst_1650_, 0);
    v_toBind_1657_ = leanh::lean_ctor_get(v_inst_1650_, 1);
    leanh::lean_inc_n(v_toBind_1657_, 2);
    v_d_1658_ = leanh::lean_ctor_get(v_c_1655_, 4);
    v_toPure_1659_ = leanh::lean_ctor_get(v_toApplicative_1656_, 1);
    leanh::lean_inc_ref(v_inst_1654_);
    leanh::lean_inc_ref(v_inst_1653_);
    leanh::lean_inc(v_inst_1652_);
    leanh::lean_inc_ref(v_inst_1651_);
    leanh::lean_inc_ref(v_inst_1650_);
    v___x_1660_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
        v_inst_1650_,
        v_inst_1651_,
        v_inst_1652_,
        v_inst_1653_,
        v_inst_1654_,
        v_d_1658_,
    );
    leanh::lean_inc(v_toPure_1659_);
    v___f_1661_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1661_, 0, v_toPure_1659_);
    v___f_1662_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1662_, 0, v_inst_1650_);
    leanh::lean_closure_set(v___f_1662_, 1, v_inst_1654_);
    leanh::lean_closure_set(v___f_1662_, 2, v_toBind_1657_);
    leanh::lean_closure_set(v___f_1662_, 3, v___f_1661_);
    leanh::lean_closure_set(v___f_1662_, 4, v_inst_1651_);
    leanh::lean_closure_set(v___f_1662_, 5, v_inst_1652_);
    leanh::lean_closure_set(v___f_1662_, 6, v_inst_1653_);
    v___x_1663_ = leanh::lean_apply_4(
        v_toBind_1657_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1660_,
        v___f_1662_,
    );
    return v___x_1663_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___boxed(
    mut v_inst_1664_: *mut leanh::LeanObject,
    mut v_inst_1665_: *mut leanh::LeanObject,
    mut v_inst_1666_: *mut leanh::LeanObject,
    mut v_inst_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_c_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg(
        v_inst_1664_,
        v_inst_1665_,
        v_inst_1666_,
        v_inst_1667_,
        v_inst_1668_,
        v_c_1669_,
    );
    leanh::lean_dec_ref(v_c_1669_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr(
    mut v_M_1671_: *mut leanh::LeanObject,
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_inst_1674_: *mut leanh::LeanObject,
    mut v_inst_1675_: *mut leanh::LeanObject,
    mut v_inst_1676_: *mut leanh::LeanObject,
    mut v_c_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg(
        v_inst_1672_,
        v_inst_1673_,
        v_inst_1674_,
        v_inst_1675_,
        v_inst_1676_,
        v_c_1677_,
    );
    return v___x_1678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___boxed(
    mut v_M_1679_: *mut leanh::LeanObject,
    mut v_inst_1680_: *mut leanh::LeanObject,
    mut v_inst_1681_: *mut leanh::LeanObject,
    mut v_inst_1682_: *mut leanh::LeanObject,
    mut v_inst_1683_: *mut leanh::LeanObject,
    mut v_inst_1684_: *mut leanh::LeanObject,
    mut v_c_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr(
        v_M_1679_,
        v_inst_1680_,
        v_inst_1681_,
        v_inst_1682_,
        v_inst_1683_,
        v_inst_1684_,
        v_c_1685_,
    );
    leanh::lean_dec_ref(v_c_1685_);
    return v_res_1686_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
}