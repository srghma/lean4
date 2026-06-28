// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_nat_dec_eq, lean_nat_dec_lt,
};
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9341924117480681831 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17636616155771105671 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__0(
    mut v_n_844_: *mut crate::leanh::LeanObject,
    mut v_toPure_845_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Expr_app___override(v_____do__lift_846_, v_n_844_);
    v___x_848_ = crate::leanh::lean_apply_2(v_toPure_845_, crate::leanh::lean_box(0), v___x_847_);
    return v___x_848_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_851_ = lean_nat_to_int(v___x_850_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1(
    mut v___x_852_: *mut crate::leanh::LeanObject,
    mut v___x_853_: *mut crate::leanh::LeanObject,
    mut v_type_854_: *mut crate::leanh::LeanObject,
    mut v_n_855_: *mut crate::leanh::LeanObject,
    mut v_k_856_: *mut crate::leanh::LeanObject,
    mut v_toPure_857_: *mut crate::leanh::LeanObject,
    mut v_inst_858_: *mut crate::leanh::LeanObject,
    mut v_inst_859_: *mut crate::leanh::LeanObject,
    mut v_inst_860_: *mut crate::leanh::LeanObject,
    mut v_inst_861_: *mut crate::leanh::LeanObject,
    mut v_inst_862_: *mut crate::leanh::LeanObject,
    mut v_toBind_863_: *mut crate::leanh::LeanObject,
    mut v_ofNatInst_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    v___x_865_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___closed__0;
    v___x_866_ = l_Lean_Name_mkStr2(v___x_852_, v___x_865_);
    v___x_867_ = l_Lean_mkConst(v___x_866_, v___x_853_);
    v_n_868_ = l_Lean_mkApp3(v___x_867_, v_type_854_, v_n_855_, v_ofNatInst_864_);
    v___x_869_ = crate::leanh::lean_obj_once(
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
        let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_863_);
        crate::leanh::lean_dec_ref(v_inst_862_);
        crate::leanh::lean_dec_ref(v_inst_861_);
        crate::leanh::lean_dec_ref(v_inst_860_);
        crate::leanh::lean_dec_ref(v_inst_859_);
        crate::leanh::lean_dec(v_inst_858_);
        v___x_871_ = crate::leanh::lean_apply_2(v_toPure_857_, crate::leanh::lean_box(0), v_n_868_);
        return v___x_871_;
    } else {
        let mut v___f_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_872_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_872_, 0, v_n_868_);
        crate::leanh::lean_closure_set(v___f_872_, 1, v_toPure_857_);
        v___x_873_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
            v_inst_858_,
            v_inst_859_,
            v_inst_860_,
            v_inst_861_,
            v_inst_862_,
        );
        v___x_874_ = crate::leanh::lean_apply_4(
            v_toBind_863_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_873_,
            v___f_872_,
        );
        return v___x_874_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___boxed(
    mut v___x_875_: *mut crate::leanh::LeanObject,
    mut v___x_876_: *mut crate::leanh::LeanObject,
    mut v_type_877_: *mut crate::leanh::LeanObject,
    mut v_n_878_: *mut crate::leanh::LeanObject,
    mut v_k_879_: *mut crate::leanh::LeanObject,
    mut v_toPure_880_: *mut crate::leanh::LeanObject,
    mut v_inst_881_: *mut crate::leanh::LeanObject,
    mut v_inst_882_: *mut crate::leanh::LeanObject,
    mut v_inst_883_: *mut crate::leanh::LeanObject,
    mut v_inst_884_: *mut crate::leanh::LeanObject,
    mut v_inst_885_: *mut crate::leanh::LeanObject,
    mut v_toBind_886_: *mut crate::leanh::LeanObject,
    mut v_ofNatInst_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_k_879_);
    return v_res_888_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__2(
    mut v___f_889_: *mut crate::leanh::LeanObject,
    mut v_ofNatInst_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = crate::leanh::lean_apply_1(v___f_889_, v_ofNatInst_890_);
    return v___x_891_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4(
    mut v_toPure_900_: *mut crate::leanh::LeanObject,
    mut v_toBind_901_: *mut crate::leanh::LeanObject,
    mut v___f_902_: *mut crate::leanh::LeanObject,
    mut v___x_903_: *mut crate::leanh::LeanObject,
    mut v_type_904_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_905_: *mut crate::leanh::LeanObject,
    mut v_n_906_: *mut crate::leanh::LeanObject,
    mut v___f_907_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_908_) == 1 {
        let mut v_val_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_907_);
        crate::leanh::lean_dec_ref(v_n_906_);
        crate::leanh::lean_dec_ref(v_semiringInst_905_);
        crate::leanh::lean_dec_ref(v_type_904_);
        crate::leanh::lean_dec(v___x_903_);
        v_val_909_ = crate::leanh::lean_ctor_get(v_____do__lift_908_, 0);
        crate::leanh::lean_inc(v_val_909_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_908_, 1);
        v___x_910_ =
            crate::leanh::lean_apply_2(v_toPure_900_, crate::leanh::lean_box(0), v_val_909_);
        v___x_911_ = crate::leanh::lean_apply_4(
            v_toBind_901_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_910_,
            v___f_902_,
        );
        return v___x_911_;
    } else {
        let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____do__lift_908_);
        crate::leanh::lean_dec(v___f_902_);
        v___x_912_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4___closed__3;
        v___x_913_ = l_Lean_mkConst(v___x_912_, v___x_903_);
        v___x_914_ = l_Lean_mkApp3(v___x_913_, v_type_904_, v_semiringInst_905_, v_n_906_);
        v___x_915_ =
            crate::leanh::lean_apply_2(v_toPure_900_, crate::leanh::lean_box(0), v___x_914_);
        v___x_916_ = crate::leanh::lean_apply_4(
            v_toBind_901_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_915_,
            v___f_907_,
        );
        return v___x_916_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3(
    mut v_k_920_: *mut crate::leanh::LeanObject,
    mut v_toPure_921_: *mut crate::leanh::LeanObject,
    mut v_inst_922_: *mut crate::leanh::LeanObject,
    mut v_inst_923_: *mut crate::leanh::LeanObject,
    mut v_inst_924_: *mut crate::leanh::LeanObject,
    mut v_inst_925_: *mut crate::leanh::LeanObject,
    mut v_inst_926_: *mut crate::leanh::LeanObject,
    mut v_toBind_927_: *mut crate::leanh::LeanObject,
    mut v_ring_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_929_ = crate::leanh::lean_ctor_get(v_ring_928_, 1);
    crate::leanh::lean_inc_ref_n(v_type_929_, 3);
    v_u_930_ = crate::leanh::lean_ctor_get(v_ring_928_, 2);
    crate::leanh::lean_inc(v_u_930_);
    v_semiringInst_931_ = crate::leanh::lean_ctor_get(v_ring_928_, 4);
    crate::leanh::lean_inc_ref(v_semiringInst_931_);
    crate::leanh::lean_dec_ref(v_ring_928_);
    v___x_932_ = lean_nat_abs(v_k_920_);
    v_n_933_ = l_Lean_mkRawNatLit(v___x_932_);
    v___x_934_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__0;
    v___x_935_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3___closed__1;
    v___x_936_ = crate::leanh::lean_box(0);
    v___x_937_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_937_, 0, v_u_930_);
    crate::leanh::lean_ctor_set(v___x_937_, 1, v___x_936_);
    crate::leanh::lean_inc_n(v_toBind_927_, 2);
    crate::leanh::lean_inc(v_inst_922_);
    crate::leanh::lean_inc(v_toPure_921_);
    crate::leanh::lean_inc_ref_n(v_n_933_, 2);
    crate::leanh::lean_inc_ref_n(v___x_937_, 2);
    v___f_938_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_938_, 0, v___x_934_);
    crate::leanh::lean_closure_set(v___f_938_, 1, v___x_937_);
    crate::leanh::lean_closure_set(v___f_938_, 2, v_type_929_);
    crate::leanh::lean_closure_set(v___f_938_, 3, v_n_933_);
    crate::leanh::lean_closure_set(v___f_938_, 4, v_k_920_);
    crate::leanh::lean_closure_set(v___f_938_, 5, v_toPure_921_);
    crate::leanh::lean_closure_set(v___f_938_, 6, v_inst_922_);
    crate::leanh::lean_closure_set(v___f_938_, 7, v_inst_923_);
    crate::leanh::lean_closure_set(v___f_938_, 8, v_inst_924_);
    crate::leanh::lean_closure_set(v___f_938_, 9, v_inst_925_);
    crate::leanh::lean_closure_set(v___f_938_, 10, v_inst_926_);
    crate::leanh::lean_closure_set(v___f_938_, 11, v_toBind_927_);
    v___f_939_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_939_, 0, v___f_938_);
    crate::leanh::lean_inc_ref(v___f_939_);
    v___f_940_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_940_, 0, v_toPure_921_);
    crate::leanh::lean_closure_set(v___f_940_, 1, v_toBind_927_);
    crate::leanh::lean_closure_set(v___f_940_, 2, v___f_939_);
    crate::leanh::lean_closure_set(v___f_940_, 3, v___x_937_);
    crate::leanh::lean_closure_set(v___f_940_, 4, v_type_929_);
    crate::leanh::lean_closure_set(v___f_940_, 5, v_semiringInst_931_);
    crate::leanh::lean_closure_set(v___f_940_, 6, v_n_933_);
    crate::leanh::lean_closure_set(v___f_940_, 7, v___f_939_);
    v___x_941_ = l_Lean_mkConst(v___x_935_, v___x_937_);
    v___x_942_ = l_Lean_mkAppB(v___x_941_, v_type_929_, v_n_933_);
    v___x_943_ = crate::leanh::lean_box(0);
    v___x_944_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_synthInstance_x3f___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_944_, 0, v___x_942_);
    crate::leanh::lean_closure_set(v___x_944_, 1, v___x_943_);
    v___x_945_ = crate::leanh::lean_apply_2(v_inst_922_, crate::leanh::lean_box(0), v___x_944_);
    v___x_946_ = crate::leanh::lean_apply_4(
        v_toBind_927_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_945_,
        v___f_940_,
    );
    return v___x_946_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
    mut v_inst_947_: *mut crate::leanh::LeanObject,
    mut v_inst_948_: *mut crate::leanh::LeanObject,
    mut v_inst_949_: *mut crate::leanh::LeanObject,
    mut v_inst_950_: *mut crate::leanh::LeanObject,
    mut v_inst_951_: *mut crate::leanh::LeanObject,
    mut v_k_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_953_ = crate::leanh::lean_ctor_get(v_inst_947_, 0);
    v_toBind_954_ = crate::leanh::lean_ctor_get(v_inst_947_, 1);
    crate::leanh::lean_inc_n(v_toBind_954_, 2);
    v_getRing_955_ = crate::leanh::lean_ctor_get(v_inst_951_, 0);
    crate::leanh::lean_inc(v_getRing_955_);
    v_toPure_956_ = crate::leanh::lean_ctor_get(v_toApplicative_953_, 1);
    crate::leanh::lean_inc(v_toPure_956_);
    v___f_957_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg___lam__3 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_957_, 0, v_k_952_);
    crate::leanh::lean_closure_set(v___f_957_, 1, v_toPure_956_);
    crate::leanh::lean_closure_set(v___f_957_, 2, v_inst_949_);
    crate::leanh::lean_closure_set(v___f_957_, 3, v_inst_948_);
    crate::leanh::lean_closure_set(v___f_957_, 4, v_inst_947_);
    crate::leanh::lean_closure_set(v___f_957_, 5, v_inst_950_);
    crate::leanh::lean_closure_set(v___f_957_, 6, v_inst_951_);
    crate::leanh::lean_closure_set(v___f_957_, 7, v_toBind_954_);
    v___x_958_ = crate::leanh::lean_apply_4(
        v_toBind_954_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_955_,
        v___f_957_,
    );
    return v___x_958_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum(
    mut v_M_959_: *mut crate::leanh::LeanObject,
    mut v_inst_960_: *mut crate::leanh::LeanObject,
    mut v_inst_961_: *mut crate::leanh::LeanObject,
    mut v_inst_962_: *mut crate::leanh::LeanObject,
    mut v_inst_963_: *mut crate::leanh::LeanObject,
    mut v_inst_964_: *mut crate::leanh::LeanObject,
    mut v_k_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_967_: *mut crate::leanh::LeanObject,
    mut v_k_968_: *mut crate::leanh::LeanObject,
    mut v___y_969_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_971_ = crate::leanh::lean_ctor_get(v_toApplicative_967_, 1);
    crate::leanh::lean_inc(v_toPure_971_);
    crate::leanh::lean_dec_ref(v_toApplicative_967_);
    v___x_972_ = l_Lean_mkNatLit(v_k_968_);
    v___x_973_ = l_Lean_mkAppB(v_____do__lift_970_, v___y_969_, v___x_972_);
    v___x_974_ = crate::leanh::lean_apply_2(v_toPure_971_, crate::leanh::lean_box(0), v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1(
    mut v_pw_975_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_976_: *mut crate::leanh::LeanObject,
    mut v_inst_977_: *mut crate::leanh::LeanObject,
    mut v_inst_978_: *mut crate::leanh::LeanObject,
    mut v_inst_979_: *mut crate::leanh::LeanObject,
    mut v_inst_980_: *mut crate::leanh::LeanObject,
    mut v_inst_981_: *mut crate::leanh::LeanObject,
    mut v_toBind_982_: *mut crate::leanh::LeanObject,
    mut v___x_983_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut v___f_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_985_ = crate::leanh::lean_ctor_get(v_____do__lift_984_, 14);
                v_x_986_ = crate::leanh::lean_ctor_get(v_pw_975_, 0);
                crate::leanh::lean_inc(v_x_986_);
                v_k_987_ = crate::leanh::lean_ctor_get(v_pw_975_, 1);
                crate::leanh::lean_inc(v_k_987_);
                crate::leanh::lean_dec_ref(v_pw_975_);
                v_size_997_ = crate::leanh::lean_ctor_get(v_vars_985_, 2);
                v___x_998_ = lean_nat_dec_lt(v_x_986_, v_size_997_);
                if v___x_998_ == 0 {
                    crate::leanh::lean_dec(v_x_986_);
                    v___x_999_ = l_outOfBounds___redArg(v___x_983_);
                    v___y_989_ = v___x_999_;
                    state = 1;
                    continue;
                } else {
                    v___x_1000_ =
                        l_Lean_PersistentArray_get_x21___redArg(v___x_983_, v_vars_985_, v_x_986_);
                    crate::leanh::lean_dec(v_x_986_);
                    v___y_989_ = v___x_1000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_990_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_991_ = lean_nat_dec_eq(v_k_987_, v___x_990_);
                if v___x_991_ == 0 {
                    v___f_992_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__0
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_992_, 0, v_toApplicative_976_);
                    crate::leanh::lean_closure_set(v___f_992_, 1, v_k_987_);
                    crate::leanh::lean_closure_set(v___f_992_, 2, v___y_989_);
                    v___x_993_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
                        v_inst_977_,
                        v_inst_978_,
                        v_inst_979_,
                        v_inst_980_,
                        v_inst_981_,
                    );
                    v___x_994_ = crate::leanh::lean_apply_4(
                        v_toBind_982_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_993_,
                        v___f_992_,
                    );
                    return v___x_994_;
                } else {
                    crate::leanh::lean_dec(v_k_987_);
                    crate::leanh::lean_dec(v_toBind_982_);
                    crate::leanh::lean_dec_ref(v_inst_981_);
                    crate::leanh::lean_dec_ref(v_inst_980_);
                    crate::leanh::lean_dec_ref(v_inst_979_);
                    crate::leanh::lean_dec_ref(v_inst_978_);
                    crate::leanh::lean_dec(v_inst_977_);
                    v_toPure_995_ = crate::leanh::lean_ctor_get(v_toApplicative_976_, 1);
                    crate::leanh::lean_inc(v_toPure_995_);
                    crate::leanh::lean_dec_ref(v_toApplicative_976_);
                    v___x_996_ = crate::leanh::lean_apply_2(
                        v_toPure_995_,
                        crate::leanh::lean_box(0),
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
    mut v_pw_1001_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_inst_1004_: *mut crate::leanh::LeanObject,
    mut v_inst_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_inst_1007_: *mut crate::leanh::LeanObject,
    mut v_toBind_1008_: *mut crate::leanh::LeanObject,
    mut v___x_1009_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_____do__lift_1010_);
    crate::leanh::lean_dec_ref(v___x_1009_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
    mut v_inst_1012_: *mut crate::leanh::LeanObject,
    mut v_inst_1013_: *mut crate::leanh::LeanObject,
    mut v_inst_1014_: *mut crate::leanh::LeanObject,
    mut v_inst_1015_: *mut crate::leanh::LeanObject,
    mut v_inst_1016_: *mut crate::leanh::LeanObject,
    mut v_pw_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1018_ = crate::leanh::lean_ctor_get(v_inst_1012_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1018_);
    v_toBind_1019_ = crate::leanh::lean_ctor_get(v_inst_1012_, 1);
    crate::leanh::lean_inc_n(v_toBind_1019_, 2);
    v_getRing_1020_ = crate::leanh::lean_ctor_get(v_inst_1016_, 0);
    crate::leanh::lean_inc(v_getRing_1020_);
    v___x_1021_ = l_Lean_instInhabitedExpr;
    v___f_1022_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Power_denoteExpr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1022_, 0, v_pw_1017_);
    crate::leanh::lean_closure_set(v___f_1022_, 1, v_toApplicative_1018_);
    crate::leanh::lean_closure_set(v___f_1022_, 2, v_inst_1014_);
    crate::leanh::lean_closure_set(v___f_1022_, 3, v_inst_1013_);
    crate::leanh::lean_closure_set(v___f_1022_, 4, v_inst_1012_);
    crate::leanh::lean_closure_set(v___f_1022_, 5, v_inst_1015_);
    crate::leanh::lean_closure_set(v___f_1022_, 6, v_inst_1016_);
    crate::leanh::lean_closure_set(v___f_1022_, 7, v_toBind_1019_);
    crate::leanh::lean_closure_set(v___f_1022_, 8, v___x_1021_);
    v___x_1023_ = crate::leanh::lean_apply_4(
        v_toBind_1019_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1020_,
        v___f_1022_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr(
    mut v_M_1024_: *mut crate::leanh::LeanObject,
    mut v_inst_1025_: *mut crate::leanh::LeanObject,
    mut v_inst_1026_: *mut crate::leanh::LeanObject,
    mut v_inst_1027_: *mut crate::leanh::LeanObject,
    mut v_inst_1028_: *mut crate::leanh::LeanObject,
    mut v_inst_1029_: *mut crate::leanh::LeanObject,
    mut v_pw_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_acc_1032_: *mut crate::leanh::LeanObject,
    mut v_inst_1033_: *mut crate::leanh::LeanObject,
    mut v_inst_1034_: *mut crate::leanh::LeanObject,
    mut v_inst_1035_: *mut crate::leanh::LeanObject,
    mut v_inst_1036_: *mut crate::leanh::LeanObject,
    mut v_inst_1037_: *mut crate::leanh::LeanObject,
    mut v_m_1038_: *mut crate::leanh::LeanObject,
    mut v_p_1039_: *mut crate::leanh::LeanObject,
    mut v_toBind_1040_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1037_);
    crate::leanh::lean_inc_ref(v_inst_1036_);
    crate::leanh::lean_inc(v_inst_1035_);
    crate::leanh::lean_inc_ref(v_inst_1034_);
    crate::leanh::lean_inc_ref(v_inst_1033_);
    v___f_1042_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 9, 8);
    crate::leanh::lean_closure_set(v___f_1042_, 0, v_____do__lift_1041_);
    crate::leanh::lean_closure_set(v___f_1042_, 1, v_acc_1032_);
    crate::leanh::lean_closure_set(v___f_1042_, 2, v_inst_1033_);
    crate::leanh::lean_closure_set(v___f_1042_, 3, v_inst_1034_);
    crate::leanh::lean_closure_set(v___f_1042_, 4, v_inst_1035_);
    crate::leanh::lean_closure_set(v___f_1042_, 5, v_inst_1036_);
    crate::leanh::lean_closure_set(v___f_1042_, 6, v_inst_1037_);
    crate::leanh::lean_closure_set(v___f_1042_, 7, v_m_1038_);
    v___x_1043_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
        v_inst_1033_,
        v_inst_1034_,
        v_inst_1035_,
        v_inst_1036_,
        v_inst_1037_,
        v_p_1039_,
    );
    v___x_1044_ = crate::leanh::lean_apply_4(
        v_toBind_1040_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1043_,
        v___f_1042_,
    );
    return v___x_1044_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(
    mut v_inst_1045_: *mut crate::leanh::LeanObject,
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_inst_1047_: *mut crate::leanh::LeanObject,
    mut v_inst_1048_: *mut crate::leanh::LeanObject,
    mut v_inst_1049_: *mut crate::leanh::LeanObject,
    mut v_m_1050_: *mut crate::leanh::LeanObject,
    mut v_acc_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_1050_) == 0 {
        let mut v_toApplicative_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1052_ = crate::leanh::lean_ctor_get(v_inst_1045_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1052_);
        crate::leanh::lean_dec_ref(v_inst_1049_);
        crate::leanh::lean_dec_ref(v_inst_1048_);
        crate::leanh::lean_dec(v_inst_1047_);
        crate::leanh::lean_dec_ref(v_inst_1046_);
        crate::leanh::lean_dec_ref(v_inst_1045_);
        v_toPure_1053_ = crate::leanh::lean_ctor_get(v_toApplicative_1052_, 1);
        crate::leanh::lean_inc(v_toPure_1053_);
        crate::leanh::lean_dec_ref(v_toApplicative_1052_);
        v___x_1054_ =
            crate::leanh::lean_apply_2(v_toPure_1053_, crate::leanh::lean_box(0), v_acc_1051_);
        return v___x_1054_;
    } else {
        let mut v_toBind_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1055_ = crate::leanh::lean_ctor_get(v_inst_1045_, 1);
        crate::leanh::lean_inc_n(v_toBind_1055_, 2);
        v_p_1056_ = crate::leanh::lean_ctor_get(v_m_1050_, 0);
        crate::leanh::lean_inc_ref(v_p_1056_);
        v_m_1057_ = crate::leanh::lean_ctor_get(v_m_1050_, 1);
        crate::leanh::lean_inc(v_m_1057_);
        crate::leanh::lean_dec_ref_known(v_m_1050_, 2);
        crate::leanh::lean_inc_ref(v_inst_1049_);
        crate::leanh::lean_inc_ref(v_inst_1048_);
        crate::leanh::lean_inc(v_inst_1047_);
        crate::leanh::lean_inc_ref(v_inst_1046_);
        crate::leanh::lean_inc_ref(v_inst_1045_);
        v___f_1058_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
        crate::leanh::lean_closure_set(v___f_1058_, 0, v_acc_1051_);
        crate::leanh::lean_closure_set(v___f_1058_, 1, v_inst_1045_);
        crate::leanh::lean_closure_set(v___f_1058_, 2, v_inst_1046_);
        crate::leanh::lean_closure_set(v___f_1058_, 3, v_inst_1047_);
        crate::leanh::lean_closure_set(v___f_1058_, 4, v_inst_1048_);
        crate::leanh::lean_closure_set(v___f_1058_, 5, v_inst_1049_);
        crate::leanh::lean_closure_set(v___f_1058_, 6, v_m_1057_);
        crate::leanh::lean_closure_set(v___f_1058_, 7, v_p_1056_);
        crate::leanh::lean_closure_set(v___f_1058_, 8, v_toBind_1055_);
        v___x_1059_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
            v_inst_1047_,
            v_inst_1046_,
            v_inst_1045_,
            v_inst_1048_,
            v_inst_1049_,
        );
        v___x_1060_ = crate::leanh::lean_apply_4(
            v_toBind_1055_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1059_,
            v___f_1058_,
        );
        return v___x_1060_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1061_: *mut crate::leanh::LeanObject,
    mut v_acc_1062_: *mut crate::leanh::LeanObject,
    mut v_inst_1063_: *mut crate::leanh::LeanObject,
    mut v_inst_1064_: *mut crate::leanh::LeanObject,
    mut v_inst_1065_: *mut crate::leanh::LeanObject,
    mut v_inst_1066_: *mut crate::leanh::LeanObject,
    mut v_inst_1067_: *mut crate::leanh::LeanObject,
    mut v_m_1068_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lean_mkAppB(v_____do__lift_1061_, v_acc_1062_, v_____do__lift_1069_);
    v___x_1071_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_inst_1067_, v_m_1068_, v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go(
    mut v_M_1072_: *mut crate::leanh::LeanObject,
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
    mut v_inst_1074_: *mut crate::leanh::LeanObject,
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_inst_1077_: *mut crate::leanh::LeanObject,
    mut v_m_1078_: *mut crate::leanh::LeanObject,
    mut v_acc_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1073_, v_inst_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_m_1078_, v_acc_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___lam__0(
    mut v_inst_1081_: *mut crate::leanh::LeanObject,
    mut v_inst_1082_: *mut crate::leanh::LeanObject,
    mut v_inst_1083_: *mut crate::leanh::LeanObject,
    mut v_inst_1084_: *mut crate::leanh::LeanObject,
    mut v_inst_1085_: *mut crate::leanh::LeanObject,
    mut v_m_1086_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___redArg(v_inst_1081_, v_inst_1082_, v_inst_1083_, v_inst_1084_, v_inst_1085_, v_m_1086_, v_____do__lift_1087_);
    return v___x_1088_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1090_ = lean_nat_to_int(v___x_1089_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
    mut v_inst_1091_: *mut crate::leanh::LeanObject,
    mut v_inst_1092_: *mut crate::leanh::LeanObject,
    mut v_inst_1093_: *mut crate::leanh::LeanObject,
    mut v_inst_1094_: *mut crate::leanh::LeanObject,
    mut v_inst_1095_: *mut crate::leanh::LeanObject,
    mut v_m_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_1096_) == 0 {
        let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1097_ = crate::leanh::lean_obj_once(
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
        let mut v_toBind_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1099_ = crate::leanh::lean_ctor_get(v_inst_1091_, 1);
        crate::leanh::lean_inc(v_toBind_1099_);
        v_p_1100_ = crate::leanh::lean_ctor_get(v_m_1096_, 0);
        crate::leanh::lean_inc_ref(v_p_1100_);
        v_m_1101_ = crate::leanh::lean_ctor_get(v_m_1096_, 1);
        crate::leanh::lean_inc(v_m_1101_);
        crate::leanh::lean_dec_ref_known(v_m_1096_, 2);
        crate::leanh::lean_inc_ref(v_inst_1095_);
        crate::leanh::lean_inc_ref(v_inst_1094_);
        crate::leanh::lean_inc(v_inst_1093_);
        crate::leanh::lean_inc_ref(v_inst_1092_);
        crate::leanh::lean_inc_ref(v_inst_1091_);
        v___f_1102_ = crate::leanh::lean_alloc_closure(
            l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_1102_, 0, v_inst_1091_);
        crate::leanh::lean_closure_set(v___f_1102_, 1, v_inst_1092_);
        crate::leanh::lean_closure_set(v___f_1102_, 2, v_inst_1093_);
        crate::leanh::lean_closure_set(v___f_1102_, 3, v_inst_1094_);
        crate::leanh::lean_closure_set(v___f_1102_, 4, v_inst_1095_);
        crate::leanh::lean_closure_set(v___f_1102_, 5, v_m_1101_);
        v___x_1103_ = l_Lean_Grind_CommRing_Power_denoteExpr___redArg(
            v_inst_1091_,
            v_inst_1092_,
            v_inst_1093_,
            v_inst_1094_,
            v_inst_1095_,
            v_p_1100_,
        );
        v___x_1104_ = crate::leanh::lean_apply_4(
            v_toBind_1099_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1103_,
            v___f_1102_,
        );
        return v___x_1104_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr(
    mut v_M_1105_: *mut crate::leanh::LeanObject,
    mut v_inst_1106_: *mut crate::leanh::LeanObject,
    mut v_inst_1107_: *mut crate::leanh::LeanObject,
    mut v_inst_1108_: *mut crate::leanh::LeanObject,
    mut v_inst_1109_: *mut crate::leanh::LeanObject,
    mut v_inst_1110_: *mut crate::leanh::LeanObject,
    mut v_m_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_1113_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1114_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1115_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_1117_ = crate::leanh::lean_ctor_get(v_toApplicative_1113_, 1);
    crate::leanh::lean_inc(v_toPure_1117_);
    crate::leanh::lean_dec_ref(v_toApplicative_1113_);
    v___x_1118_ = l_Lean_mkAppB(
        v_____do__lift_1114_,
        v_____do__lift_1115_,
        v_____do__lift_1116_,
    );
    v___x_1119_ =
        crate::leanh::lean_apply_2(v_toPure_1117_, crate::leanh::lean_box(0), v___x_1118_);
    return v___x_1119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__1(
    mut v_toApplicative_1120_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1121_: *mut crate::leanh::LeanObject,
    mut v_inst_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_inst_1124_: *mut crate::leanh::LeanObject,
    mut v_inst_1125_: *mut crate::leanh::LeanObject,
    mut v_inst_1126_: *mut crate::leanh::LeanObject,
    mut v_m_1127_: *mut crate::leanh::LeanObject,
    mut v_toBind_1128_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1130_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1130_, 0, v_toApplicative_1120_);
    crate::leanh::lean_closure_set(v___f_1130_, 1, v_____do__lift_1121_);
    crate::leanh::lean_closure_set(v___f_1130_, 2, v_____do__lift_1129_);
    v___x_1131_ = l_Lean_Grind_CommRing_Mon_denoteExpr___redArg(
        v_inst_1122_,
        v_inst_1123_,
        v_inst_1124_,
        v_inst_1125_,
        v_inst_1126_,
        v_m_1127_,
    );
    v___x_1132_ = crate::leanh::lean_apply_4(
        v_toBind_1128_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1131_,
        v___f_1130_,
    );
    return v___x_1132_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__2(
    mut v_toApplicative_1133_: *mut crate::leanh::LeanObject,
    mut v_inst_1134_: *mut crate::leanh::LeanObject,
    mut v_inst_1135_: *mut crate::leanh::LeanObject,
    mut v_inst_1136_: *mut crate::leanh::LeanObject,
    mut v_inst_1137_: *mut crate::leanh::LeanObject,
    mut v_inst_1138_: *mut crate::leanh::LeanObject,
    mut v_m_1139_: *mut crate::leanh::LeanObject,
    mut v_toBind_1140_: *mut crate::leanh::LeanObject,
    mut v_k_1141_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1140_);
    crate::leanh::lean_inc_ref(v_inst_1138_);
    crate::leanh::lean_inc_ref(v_inst_1137_);
    crate::leanh::lean_inc(v_inst_1136_);
    crate::leanh::lean_inc_ref(v_inst_1135_);
    crate::leanh::lean_inc_ref(v_inst_1134_);
    v___f_1143_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
    crate::leanh::lean_closure_set(v___f_1143_, 0, v_toApplicative_1133_);
    crate::leanh::lean_closure_set(v___f_1143_, 1, v_____do__lift_1142_);
    crate::leanh::lean_closure_set(v___f_1143_, 2, v_inst_1134_);
    crate::leanh::lean_closure_set(v___f_1143_, 3, v_inst_1135_);
    crate::leanh::lean_closure_set(v___f_1143_, 4, v_inst_1136_);
    crate::leanh::lean_closure_set(v___f_1143_, 5, v_inst_1137_);
    crate::leanh::lean_closure_set(v___f_1143_, 6, v_inst_1138_);
    crate::leanh::lean_closure_set(v___f_1143_, 7, v_m_1139_);
    crate::leanh::lean_closure_set(v___f_1143_, 8, v_toBind_1140_);
    v___x_1144_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1134_,
        v_inst_1135_,
        v_inst_1136_,
        v_inst_1137_,
        v_inst_1138_,
        v_k_1141_,
    );
    v___x_1145_ = crate::leanh::lean_apply_4(
        v_toBind_1140_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1144_,
        v___f_1143_,
    );
    return v___x_1145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(
    mut v_inst_1146_: *mut crate::leanh::LeanObject,
    mut v_inst_1147_: *mut crate::leanh::LeanObject,
    mut v_inst_1148_: *mut crate::leanh::LeanObject,
    mut v_inst_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
    mut v_k_1151_: *mut crate::leanh::LeanObject,
    mut v_m_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_denoteExpr___redArg___closed__0,
    );
    v___x_1154_ = lean_int_dec_eq(v_k_1151_, v___x_1153_);
    if v___x_1154_ == 0 {
        let mut v_toApplicative_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1155_ = crate::leanh::lean_ctor_get(v_inst_1146_, 0);
        v_toBind_1156_ = crate::leanh::lean_ctor_get(v_inst_1146_, 1);
        crate::leanh::lean_inc_n(v_toBind_1156_, 2);
        crate::leanh::lean_inc_ref(v_inst_1150_);
        crate::leanh::lean_inc_ref(v_inst_1149_);
        crate::leanh::lean_inc(v_inst_1148_);
        crate::leanh::lean_inc_ref(v_inst_1147_);
        crate::leanh::lean_inc_ref(v_inst_1146_);
        crate::leanh::lean_inc_ref(v_toApplicative_1155_);
        v___f_1157_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg___lam__2 as *mut core::ffi::c_void, 10, 9);
        crate::leanh::lean_closure_set(v___f_1157_, 0, v_toApplicative_1155_);
        crate::leanh::lean_closure_set(v___f_1157_, 1, v_inst_1146_);
        crate::leanh::lean_closure_set(v___f_1157_, 2, v_inst_1147_);
        crate::leanh::lean_closure_set(v___f_1157_, 3, v_inst_1148_);
        crate::leanh::lean_closure_set(v___f_1157_, 4, v_inst_1149_);
        crate::leanh::lean_closure_set(v___f_1157_, 5, v_inst_1150_);
        crate::leanh::lean_closure_set(v___f_1157_, 6, v_m_1152_);
        crate::leanh::lean_closure_set(v___f_1157_, 7, v_toBind_1156_);
        crate::leanh::lean_closure_set(v___f_1157_, 8, v_k_1151_);
        v___x_1158_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
            v_inst_1148_,
            v_inst_1147_,
            v_inst_1146_,
            v_inst_1149_,
            v_inst_1150_,
        );
        v___x_1159_ = crate::leanh::lean_apply_4(
            v_toBind_1156_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1158_,
            v___f_1157_,
        );
        return v___x_1159_;
    } else {
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1151_);
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
    mut v_M_1161_: *mut crate::leanh::LeanObject,
    mut v_inst_1162_: *mut crate::leanh::LeanObject,
    mut v_inst_1163_: *mut crate::leanh::LeanObject,
    mut v_inst_1164_: *mut crate::leanh::LeanObject,
    mut v_inst_1165_: *mut crate::leanh::LeanObject,
    mut v_inst_1166_: *mut crate::leanh::LeanObject,
    mut v_k_1167_: *mut crate::leanh::LeanObject,
    mut v_m_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_k_1167_, v_m_1168_);
    return v___x_1169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1170_: *mut crate::leanh::LeanObject,
    mut v_acc_1171_: *mut crate::leanh::LeanObject,
    mut v_toPure_1172_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_mkAppB(v_____do__lift_1170_, v_acc_1171_, v_____do__lift_1173_);
    v___x_1175_ =
        crate::leanh::lean_apply_2(v_toPure_1172_, crate::leanh::lean_box(0), v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__1(
    mut v_acc_1176_: *mut crate::leanh::LeanObject,
    mut v_toPure_1177_: *mut crate::leanh::LeanObject,
    mut v_inst_1178_: *mut crate::leanh::LeanObject,
    mut v_inst_1179_: *mut crate::leanh::LeanObject,
    mut v_inst_1180_: *mut crate::leanh::LeanObject,
    mut v_inst_1181_: *mut crate::leanh::LeanObject,
    mut v_inst_1182_: *mut crate::leanh::LeanObject,
    mut v_k_1183_: *mut crate::leanh::LeanObject,
    mut v_toBind_1184_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1186_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1186_, 0, v_____do__lift_1185_);
    crate::leanh::lean_closure_set(v___f_1186_, 1, v_acc_1176_);
    crate::leanh::lean_closure_set(v___f_1186_, 2, v_toPure_1177_);
    v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___redArg(
        v_inst_1178_,
        v_inst_1179_,
        v_inst_1180_,
        v_inst_1181_,
        v_inst_1182_,
        v_k_1183_,
    );
    v___x_1188_ = crate::leanh::lean_apply_4(
        v_toBind_1184_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1187_,
        v___f_1186_,
    );
    return v___x_1188_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__3(
    mut v_acc_1189_: *mut crate::leanh::LeanObject,
    mut v_inst_1190_: *mut crate::leanh::LeanObject,
    mut v_inst_1191_: *mut crate::leanh::LeanObject,
    mut v_inst_1192_: *mut crate::leanh::LeanObject,
    mut v_inst_1193_: *mut crate::leanh::LeanObject,
    mut v_inst_1194_: *mut crate::leanh::LeanObject,
    mut v_p_1195_: *mut crate::leanh::LeanObject,
    mut v_k_1196_: *mut crate::leanh::LeanObject,
    mut v_v_1197_: *mut crate::leanh::LeanObject,
    mut v_toBind_1198_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1194_);
    crate::leanh::lean_inc_ref(v_inst_1193_);
    crate::leanh::lean_inc(v_inst_1192_);
    crate::leanh::lean_inc_ref(v_inst_1191_);
    crate::leanh::lean_inc_ref(v_inst_1190_);
    v___f_1200_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__2 as *mut core::ffi::c_void, 9, 8);
    crate::leanh::lean_closure_set(v___f_1200_, 0, v_____do__lift_1199_);
    crate::leanh::lean_closure_set(v___f_1200_, 1, v_acc_1189_);
    crate::leanh::lean_closure_set(v___f_1200_, 2, v_inst_1190_);
    crate::leanh::lean_closure_set(v___f_1200_, 3, v_inst_1191_);
    crate::leanh::lean_closure_set(v___f_1200_, 4, v_inst_1192_);
    crate::leanh::lean_closure_set(v___f_1200_, 5, v_inst_1193_);
    crate::leanh::lean_closure_set(v___f_1200_, 6, v_inst_1194_);
    crate::leanh::lean_closure_set(v___f_1200_, 7, v_p_1195_);
    v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_k_1196_, v_v_1197_);
    v___x_1202_ = crate::leanh::lean_apply_4(
        v_toBind_1198_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1201_,
        v___f_1200_,
    );
    return v___x_1202_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(
    mut v_inst_1203_: *mut crate::leanh::LeanObject,
    mut v_inst_1204_: *mut crate::leanh::LeanObject,
    mut v_inst_1205_: *mut crate::leanh::LeanObject,
    mut v_inst_1206_: *mut crate::leanh::LeanObject,
    mut v_inst_1207_: *mut crate::leanh::LeanObject,
    mut v_p_1208_: *mut crate::leanh::LeanObject,
    mut v_acc_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1208_) == 0 {
        let mut v_toApplicative_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1215_: u8 = 0;
        v_toApplicative_1210_ = crate::leanh::lean_ctor_get(v_inst_1203_, 0);
        v_toBind_1211_ = crate::leanh::lean_ctor_get(v_inst_1203_, 1);
        crate::leanh::lean_inc(v_toBind_1211_);
        v_toPure_1212_ = crate::leanh::lean_ctor_get(v_toApplicative_1210_, 1);
        v_k_1213_ = crate::leanh::lean_ctor_get(v_p_1208_, 0);
        crate::leanh::lean_inc(v_k_1213_);
        crate::leanh::lean_dec_ref_known(v_p_1208_, 1);
        v___x_1214_ = crate::leanh::lean_obj_once(
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
            let mut v___f_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_toBind_1211_);
            crate::leanh::lean_inc_ref(v_inst_1207_);
            crate::leanh::lean_inc_ref(v_inst_1206_);
            crate::leanh::lean_inc(v_inst_1205_);
            crate::leanh::lean_inc_ref(v_inst_1204_);
            crate::leanh::lean_inc_ref(v_inst_1203_);
            crate::leanh::lean_inc(v_toPure_1212_);
            v___f_1216_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
            crate::leanh::lean_closure_set(v___f_1216_, 0, v_acc_1209_);
            crate::leanh::lean_closure_set(v___f_1216_, 1, v_toPure_1212_);
            crate::leanh::lean_closure_set(v___f_1216_, 2, v_inst_1203_);
            crate::leanh::lean_closure_set(v___f_1216_, 3, v_inst_1204_);
            crate::leanh::lean_closure_set(v___f_1216_, 4, v_inst_1205_);
            crate::leanh::lean_closure_set(v___f_1216_, 5, v_inst_1206_);
            crate::leanh::lean_closure_set(v___f_1216_, 6, v_inst_1207_);
            crate::leanh::lean_closure_set(v___f_1216_, 7, v_k_1213_);
            crate::leanh::lean_closure_set(v___f_1216_, 8, v_toBind_1211_);
            v___x_1217_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
                v_inst_1205_,
                v_inst_1204_,
                v_inst_1203_,
                v_inst_1206_,
                v_inst_1207_,
            );
            v___x_1218_ = crate::leanh::lean_apply_4(
                v_toBind_1211_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1217_,
                v___f_1216_,
            );
            return v___x_1218_;
        } else {
            let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_toPure_1212_);
            crate::leanh::lean_dec(v_k_1213_);
            crate::leanh::lean_dec(v_toBind_1211_);
            crate::leanh::lean_dec_ref(v_inst_1207_);
            crate::leanh::lean_dec_ref(v_inst_1206_);
            crate::leanh::lean_dec(v_inst_1205_);
            crate::leanh::lean_dec_ref(v_inst_1204_);
            crate::leanh::lean_dec_ref(v_inst_1203_);
            v___x_1219_ =
                crate::leanh::lean_apply_2(v_toPure_1212_, crate::leanh::lean_box(0), v_acc_1209_);
            return v___x_1219_;
        }
    } else {
        let mut v_toBind_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1220_ = crate::leanh::lean_ctor_get(v_inst_1203_, 1);
        crate::leanh::lean_inc_n(v_toBind_1220_, 2);
        v_k_1221_ = crate::leanh::lean_ctor_get(v_p_1208_, 0);
        crate::leanh::lean_inc(v_k_1221_);
        v_v_1222_ = crate::leanh::lean_ctor_get(v_p_1208_, 1);
        crate::leanh::lean_inc(v_v_1222_);
        v_p_1223_ = crate::leanh::lean_ctor_get(v_p_1208_, 2);
        crate::leanh::lean_inc_ref(v_p_1223_);
        crate::leanh::lean_dec_ref_known(v_p_1208_, 3);
        crate::leanh::lean_inc_ref(v_inst_1207_);
        crate::leanh::lean_inc_ref(v_inst_1206_);
        crate::leanh::lean_inc(v_inst_1205_);
        crate::leanh::lean_inc_ref(v_inst_1204_);
        crate::leanh::lean_inc_ref(v_inst_1203_);
        v___f_1224_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__3 as *mut core::ffi::c_void, 11, 10);
        crate::leanh::lean_closure_set(v___f_1224_, 0, v_acc_1209_);
        crate::leanh::lean_closure_set(v___f_1224_, 1, v_inst_1203_);
        crate::leanh::lean_closure_set(v___f_1224_, 2, v_inst_1204_);
        crate::leanh::lean_closure_set(v___f_1224_, 3, v_inst_1205_);
        crate::leanh::lean_closure_set(v___f_1224_, 4, v_inst_1206_);
        crate::leanh::lean_closure_set(v___f_1224_, 5, v_inst_1207_);
        crate::leanh::lean_closure_set(v___f_1224_, 6, v_p_1223_);
        crate::leanh::lean_closure_set(v___f_1224_, 7, v_k_1221_);
        crate::leanh::lean_closure_set(v___f_1224_, 8, v_v_1222_);
        crate::leanh::lean_closure_set(v___f_1224_, 9, v_toBind_1220_);
        v___x_1225_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
            v_inst_1205_,
            v_inst_1204_,
            v_inst_1203_,
            v_inst_1206_,
            v_inst_1207_,
        );
        v___x_1226_ = crate::leanh::lean_apply_4(
            v_toBind_1220_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1225_,
            v___f_1224_,
        );
        return v___x_1226_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg___lam__2(
    mut v_____do__lift_1227_: *mut crate::leanh::LeanObject,
    mut v_acc_1228_: *mut crate::leanh::LeanObject,
    mut v_inst_1229_: *mut crate::leanh::LeanObject,
    mut v_inst_1230_: *mut crate::leanh::LeanObject,
    mut v_inst_1231_: *mut crate::leanh::LeanObject,
    mut v_inst_1232_: *mut crate::leanh::LeanObject,
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_p_1234_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = l_Lean_mkAppB(v_____do__lift_1227_, v_acc_1228_, v_____do__lift_1235_);
    v___x_1237_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_p_1234_, v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go(
    mut v_M_1238_: *mut crate::leanh::LeanObject,
    mut v_inst_1239_: *mut crate::leanh::LeanObject,
    mut v_inst_1240_: *mut crate::leanh::LeanObject,
    mut v_inst_1241_: *mut crate::leanh::LeanObject,
    mut v_inst_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
    mut v_p_1244_: *mut crate::leanh::LeanObject,
    mut v_acc_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v_inst_1243_, v_p_1244_, v_acc_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___redArg___lam__0(
    mut v_inst_1247_: *mut crate::leanh::LeanObject,
    mut v_inst_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
    mut v_inst_1251_: *mut crate::leanh::LeanObject,
    mut v_p_1252_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___redArg(v_inst_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_p_1252_, v_____do__lift_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
    mut v_inst_1255_: *mut crate::leanh::LeanObject,
    mut v_inst_1256_: *mut crate::leanh::LeanObject,
    mut v_inst_1257_: *mut crate::leanh::LeanObject,
    mut v_inst_1258_: *mut crate::leanh::LeanObject,
    mut v_inst_1259_: *mut crate::leanh::LeanObject,
    mut v_p_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1260_) == 0 {
        let mut v_k_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1261_ = crate::leanh::lean_ctor_get(v_p_1260_, 0);
        crate::leanh::lean_inc(v_k_1261_);
        crate::leanh::lean_dec_ref_known(v_p_1260_, 1);
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
        let mut v_toBind_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1263_ = crate::leanh::lean_ctor_get(v_inst_1255_, 1);
        crate::leanh::lean_inc(v_toBind_1263_);
        v_k_1264_ = crate::leanh::lean_ctor_get(v_p_1260_, 0);
        crate::leanh::lean_inc(v_k_1264_);
        v_v_1265_ = crate::leanh::lean_ctor_get(v_p_1260_, 1);
        crate::leanh::lean_inc(v_v_1265_);
        v_p_1266_ = crate::leanh::lean_ctor_get(v_p_1260_, 2);
        crate::leanh::lean_inc_ref(v_p_1266_);
        crate::leanh::lean_dec_ref_known(v_p_1260_, 3);
        crate::leanh::lean_inc_ref(v_inst_1259_);
        crate::leanh::lean_inc_ref(v_inst_1258_);
        crate::leanh::lean_inc(v_inst_1257_);
        crate::leanh::lean_inc_ref(v_inst_1256_);
        crate::leanh::lean_inc_ref(v_inst_1255_);
        v___f_1267_ = crate::leanh::lean_alloc_closure(
            l_Lean_Grind_CommRing_Poly_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_1267_, 0, v_inst_1255_);
        crate::leanh::lean_closure_set(v___f_1267_, 1, v_inst_1256_);
        crate::leanh::lean_closure_set(v___f_1267_, 2, v_inst_1257_);
        crate::leanh::lean_closure_set(v___f_1267_, 3, v_inst_1258_);
        crate::leanh::lean_closure_set(v___f_1267_, 4, v_inst_1259_);
        crate::leanh::lean_closure_set(v___f_1267_, 5, v_p_1266_);
        v___x_1268_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___redArg(v_inst_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_k_1264_, v_v_1265_);
        v___x_1269_ = crate::leanh::lean_apply_4(
            v_toBind_1263_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1268_,
            v___f_1267_,
        );
        return v___x_1269_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr(
    mut v_M_1270_: *mut crate::leanh::LeanObject,
    mut v_inst_1271_: *mut crate::leanh::LeanObject,
    mut v_inst_1272_: *mut crate::leanh::LeanObject,
    mut v_inst_1273_: *mut crate::leanh::LeanObject,
    mut v_inst_1274_: *mut crate::leanh::LeanObject,
    mut v_inst_1275_: *mut crate::leanh::LeanObject,
    mut v_p_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_k_1278_: *mut crate::leanh::LeanObject,
    mut v_toPure_1279_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_mkNatLit(v_k_1278_);
    v___x_1282_ = l_Lean_Expr_app___override(v_____do__lift_1280_, v___x_1281_);
    v___x_1283_ =
        crate::leanh::lean_apply_2(v_toPure_1279_, crate::leanh::lean_box(0), v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1(
    mut v_k_1284_: *mut crate::leanh::LeanObject,
    mut v_toPure_1285_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = l_Lean_mkIntLit(v_k_1284_);
    v___x_1288_ = l_Lean_Expr_app___override(v_____do__lift_1286_, v___x_1287_);
    v___x_1289_ =
        crate::leanh::lean_apply_2(v_toPure_1285_, crate::leanh::lean_box(0), v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1___boxed(
    mut v_k_1290_: *mut crate::leanh::LeanObject,
    mut v_toPure_1291_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1(v_k_1290_, v_toPure_1291_, v_____do__lift_1292_);
    crate::leanh::lean_dec(v_k_1290_);
    return v_res_1293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__2(
    mut v_____do__lift_1294_: *mut crate::leanh::LeanObject,
    mut v_toPure_1295_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Expr_app___override(v_____do__lift_1294_, v_____do__lift_1296_);
    v___x_1298_ =
        crate::leanh::lean_apply_2(v_toPure_1295_, crate::leanh::lean_box(0), v___x_1297_);
    return v___x_1298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__13(
    mut v_k_1299_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1300_: *mut crate::leanh::LeanObject,
    mut v_toPure_1301_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1303_ = l_Lean_mkNatLit(v_k_1299_);
    v___x_1304_ = l_Lean_mkAppB(v_____do__lift_1300_, v_____do__lift_1302_, v___x_1303_);
    v___x_1305_ =
        crate::leanh::lean_apply_2(v_toPure_1301_, crate::leanh::lean_box(0), v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__4(
    mut v_____do__lift_1306_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1307_: *mut crate::leanh::LeanObject,
    mut v_toPure_1308_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Lean_mkAppB(
        v_____do__lift_1306_,
        v_____do__lift_1307_,
        v_____do__lift_1309_,
    );
    v___x_1311_ =
        crate::leanh::lean_apply_2(v_toPure_1308_, crate::leanh::lean_box(0), v___x_1310_);
    return v___x_1311_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__5(
    mut v_____do__lift_1312_: *mut crate::leanh::LeanObject,
    mut v_toPure_1313_: *mut crate::leanh::LeanObject,
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_inst_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_inst_1317_: *mut crate::leanh::LeanObject,
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
    mut v_getVar_1319_: *mut crate::leanh::LeanObject,
    mut v_b_1320_: *mut crate::leanh::LeanObject,
    mut v_toBind_1321_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1323_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__4 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1323_, 0, v_____do__lift_1312_);
    crate::leanh::lean_closure_set(v___f_1323_, 1, v_____do__lift_1322_);
    crate::leanh::lean_closure_set(v___f_1323_, 2, v_toPure_1313_);
    v___x_1324_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_getVar_1319_, v_b_1320_);
    v___x_1325_ = crate::leanh::lean_apply_4(
        v_toBind_1321_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1324_,
        v___f_1323_,
    );
    return v___x_1325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6(
    mut v_toPure_1326_: *mut crate::leanh::LeanObject,
    mut v_inst_1327_: *mut crate::leanh::LeanObject,
    mut v_inst_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
    mut v_inst_1331_: *mut crate::leanh::LeanObject,
    mut v_getVar_1332_: *mut crate::leanh::LeanObject,
    mut v_b_1333_: *mut crate::leanh::LeanObject,
    mut v_toBind_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1334_);
    crate::leanh::lean_inc_ref(v_getVar_1332_);
    crate::leanh::lean_inc_ref(v_inst_1331_);
    crate::leanh::lean_inc_ref(v_inst_1330_);
    crate::leanh::lean_inc(v_inst_1329_);
    crate::leanh::lean_inc_ref(v_inst_1328_);
    crate::leanh::lean_inc_ref(v_inst_1327_);
    v___f_1337_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__5 as *mut core::ffi::c_void, 11, 10);
    crate::leanh::lean_closure_set(v___f_1337_, 0, v_____do__lift_1336_);
    crate::leanh::lean_closure_set(v___f_1337_, 1, v_toPure_1326_);
    crate::leanh::lean_closure_set(v___f_1337_, 2, v_inst_1327_);
    crate::leanh::lean_closure_set(v___f_1337_, 3, v_inst_1328_);
    crate::leanh::lean_closure_set(v___f_1337_, 4, v_inst_1329_);
    crate::leanh::lean_closure_set(v___f_1337_, 5, v_inst_1330_);
    crate::leanh::lean_closure_set(v___f_1337_, 6, v_inst_1331_);
    crate::leanh::lean_closure_set(v___f_1337_, 7, v_getVar_1332_);
    crate::leanh::lean_closure_set(v___f_1337_, 8, v_b_1333_);
    crate::leanh::lean_closure_set(v___f_1337_, 9, v_toBind_1334_);
    v___x_1338_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_getVar_1332_, v_a_1335_);
    v___x_1339_ = crate::leanh::lean_apply_4(
        v_toBind_1334_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1338_,
        v___f_1337_,
    );
    return v___x_1339_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__7(
    mut v_k_1340_: *mut crate::leanh::LeanObject,
    mut v_toPure_1341_: *mut crate::leanh::LeanObject,
    mut v_inst_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_inst_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_getVar_1347_: *mut crate::leanh::LeanObject,
    mut v_a_1348_: *mut crate::leanh::LeanObject,
    mut v_toBind_1349_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1351_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__13 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1351_, 0, v_k_1340_);
    crate::leanh::lean_closure_set(v___f_1351_, 1, v_____do__lift_1350_);
    crate::leanh::lean_closure_set(v___f_1351_, 2, v_toPure_1341_);
    v___x_1352_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_getVar_1347_, v_a_1348_);
    v___x_1353_ = crate::leanh::lean_apply_4(
        v_toBind_1349_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1352_,
        v___f_1351_,
    );
    return v___x_1353_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_getVar_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_1360_) {
        0 => {
            let mut v_k_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_getVar_1359_);
            v_k_1361_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc(v_k_1361_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 1);
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
            let mut v_toApplicative_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1363_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            crate::leanh::lean_dec_ref(v_getVar_1359_);
            crate::leanh::lean_dec_ref(v_inst_1355_);
            v_toBind_1364_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc(v_toBind_1364_);
            v_toPure_1365_ = crate::leanh::lean_ctor_get(v_toApplicative_1363_, 1);
            v_k_1366_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc(v_k_1366_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 1);
            crate::leanh::lean_inc(v_toPure_1365_);
            v___f_1367_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
            crate::leanh::lean_closure_set(v___f_1367_, 0, v_k_1366_);
            crate::leanh::lean_closure_set(v___f_1367_, 1, v_toPure_1365_);
            v___x_1368_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
                v_inst_1356_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1369_ = crate::leanh::lean_apply_4(
                v_toBind_1364_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1368_,
                v___f_1367_,
            );
            return v___x_1369_;
        }
        2 => {
            let mut v_toApplicative_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1370_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            crate::leanh::lean_dec_ref(v_getVar_1359_);
            crate::leanh::lean_dec_ref(v_inst_1355_);
            v_toBind_1371_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc(v_toBind_1371_);
            v_toPure_1372_ = crate::leanh::lean_ctor_get(v_toApplicative_1370_, 1);
            v_k_1373_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc(v_k_1373_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 1);
            crate::leanh::lean_inc(v_toPure_1372_);
            v___f_1374_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
            crate::leanh::lean_closure_set(v___f_1374_, 0, v_k_1373_);
            crate::leanh::lean_closure_set(v___f_1374_, 1, v_toPure_1372_);
            v___x_1375_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
                v_inst_1356_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1376_ = crate::leanh::lean_apply_4(
                v_toBind_1371_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1375_,
                v___f_1374_,
            );
            return v___x_1376_;
        }
        3 => {
            let mut v_toApplicative_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1377_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1377_);
            crate::leanh::lean_dec_ref(v_inst_1358_);
            crate::leanh::lean_dec_ref(v_inst_1357_);
            crate::leanh::lean_dec(v_inst_1356_);
            crate::leanh::lean_dec_ref(v_inst_1355_);
            crate::leanh::lean_dec_ref(v_inst_1354_);
            v_toPure_1378_ = crate::leanh::lean_ctor_get(v_toApplicative_1377_, 1);
            crate::leanh::lean_inc(v_toPure_1378_);
            crate::leanh::lean_dec_ref(v_toApplicative_1377_);
            v_i_1379_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc(v_i_1379_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 1);
            v___x_1380_ = crate::leanh::lean_apply_1(v_getVar_1359_, v_i_1379_);
            v___x_1381_ =
                crate::leanh::lean_apply_2(v_toPure_1378_, crate::leanh::lean_box(0), v___x_1380_);
            return v___x_1381_;
        }
        4 => {
            let mut v_toApplicative_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1382_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1383_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc_n(v_toBind_1383_, 2);
            v_toPure_1384_ = crate::leanh::lean_ctor_get(v_toApplicative_1382_, 1);
            v_a_1385_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc_ref(v_a_1385_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 1);
            crate::leanh::lean_inc_ref(v_inst_1358_);
            crate::leanh::lean_inc_ref(v_inst_1357_);
            crate::leanh::lean_inc(v_inst_1356_);
            crate::leanh::lean_inc_ref(v_inst_1355_);
            crate::leanh::lean_inc_ref(v_inst_1354_);
            crate::leanh::lean_inc(v_toPure_1384_);
            v___f_1386_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__3 as *mut core::ffi::c_void, 10, 9);
            crate::leanh::lean_closure_set(v___f_1386_, 0, v_toPure_1384_);
            crate::leanh::lean_closure_set(v___f_1386_, 1, v_inst_1354_);
            crate::leanh::lean_closure_set(v___f_1386_, 2, v_inst_1355_);
            crate::leanh::lean_closure_set(v___f_1386_, 3, v_inst_1356_);
            crate::leanh::lean_closure_set(v___f_1386_, 4, v_inst_1357_);
            crate::leanh::lean_closure_set(v___f_1386_, 5, v_inst_1358_);
            crate::leanh::lean_closure_set(v___f_1386_, 6, v_getVar_1359_);
            crate::leanh::lean_closure_set(v___f_1386_, 7, v_a_1385_);
            crate::leanh::lean_closure_set(v___f_1386_, 8, v_toBind_1383_);
            v___x_1387_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1388_ = crate::leanh::lean_apply_4(
                v_toBind_1383_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1387_,
                v___f_1386_,
            );
            return v___x_1388_;
        }
        5 => {
            let mut v_toApplicative_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1389_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1390_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc_n(v_toBind_1390_, 2);
            v_toPure_1391_ = crate::leanh::lean_ctor_get(v_toApplicative_1389_, 1);
            v_a_1392_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc_ref(v_a_1392_);
            v_b_1393_ = crate::leanh::lean_ctor_get(v_a_1360_, 1);
            crate::leanh::lean_inc_ref(v_b_1393_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 2);
            crate::leanh::lean_inc_ref(v_inst_1358_);
            crate::leanh::lean_inc_ref(v_inst_1357_);
            crate::leanh::lean_inc(v_inst_1356_);
            crate::leanh::lean_inc_ref(v_inst_1355_);
            crate::leanh::lean_inc_ref(v_inst_1354_);
            crate::leanh::lean_inc(v_toPure_1391_);
            v___f_1394_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            crate::leanh::lean_closure_set(v___f_1394_, 0, v_toPure_1391_);
            crate::leanh::lean_closure_set(v___f_1394_, 1, v_inst_1354_);
            crate::leanh::lean_closure_set(v___f_1394_, 2, v_inst_1355_);
            crate::leanh::lean_closure_set(v___f_1394_, 3, v_inst_1356_);
            crate::leanh::lean_closure_set(v___f_1394_, 4, v_inst_1357_);
            crate::leanh::lean_closure_set(v___f_1394_, 5, v_inst_1358_);
            crate::leanh::lean_closure_set(v___f_1394_, 6, v_getVar_1359_);
            crate::leanh::lean_closure_set(v___f_1394_, 7, v_b_1393_);
            crate::leanh::lean_closure_set(v___f_1394_, 8, v_toBind_1390_);
            crate::leanh::lean_closure_set(v___f_1394_, 9, v_a_1392_);
            v___x_1395_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1396_ = crate::leanh::lean_apply_4(
                v_toBind_1390_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1395_,
                v___f_1394_,
            );
            return v___x_1396_;
        }
        6 => {
            let mut v_toApplicative_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1397_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1398_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc_n(v_toBind_1398_, 2);
            v_toPure_1399_ = crate::leanh::lean_ctor_get(v_toApplicative_1397_, 1);
            v_a_1400_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc_ref(v_a_1400_);
            v_b_1401_ = crate::leanh::lean_ctor_get(v_a_1360_, 1);
            crate::leanh::lean_inc_ref(v_b_1401_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 2);
            crate::leanh::lean_inc_ref(v_inst_1358_);
            crate::leanh::lean_inc_ref(v_inst_1357_);
            crate::leanh::lean_inc(v_inst_1356_);
            crate::leanh::lean_inc_ref(v_inst_1355_);
            crate::leanh::lean_inc_ref(v_inst_1354_);
            crate::leanh::lean_inc(v_toPure_1399_);
            v___f_1402_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            crate::leanh::lean_closure_set(v___f_1402_, 0, v_toPure_1399_);
            crate::leanh::lean_closure_set(v___f_1402_, 1, v_inst_1354_);
            crate::leanh::lean_closure_set(v___f_1402_, 2, v_inst_1355_);
            crate::leanh::lean_closure_set(v___f_1402_, 3, v_inst_1356_);
            crate::leanh::lean_closure_set(v___f_1402_, 4, v_inst_1357_);
            crate::leanh::lean_closure_set(v___f_1402_, 5, v_inst_1358_);
            crate::leanh::lean_closure_set(v___f_1402_, 6, v_getVar_1359_);
            crate::leanh::lean_closure_set(v___f_1402_, 7, v_b_1401_);
            crate::leanh::lean_closure_set(v___f_1402_, 8, v_toBind_1398_);
            crate::leanh::lean_closure_set(v___f_1402_, 9, v_a_1400_);
            v___x_1403_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1404_ = crate::leanh::lean_apply_4(
                v_toBind_1398_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1403_,
                v___f_1402_,
            );
            return v___x_1404_;
        }
        7 => {
            let mut v_toApplicative_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1405_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1406_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc_n(v_toBind_1406_, 2);
            v_toPure_1407_ = crate::leanh::lean_ctor_get(v_toApplicative_1405_, 1);
            v_a_1408_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc_ref(v_a_1408_);
            v_b_1409_ = crate::leanh::lean_ctor_get(v_a_1360_, 1);
            crate::leanh::lean_inc_ref(v_b_1409_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 2);
            crate::leanh::lean_inc_ref(v_inst_1358_);
            crate::leanh::lean_inc_ref(v_inst_1357_);
            crate::leanh::lean_inc(v_inst_1356_);
            crate::leanh::lean_inc_ref(v_inst_1355_);
            crate::leanh::lean_inc_ref(v_inst_1354_);
            crate::leanh::lean_inc(v_toPure_1407_);
            v___f_1410_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
            crate::leanh::lean_closure_set(v___f_1410_, 0, v_toPure_1407_);
            crate::leanh::lean_closure_set(v___f_1410_, 1, v_inst_1354_);
            crate::leanh::lean_closure_set(v___f_1410_, 2, v_inst_1355_);
            crate::leanh::lean_closure_set(v___f_1410_, 3, v_inst_1356_);
            crate::leanh::lean_closure_set(v___f_1410_, 4, v_inst_1357_);
            crate::leanh::lean_closure_set(v___f_1410_, 5, v_inst_1358_);
            crate::leanh::lean_closure_set(v___f_1410_, 6, v_getVar_1359_);
            crate::leanh::lean_closure_set(v___f_1410_, 7, v_b_1409_);
            crate::leanh::lean_closure_set(v___f_1410_, 8, v_toBind_1406_);
            crate::leanh::lean_closure_set(v___f_1410_, 9, v_a_1408_);
            v___x_1411_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1412_ = crate::leanh::lean_apply_4(
                v_toBind_1406_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1411_,
                v___f_1410_,
            );
            return v___x_1412_;
        }
        _ => {
            let mut v_toApplicative_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1413_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
            v_toBind_1414_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
            crate::leanh::lean_inc_n(v_toBind_1414_, 2);
            v_toPure_1415_ = crate::leanh::lean_ctor_get(v_toApplicative_1413_, 1);
            v_a_1416_ = crate::leanh::lean_ctor_get(v_a_1360_, 0);
            crate::leanh::lean_inc_ref(v_a_1416_);
            v_k_1417_ = crate::leanh::lean_ctor_get(v_a_1360_, 1);
            crate::leanh::lean_inc(v_k_1417_);
            crate::leanh::lean_dec_ref_known(v_a_1360_, 2);
            crate::leanh::lean_inc_ref(v_inst_1358_);
            crate::leanh::lean_inc_ref(v_inst_1357_);
            crate::leanh::lean_inc(v_inst_1356_);
            crate::leanh::lean_inc_ref(v_inst_1355_);
            crate::leanh::lean_inc_ref(v_inst_1354_);
            crate::leanh::lean_inc(v_toPure_1415_);
            v___f_1418_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__7 as *mut core::ffi::c_void, 11, 10);
            crate::leanh::lean_closure_set(v___f_1418_, 0, v_k_1417_);
            crate::leanh::lean_closure_set(v___f_1418_, 1, v_toPure_1415_);
            crate::leanh::lean_closure_set(v___f_1418_, 2, v_inst_1354_);
            crate::leanh::lean_closure_set(v___f_1418_, 3, v_inst_1355_);
            crate::leanh::lean_closure_set(v___f_1418_, 4, v_inst_1356_);
            crate::leanh::lean_closure_set(v___f_1418_, 5, v_inst_1357_);
            crate::leanh::lean_closure_set(v___f_1418_, 6, v_inst_1358_);
            crate::leanh::lean_closure_set(v___f_1418_, 7, v_getVar_1359_);
            crate::leanh::lean_closure_set(v___f_1418_, 8, v_a_1416_);
            crate::leanh::lean_closure_set(v___f_1418_, 9, v_toBind_1414_);
            v___x_1419_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
                v_inst_1356_,
                v_inst_1355_,
                v_inst_1354_,
                v_inst_1357_,
                v_inst_1358_,
            );
            v___x_1420_ = crate::leanh::lean_apply_4(
                v_toBind_1414_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1419_,
                v___f_1418_,
            );
            return v___x_1420_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__3(
    mut v_toPure_1421_: *mut crate::leanh::LeanObject,
    mut v_inst_1422_: *mut crate::leanh::LeanObject,
    mut v_inst_1423_: *mut crate::leanh::LeanObject,
    mut v_inst_1424_: *mut crate::leanh::LeanObject,
    mut v_inst_1425_: *mut crate::leanh::LeanObject,
    mut v_inst_1426_: *mut crate::leanh::LeanObject,
    mut v_getVar_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_toBind_1429_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1431_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1431_, 0, v_____do__lift_1430_);
    crate::leanh::lean_closure_set(v___f_1431_, 1, v_toPure_1421_);
    v___x_1432_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1422_, v_inst_1423_, v_inst_1424_, v_inst_1425_, v_inst_1426_, v_getVar_1427_, v_a_1428_);
    v___x_1433_ = crate::leanh::lean_apply_4(
        v_toBind_1429_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1432_,
        v___f_1431_,
    );
    return v___x_1433_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go(
    mut v_M_1434_: *mut crate::leanh::LeanObject,
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_inst_1436_: *mut crate::leanh::LeanObject,
    mut v_inst_1437_: *mut crate::leanh::LeanObject,
    mut v_inst_1438_: *mut crate::leanh::LeanObject,
    mut v_inst_1439_: *mut crate::leanh::LeanObject,
    mut v_getVar_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1435_, v_inst_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_getVar_1440_, v_a_1441_);
    return v___x_1442_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore___redArg(
    mut v_inst_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
    mut v_inst_1447_: *mut crate::leanh::LeanObject,
    mut v_getVar_1448_: *mut crate::leanh::LeanObject,
    mut v_e_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_getVar_1448_, v_e_1449_);
    return v___x_1450_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore(
    mut v_M_1451_: *mut crate::leanh::LeanObject,
    mut v_inst_1452_: *mut crate::leanh::LeanObject,
    mut v_inst_1453_: *mut crate::leanh::LeanObject,
    mut v_inst_1454_: *mut crate::leanh::LeanObject,
    mut v_inst_1455_: *mut crate::leanh::LeanObject,
    mut v_inst_1456_: *mut crate::leanh::LeanObject,
    mut v_getVar_1457_: *mut crate::leanh::LeanObject,
    mut v_e_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_inst_1456_, v_getVar_1457_, v_e_1458_);
    return v___x_1459_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0(
    mut v_ring_1460_: *mut crate::leanh::LeanObject,
    mut v___x_1461_: *mut crate::leanh::LeanObject,
    mut v_x_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    v_vars_1463_ = crate::leanh::lean_ctor_get(v_ring_1460_, 14);
    v_size_1464_ = crate::leanh::lean_ctor_get(v_vars_1463_, 2);
    v___x_1465_ = lean_nat_dec_lt(v_x_1462_, v_size_1464_);
    if v___x_1465_ == 0 {
        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1466_ = l_outOfBounds___redArg(v___x_1461_);
        return v___x_1466_;
    } else {
        let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1467_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1461_, v_vars_1463_, v_x_1462_);
        return v___x_1467_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0___boxed(
    mut v_ring_1468_: *mut crate::leanh::LeanObject,
    mut v___x_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0(
        v_ring_1468_,
        v___x_1469_,
        v_x_1470_,
    );
    crate::leanh::lean_dec(v_x_1470_);
    crate::leanh::lean_dec_ref(v___x_1469_);
    crate::leanh::lean_dec_ref(v_ring_1468_);
    return v_res_1471_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__1(
    mut v___x_1472_: *mut crate::leanh::LeanObject,
    mut v_inst_1473_: *mut crate::leanh::LeanObject,
    mut v_inst_1474_: *mut crate::leanh::LeanObject,
    mut v_inst_1475_: *mut crate::leanh::LeanObject,
    mut v_inst_1476_: *mut crate::leanh::LeanObject,
    mut v_inst_1477_: *mut crate::leanh::LeanObject,
    mut v_e_1478_: *mut crate::leanh::LeanObject,
    mut v_ring_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1480_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1480_, 0, v_ring_1479_);
    crate::leanh::lean_closure_set(v___f_1480_, 1, v___x_1472_);
    v___x_1481_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1473_, v_inst_1474_, v_inst_1475_, v_inst_1476_, v_inst_1477_, v___f_1480_, v_e_1478_);
    return v___x_1481_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr___redArg(
    mut v_inst_1482_: *mut crate::leanh::LeanObject,
    mut v_inst_1483_: *mut crate::leanh::LeanObject,
    mut v_inst_1484_: *mut crate::leanh::LeanObject,
    mut v_inst_1485_: *mut crate::leanh::LeanObject,
    mut v_inst_1486_: *mut crate::leanh::LeanObject,
    mut v_e_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1488_ = crate::leanh::lean_ctor_get(v_inst_1482_, 1);
    crate::leanh::lean_inc(v_toBind_1488_);
    v_getRing_1489_ = crate::leanh::lean_ctor_get(v_inst_1486_, 0);
    crate::leanh::lean_inc(v_getRing_1489_);
    v___x_1490_ = l_Lean_instInhabitedExpr;
    v___f_1491_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1491_, 0, v___x_1490_);
    crate::leanh::lean_closure_set(v___f_1491_, 1, v_inst_1482_);
    crate::leanh::lean_closure_set(v___f_1491_, 2, v_inst_1483_);
    crate::leanh::lean_closure_set(v___f_1491_, 3, v_inst_1484_);
    crate::leanh::lean_closure_set(v___f_1491_, 4, v_inst_1485_);
    crate::leanh::lean_closure_set(v___f_1491_, 5, v_inst_1486_);
    crate::leanh::lean_closure_set(v___f_1491_, 6, v_e_1487_);
    v___x_1492_ = crate::leanh::lean_apply_4(
        v_toBind_1488_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1489_,
        v___f_1491_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr(
    mut v_M_1493_: *mut crate::leanh::LeanObject,
    mut v_inst_1494_: *mut crate::leanh::LeanObject,
    mut v_inst_1495_: *mut crate::leanh::LeanObject,
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_inst_1497_: *mut crate::leanh::LeanObject,
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_e_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_1501_: *mut crate::leanh::LeanObject,
    mut v_vars_1502_: *mut crate::leanh::LeanObject,
    mut v_x_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = lean_array_get_borrowed(v___x_1501_, v_vars_1502_, v_x_1503_);
    crate::leanh::lean_inc(v___x_1504_);
    return v___x_1504_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0___boxed(
    mut v___x_1505_: *mut crate::leanh::LeanObject,
    mut v_vars_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0(
        v___x_1505_,
        v_vars_1506_,
        v_x_1507_,
    );
    crate::leanh::lean_dec(v_x_1507_);
    crate::leanh::lean_dec_ref(v_vars_1506_);
    crate::leanh::lean_dec_ref(v___x_1505_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg(
    mut v_inst_1509_: *mut crate::leanh::LeanObject,
    mut v_inst_1510_: *mut crate::leanh::LeanObject,
    mut v_inst_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_inst_1513_: *mut crate::leanh::LeanObject,
    mut v_vars_1514_: *mut crate::leanh::LeanObject,
    mut v_e_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_instInhabitedExpr;
    v___f_1517_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_CommRing_Expr_denoteExpr_x27___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1517_, 0, v___x_1516_);
    crate::leanh::lean_closure_set(v___f_1517_, 1, v_vars_1514_);
    v___x_1518_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___redArg(v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_inst_1513_, v___f_1517_, v_e_1515_);
    return v___x_1518_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteExpr_x27(
    mut v_M_1519_: *mut crate::leanh::LeanObject,
    mut v_inst_1520_: *mut crate::leanh::LeanObject,
    mut v_inst_1521_: *mut crate::leanh::LeanObject,
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
    mut v_inst_1524_: *mut crate::leanh::LeanObject,
    mut v_vars_1525_: *mut crate::leanh::LeanObject,
    mut v_e_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_b_1532_: *mut crate::leanh::LeanObject,
    mut v_toPure_1533_: *mut crate::leanh::LeanObject,
    mut v_r_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_1535_ = crate::leanh::lean_ctor_get(v_r_1534_, 1);
    crate::leanh::lean_inc_ref(v_type_1535_);
    v_u_1536_ = crate::leanh::lean_ctor_get(v_r_1534_, 2);
    crate::leanh::lean_inc(v_u_1536_);
    crate::leanh::lean_dec_ref(v_r_1534_);
    v___x_1537_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0___closed__1;
    v___x_1538_ = l_Lean_Level_succ___override(v_u_1536_);
    v___x_1539_ = crate::leanh::lean_box(0);
    v___x_1540_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1538_);
    crate::leanh::lean_ctor_set(v___x_1540_, 1, v___x_1539_);
    v___x_1541_ = l_Lean_mkConst(v___x_1537_, v___x_1540_);
    v___x_1542_ = l_Lean_mkApp3(v___x_1541_, v_type_1535_, v_a_1531_, v_b_1532_);
    v___x_1543_ =
        crate::leanh::lean_apply_2(v_toPure_1533_, crate::leanh::lean_box(0), v___x_1542_);
    return v___x_1543_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_inst_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_b_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1548_ = crate::leanh::lean_ctor_get(v_inst_1544_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1548_);
    v_toBind_1549_ = crate::leanh::lean_ctor_get(v_inst_1544_, 1);
    crate::leanh::lean_inc(v_toBind_1549_);
    crate::leanh::lean_dec_ref(v_inst_1544_);
    v_getRing_1550_ = crate::leanh::lean_ctor_get(v_inst_1545_, 0);
    crate::leanh::lean_inc(v_getRing_1550_);
    crate::leanh::lean_dec_ref(v_inst_1545_);
    v_toPure_1551_ = crate::leanh::lean_ctor_get(v_toApplicative_1548_, 1);
    crate::leanh::lean_inc(v_toPure_1551_);
    crate::leanh::lean_dec_ref(v_toApplicative_1548_);
    v___f_1552_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1552_, 0, v_a_1546_);
    crate::leanh::lean_closure_set(v___f_1552_, 1, v_b_1547_);
    crate::leanh::lean_closure_set(v___f_1552_, 2, v_toPure_1551_);
    v___x_1553_ = crate::leanh::lean_apply_4(
        v_toBind_1549_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1550_,
        v___f_1552_,
    );
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq(
    mut v_M_1554_: *mut crate::leanh::LeanObject,
    mut v_inst_1555_: *mut crate::leanh::LeanObject,
    mut v_inst_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_b_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1555_, v_inst_1556_, v_a_1557_, v_b_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__0(
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
    mut v_inst_1561_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1562_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1560_, v_inst_1561_, v_____do__lift_1562_, v_____do__lift_1563_);
    return v___x_1564_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_1565_: *mut crate::leanh::LeanObject,
    mut v_inst_1566_: *mut crate::leanh::LeanObject,
    mut v_inst_1567_: *mut crate::leanh::LeanObject,
    mut v_inst_1568_: *mut crate::leanh::LeanObject,
    mut v_inst_1569_: *mut crate::leanh::LeanObject,
    mut v_toBind_1570_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1566_);
    crate::leanh::lean_inc_ref(v_inst_1565_);
    v___f_1572_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1572_, 0, v_inst_1565_);
    crate::leanh::lean_closure_set(v___f_1572_, 1, v_inst_1566_);
    crate::leanh::lean_closure_set(v___f_1572_, 2, v_____do__lift_1571_);
    v___x_1573_ = crate::leanh::lean_obj_once(
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
    v___x_1575_ = crate::leanh::lean_apply_4(
        v_toBind_1570_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1574_,
        v___f_1572_,
    );
    return v___x_1575_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg(
    mut v_inst_1576_: *mut crate::leanh::LeanObject,
    mut v_inst_1577_: *mut crate::leanh::LeanObject,
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_inst_1579_: *mut crate::leanh::LeanObject,
    mut v_inst_1580_: *mut crate::leanh::LeanObject,
    mut v_c_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1582_ = crate::leanh::lean_ctor_get(v_inst_1576_, 1);
    crate::leanh::lean_inc_n(v_toBind_1582_, 2);
    v_p_1583_ = crate::leanh::lean_ctor_get(v_c_1581_, 0);
    crate::leanh::lean_inc_ref(v_p_1583_);
    crate::leanh::lean_dec_ref(v_c_1581_);
    crate::leanh::lean_inc_ref(v_inst_1579_);
    crate::leanh::lean_inc(v_inst_1578_);
    crate::leanh::lean_inc_ref(v_inst_1577_);
    crate::leanh::lean_inc_ref(v_inst_1580_);
    crate::leanh::lean_inc_ref(v_inst_1576_);
    v___f_1584_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1584_, 0, v_inst_1576_);
    crate::leanh::lean_closure_set(v___f_1584_, 1, v_inst_1580_);
    crate::leanh::lean_closure_set(v___f_1584_, 2, v_inst_1577_);
    crate::leanh::lean_closure_set(v___f_1584_, 3, v_inst_1578_);
    crate::leanh::lean_closure_set(v___f_1584_, 4, v_inst_1579_);
    crate::leanh::lean_closure_set(v___f_1584_, 5, v_toBind_1582_);
    v___x_1585_ = l_Lean_Grind_CommRing_Poly_denoteExpr___redArg(
        v_inst_1576_,
        v_inst_1577_,
        v_inst_1578_,
        v_inst_1579_,
        v_inst_1580_,
        v_p_1583_,
    );
    v___x_1586_ = crate::leanh::lean_apply_4(
        v_toBind_1582_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1585_,
        v___f_1584_,
    );
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr(
    mut v_M_1587_: *mut crate::leanh::LeanObject,
    mut v_inst_1588_: *mut crate::leanh::LeanObject,
    mut v_inst_1589_: *mut crate::leanh::LeanObject,
    mut v_inst_1590_: *mut crate::leanh::LeanObject,
    mut v_inst_1591_: *mut crate::leanh::LeanObject,
    mut v_inst_1592_: *mut crate::leanh::LeanObject,
    mut v_c_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1595_: *mut crate::leanh::LeanObject,
    mut v_inst_1596_: *mut crate::leanh::LeanObject,
    mut v_inst_1597_: *mut crate::leanh::LeanObject,
    mut v_inst_1598_: *mut crate::leanh::LeanObject,
    mut v_inst_1599_: *mut crate::leanh::LeanObject,
    mut v_d_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
    mut v_inst_1604_: *mut crate::leanh::LeanObject,
    mut v_inst_1605_: *mut crate::leanh::LeanObject,
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
    mut v_d_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
        v_inst_1603_,
        v_inst_1604_,
        v_inst_1605_,
        v_inst_1606_,
        v_inst_1607_,
        v_d_1608_,
    );
    crate::leanh::lean_dec_ref(v_d_1608_);
    return v_res_1609_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr(
    mut v_M_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
    mut v_inst_1612_: *mut crate::leanh::LeanObject,
    mut v_inst_1613_: *mut crate::leanh::LeanObject,
    mut v_inst_1614_: *mut crate::leanh::LeanObject,
    mut v_inst_1615_: *mut crate::leanh::LeanObject,
    mut v_d_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1618_: *mut crate::leanh::LeanObject,
    mut v_inst_1619_: *mut crate::leanh::LeanObject,
    mut v_inst_1620_: *mut crate::leanh::LeanObject,
    mut v_inst_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v_inst_1623_: *mut crate::leanh::LeanObject,
    mut v_d_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr(
        v_M_1618_,
        v_inst_1619_,
        v_inst_1620_,
        v_inst_1621_,
        v_inst_1622_,
        v_inst_1623_,
        v_d_1624_,
    );
    crate::leanh::lean_dec_ref(v_d_1624_);
    return v_res_1625_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__0(
    mut v_toPure_1626_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = l_Lean_mkNot(v_____do__lift_1627_);
    v___x_1629_ =
        crate::leanh::lean_apply_2(v_toPure_1626_, crate::leanh::lean_box(0), v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_inst_1631_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1632_: *mut crate::leanh::LeanObject,
    mut v_toBind_1633_: *mut crate::leanh::LeanObject,
    mut v___f_1634_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1636_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___redArg(v_inst_1630_, v_inst_1631_, v_____do__lift_1632_, v_____do__lift_1635_);
    v___x_1637_ = crate::leanh::lean_apply_4(
        v_toBind_1633_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1636_,
        v___f_1634_,
    );
    return v___x_1637_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__2(
    mut v_inst_1638_: *mut crate::leanh::LeanObject,
    mut v_inst_1639_: *mut crate::leanh::LeanObject,
    mut v_toBind_1640_: *mut crate::leanh::LeanObject,
    mut v___f_1641_: *mut crate::leanh::LeanObject,
    mut v_inst_1642_: *mut crate::leanh::LeanObject,
    mut v_inst_1643_: *mut crate::leanh::LeanObject,
    mut v_inst_1644_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1640_);
    crate::leanh::lean_inc_ref(v_inst_1639_);
    crate::leanh::lean_inc_ref(v_inst_1638_);
    v___f_1646_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1646_, 0, v_inst_1638_);
    crate::leanh::lean_closure_set(v___f_1646_, 1, v_inst_1639_);
    crate::leanh::lean_closure_set(v___f_1646_, 2, v_____do__lift_1645_);
    crate::leanh::lean_closure_set(v___f_1646_, 3, v_toBind_1640_);
    crate::leanh::lean_closure_set(v___f_1646_, 4, v___f_1641_);
    v___x_1647_ = crate::leanh::lean_obj_once(
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
    v___x_1649_ = crate::leanh::lean_apply_4(
        v_toBind_1640_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1648_,
        v___f_1646_,
    );
    return v___x_1649_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg(
    mut v_inst_1650_: *mut crate::leanh::LeanObject,
    mut v_inst_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_inst_1653_: *mut crate::leanh::LeanObject,
    mut v_inst_1654_: *mut crate::leanh::LeanObject,
    mut v_c_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1656_ = crate::leanh::lean_ctor_get(v_inst_1650_, 0);
    v_toBind_1657_ = crate::leanh::lean_ctor_get(v_inst_1650_, 1);
    crate::leanh::lean_inc_n(v_toBind_1657_, 2);
    v_d_1658_ = crate::leanh::lean_ctor_get(v_c_1655_, 4);
    v_toPure_1659_ = crate::leanh::lean_ctor_get(v_toApplicative_1656_, 1);
    crate::leanh::lean_inc_ref(v_inst_1654_);
    crate::leanh::lean_inc_ref(v_inst_1653_);
    crate::leanh::lean_inc(v_inst_1652_);
    crate::leanh::lean_inc_ref(v_inst_1651_);
    crate::leanh::lean_inc_ref(v_inst_1650_);
    v___x_1660_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___redArg(
        v_inst_1650_,
        v_inst_1651_,
        v_inst_1652_,
        v_inst_1653_,
        v_inst_1654_,
        v_d_1658_,
    );
    crate::leanh::lean_inc(v_toPure_1659_);
    v___f_1661_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1661_, 0, v_toPure_1659_);
    v___f_1662_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1662_, 0, v_inst_1650_);
    crate::leanh::lean_closure_set(v___f_1662_, 1, v_inst_1654_);
    crate::leanh::lean_closure_set(v___f_1662_, 2, v_toBind_1657_);
    crate::leanh::lean_closure_set(v___f_1662_, 3, v___f_1661_);
    crate::leanh::lean_closure_set(v___f_1662_, 4, v_inst_1651_);
    crate::leanh::lean_closure_set(v___f_1662_, 5, v_inst_1652_);
    crate::leanh::lean_closure_set(v___f_1662_, 6, v_inst_1653_);
    v___x_1663_ = crate::leanh::lean_apply_4(
        v_toBind_1657_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1660_,
        v___f_1662_,
    );
    return v___x_1663_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg___boxed(
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
    mut v_inst_1666_: *mut crate::leanh::LeanObject,
    mut v_inst_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_c_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___redArg(
        v_inst_1664_,
        v_inst_1665_,
        v_inst_1666_,
        v_inst_1667_,
        v_inst_1668_,
        v_c_1669_,
    );
    crate::leanh::lean_dec_ref(v_c_1669_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr(
    mut v_M_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_inst_1674_: *mut crate::leanh::LeanObject,
    mut v_inst_1675_: *mut crate::leanh::LeanObject,
    mut v_inst_1676_: *mut crate::leanh::LeanObject,
    mut v_c_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1679_: *mut crate::leanh::LeanObject,
    mut v_inst_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_inst_1682_: *mut crate::leanh::LeanObject,
    mut v_inst_1683_: *mut crate::leanh::LeanObject,
    mut v_inst_1684_: *mut crate::leanh::LeanObject,
    mut v_c_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr(
        v_M_1679_,
        v_inst_1680_,
        v_inst_1681_,
        v_inst_1682_,
        v_inst_1683_,
        v_inst_1684_,
        v_c_1685_,
    );
    crate::leanh::lean_dec_ref(v_c_1685_);
    return v_res_1686_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
}
