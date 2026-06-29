// Lean compiler output
// Module: Std.Data.Internal.List.Associative
// Imports: Init.Data.Option.Attach Init.Data.List.Perm Std.Data.Internal.List.Defs Std.Data.Internal.List.Defs Init.Data.Order.LemmasExtra Init.Data.Bool Init.ByCases Init.Data.List.Count Init.Data.List.Erase Init.Data.List.Find Init.Data.List.MinMax Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.Prod Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_all___redArg, l_List_mapTR_loop___redArg, l_List_min_x3f___redArg,
};
use crate::r#gen::Init::Data::List::Count::{
    initialize_Init_Data_List_Count, runtime_initialize_Init_Data_List_Count,
};
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Perm::{
    initialize_Init_Data_List_Perm, runtime_initialize_Init_Data_List_Perm,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Option::Attach::{
    initialize_Init_Data_Option_Attach, runtime_initialize_Init_Data_Option_Attach,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Ord::Basic::l_Ord_opposite___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Order::LemmasExtra::{
    initialize_Init_Data_Order_LemmasExtra, runtime_initialize_Init_Data_Order_LemmasExtra,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_List_foldl___redArg, l_List_lengthTR___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::Internal::List::Defs::{
    initialize_Std_Data_Internal_List_Defs, runtime_initialize_Std_Data_Internal_List_Defs,
};
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le};
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 68, 97, 116, 97, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 76, 105,
        115, 116, 46, 65, 115, 115, 111, 99, 105, 97, 116, 105, 118, 101, 0,
    ],
};
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        83, 116, 100, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 76, 105, 115, 116, 46, 103,
        101, 116, 69, 110, 116, 114, 121, 33, 0,
    ],
};
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32,
        105, 110, 32, 97, 115, 115, 111, 99, 105, 97, 116, 105, 118, 101, 32, 108, 105, 115, 116,
        0,
    ],
};
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_List_insertListConst___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_List_Prod_toSigma as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_List_insertListConst___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_insertListConst___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Internal_List_getEntry_x3f___redArg(
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_x_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1348_) == 0 {
                    crate::leanh::lean_dec(v_a_1347_);
                    crate::leanh::lean_dec_ref(v_inst_1346_);
                    v___x_1349_ = crate::leanh::lean_box(0);
                    return v___x_1349_;
                } else {
                    v_head_1350_ = crate::leanh::lean_ctor_get(v_x_1348_, 0);
                    crate::leanh::lean_inc(v_head_1350_);
                    v_tail_1351_ = crate::leanh::lean_ctor_get(v_x_1348_, 1);
                    crate::leanh::lean_inc(v_tail_1351_);
                    crate::leanh::lean_dec_ref_known(v_x_1348_, 2);
                    v_fst_1352_ = crate::leanh::lean_ctor_get(v_head_1350_, 0);
                    crate::leanh::lean_inc_ref(v_inst_1346_);
                    crate::leanh::lean_inc(v_a_1347_);
                    crate::leanh::lean_inc(v_fst_1352_);
                    v___x_1353_ = crate::leanh::lean_apply_2(v_inst_1346_, v_fst_1352_, v_a_1347_);
                    v___x_1354_ = (crate::leanh::lean_unbox(v___x_1353_) as u8);
                    if v___x_1354_ == 0 {
                        crate::leanh::lean_dec(v_head_1350_);
                        v_x_1348_ = v_tail_1351_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1351_);
                        crate::leanh::lean_dec(v_a_1347_);
                        crate::leanh::lean_dec_ref(v_inst_1346_);
                        v___x_1356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1356_, 0, v_head_1350_);
                        return v___x_1356_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntry_x3f(
    mut v_00_u03b1_1357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1359_, v_a_1360_, v_x_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Std_Internal_List_getEntryD___redArg(
    mut v_inst_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_fallback_1365_: *mut crate::leanh::LeanObject,
    mut v_x_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1366_) == 0 {
                    crate::leanh::lean_dec(v_a_1364_);
                    crate::leanh::lean_dec_ref(v_inst_1363_);
                    crate::leanh::lean_inc_ref(v_fallback_1365_);
                    return v_fallback_1365_;
                } else {
                    v_head_1367_ = crate::leanh::lean_ctor_get(v_x_1366_, 0);
                    crate::leanh::lean_inc(v_head_1367_);
                    v_tail_1368_ = crate::leanh::lean_ctor_get(v_x_1366_, 1);
                    crate::leanh::lean_inc(v_tail_1368_);
                    crate::leanh::lean_dec_ref_known(v_x_1366_, 2);
                    v_fst_1369_ = crate::leanh::lean_ctor_get(v_head_1367_, 0);
                    crate::leanh::lean_inc_ref(v_inst_1363_);
                    crate::leanh::lean_inc(v_a_1364_);
                    crate::leanh::lean_inc(v_fst_1369_);
                    v___x_1370_ = crate::leanh::lean_apply_2(v_inst_1363_, v_fst_1369_, v_a_1364_);
                    v___x_1371_ = (crate::leanh::lean_unbox(v___x_1370_) as u8);
                    if v___x_1371_ == 0 {
                        crate::leanh::lean_dec(v_head_1367_);
                        v_x_1366_ = v_tail_1368_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1368_);
                        crate::leanh::lean_dec(v_a_1364_);
                        crate::leanh::lean_dec_ref(v_inst_1363_);
                        return v_head_1367_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntryD___redArg___boxed(
    mut v_inst_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_fallback_1375_: *mut crate::leanh::LeanObject,
    mut v_x_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1377_ = l_Std_Internal_List_getEntryD___redArg(
        v_inst_1373_,
        v_a_1374_,
        v_fallback_1375_,
        v_x_1376_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1375_);
    return v_res_1377_;
}
pub unsafe fn l_Std_Internal_List_getEntryD(
    mut v_00_u03b1_1378_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1379_: *mut crate::leanh::LeanObject,
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_fallback_1382_: *mut crate::leanh::LeanObject,
    mut v_x_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Std_Internal_List_getEntryD___redArg(
        v_inst_1380_,
        v_a_1381_,
        v_fallback_1382_,
        v_x_1383_,
    );
    return v___x_1384_;
}
pub unsafe fn l_Std_Internal_List_getEntryD___boxed(
    mut v_00_u03b1_1385_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_fallback_1389_: *mut crate::leanh::LeanObject,
    mut v_x_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Std_Internal_List_getEntryD(
        v_00_u03b1_1385_,
        v_00_u03b2_1386_,
        v_inst_1387_,
        v_a_1388_,
        v_fallback_1389_,
        v_x_1390_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1389_);
    return v_res_1391_;
}
pub unsafe fn _init_l_Std_Internal_List_getEntry_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Std_Internal_List_getEntry_x21___redArg___closed__2;
    v___x_1396_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1397_ = crate::leanh::lean_unsigned_to_nat(67);
    v___x_1398_ = l_Std_Internal_List_getEntry_x21___redArg___closed__1;
    v___x_1399_ = l_Std_Internal_List_getEntry_x21___redArg___closed__0;
    v___x_1400_ = l_mkPanicMessageWithDecl(
        v___x_1399_,
        v___x_1398_,
        v___x_1397_,
        v___x_1396_,
        v___x_1395_,
    );
    return v___x_1400_;
}
pub unsafe fn l_Std_Internal_List_getEntry_x21___redArg(
    mut v_inst_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1404_) == 0 {
                    crate::leanh::lean_dec(v_a_1402_);
                    crate::leanh::lean_dec_ref(v_inst_1401_);
                    v___x_1405_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_List_getEntry_x21___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_List_getEntry_x21___redArg___closed__3_once
                        ),
                        _init_l_Std_Internal_List_getEntry_x21___redArg___closed__3,
                    );
                    v___x_1406_ = l_panic___redArg(v_inst_1403_, v___x_1405_);
                    return v___x_1406_;
                } else {
                    v_head_1407_ = crate::leanh::lean_ctor_get(v_x_1404_, 0);
                    crate::leanh::lean_inc(v_head_1407_);
                    v_tail_1408_ = crate::leanh::lean_ctor_get(v_x_1404_, 1);
                    crate::leanh::lean_inc(v_tail_1408_);
                    crate::leanh::lean_dec_ref_known(v_x_1404_, 2);
                    v_fst_1409_ = crate::leanh::lean_ctor_get(v_head_1407_, 0);
                    crate::leanh::lean_inc_ref(v_inst_1401_);
                    crate::leanh::lean_inc(v_a_1402_);
                    crate::leanh::lean_inc(v_fst_1409_);
                    v___x_1410_ = crate::leanh::lean_apply_2(v_inst_1401_, v_fst_1409_, v_a_1402_);
                    v___x_1411_ = (crate::leanh::lean_unbox(v___x_1410_) as u8);
                    if v___x_1411_ == 0 {
                        crate::leanh::lean_dec(v_head_1407_);
                        v_x_1404_ = v_tail_1408_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1408_);
                        crate::leanh::lean_dec(v_a_1402_);
                        crate::leanh::lean_dec_ref(v_inst_1401_);
                        return v_head_1407_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntry_x21___redArg___boxed(
    mut v_inst_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_inst_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ =
        l_Std_Internal_List_getEntry_x21___redArg(v_inst_1413_, v_a_1414_, v_inst_1415_, v_x_1416_);
    crate::leanh::lean_dec_ref(v_inst_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Std_Internal_List_getEntry_x21(
    mut v_00_u03b1_1418_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1419_: *mut crate::leanh::LeanObject,
    mut v_inst_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_inst_1422_: *mut crate::leanh::LeanObject,
    mut v_x_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ =
        l_Std_Internal_List_getEntry_x21___redArg(v_inst_1420_, v_a_1421_, v_inst_1422_, v_x_1423_);
    return v___x_1424_;
}
pub unsafe fn l_Std_Internal_List_getEntry_x21___boxed(
    mut v_00_u03b1_1425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1426_: *mut crate::leanh::LeanObject,
    mut v_inst_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_inst_1429_: *mut crate::leanh::LeanObject,
    mut v_x_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Std_Internal_List_getEntry_x21(
        v_00_u03b1_1425_,
        v_00_u03b2_1426_,
        v_inst_1427_,
        v_a_1428_,
        v_inst_1429_,
        v_x_1430_,
    );
    crate::leanh::lean_dec_ref(v_inst_1429_);
    return v_res_1431_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1432_: *mut crate::leanh::LeanObject,
    mut v_h__1_1433_: *mut crate::leanh::LeanObject,
    mut v_h__2_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1432_) == 0 {
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1434_);
        v___x_1435_ = crate::leanh::lean_box(0);
        v___x_1436_ = crate::leanh::lean_apply_1(v_h__1_1433_, v___x_1435_);
        return v___x_1436_;
    } else {
        let mut v_head_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1433_);
        v_head_1437_ = crate::leanh::lean_ctor_get(v_x_1432_, 0);
        crate::leanh::lean_inc(v_head_1437_);
        v_tail_1438_ = crate::leanh::lean_ctor_get(v_x_1432_, 1);
        crate::leanh::lean_inc(v_tail_1438_);
        crate::leanh::lean_dec_ref_known(v_x_1432_, 2);
        v_fst_1439_ = crate::leanh::lean_ctor_get(v_head_1437_, 0);
        crate::leanh::lean_inc(v_fst_1439_);
        v_snd_1440_ = crate::leanh::lean_ctor_get(v_head_1437_, 1);
        crate::leanh::lean_inc(v_snd_1440_);
        crate::leanh::lean_dec(v_head_1437_);
        v___x_1441_ =
            crate::leanh::lean_apply_3(v_h__2_1434_, v_fst_1439_, v_snd_1440_, v_tail_1438_);
        return v___x_1441_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1442_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1443_: *mut crate::leanh::LeanObject,
    mut v_motive_1444_: *mut crate::leanh::LeanObject,
    mut v_x_1445_: *mut crate::leanh::LeanObject,
    mut v_h__1_1446_: *mut crate::leanh::LeanObject,
    mut v_h__2_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1445_) == 0 {
        let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1447_);
        v___x_1448_ = crate::leanh::lean_box(0);
        v___x_1449_ = crate::leanh::lean_apply_1(v_h__1_1446_, v___x_1448_);
        return v___x_1449_;
    } else {
        let mut v_head_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1446_);
        v_head_1450_ = crate::leanh::lean_ctor_get(v_x_1445_, 0);
        crate::leanh::lean_inc(v_head_1450_);
        v_tail_1451_ = crate::leanh::lean_ctor_get(v_x_1445_, 1);
        crate::leanh::lean_inc(v_tail_1451_);
        crate::leanh::lean_dec_ref_known(v_x_1445_, 2);
        v_fst_1452_ = crate::leanh::lean_ctor_get(v_head_1450_, 0);
        crate::leanh::lean_inc(v_fst_1452_);
        v_snd_1453_ = crate::leanh::lean_ctor_get(v_head_1450_, 1);
        crate::leanh::lean_inc(v_snd_1453_);
        crate::leanh::lean_dec(v_head_1450_);
        v___x_1454_ =
            crate::leanh::lean_apply_3(v_h__2_1447_, v_fst_1452_, v_snd_1453_, v_tail_1451_);
        return v___x_1454_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_h__1_1456_: *mut crate::leanh::LeanObject,
    mut v_h__2_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1455_) == 0 {
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1457_);
        v___x_1458_ = crate::leanh::lean_box(0);
        v___x_1459_ = crate::leanh::lean_apply_1(v_h__1_1456_, v___x_1458_);
        return v___x_1459_;
    } else {
        let mut v_head_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1456_);
        v_head_1460_ = crate::leanh::lean_ctor_get(v_x_1455_, 0);
        crate::leanh::lean_inc(v_head_1460_);
        v_tail_1461_ = crate::leanh::lean_ctor_get(v_x_1455_, 1);
        crate::leanh::lean_inc(v_tail_1461_);
        crate::leanh::lean_dec_ref_known(v_x_1455_, 2);
        v_fst_1462_ = crate::leanh::lean_ctor_get(v_head_1460_, 0);
        crate::leanh::lean_inc(v_fst_1462_);
        v_snd_1463_ = crate::leanh::lean_ctor_get(v_head_1460_, 1);
        crate::leanh::lean_inc(v_snd_1463_);
        crate::leanh::lean_dec(v_head_1460_);
        v___x_1464_ =
            crate::leanh::lean_apply_3(v_h__2_1457_, v_fst_1462_, v_snd_1463_, v_tail_1461_);
        return v___x_1464_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(
    mut v_00_u03b1_1465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1466_: *mut crate::leanh::LeanObject,
    mut v_motive_1467_: *mut crate::leanh::LeanObject,
    mut v_x_1468_: *mut crate::leanh::LeanObject,
    mut v_h__1_1469_: *mut crate::leanh::LeanObject,
    mut v_h__2_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1468_) == 0 {
        let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1470_);
        v___x_1471_ = crate::leanh::lean_box(0);
        v___x_1472_ = crate::leanh::lean_apply_1(v_h__1_1469_, v___x_1471_);
        return v___x_1472_;
    } else {
        let mut v_head_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1469_);
        v_head_1473_ = crate::leanh::lean_ctor_get(v_x_1468_, 0);
        crate::leanh::lean_inc(v_head_1473_);
        v_tail_1474_ = crate::leanh::lean_ctor_get(v_x_1468_, 1);
        crate::leanh::lean_inc(v_tail_1474_);
        crate::leanh::lean_dec_ref_known(v_x_1468_, 2);
        v_fst_1475_ = crate::leanh::lean_ctor_get(v_head_1473_, 0);
        crate::leanh::lean_inc(v_fst_1475_);
        v_snd_1476_ = crate::leanh::lean_ctor_get(v_head_1473_, 1);
        crate::leanh::lean_inc(v_snd_1476_);
        crate::leanh::lean_dec(v_head_1473_);
        v___x_1477_ =
            crate::leanh::lean_apply_3(v_h__2_1470_, v_fst_1475_, v_snd_1476_, v_tail_1474_);
        return v___x_1477_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(
    mut v_x_1478_: *mut crate::leanh::LeanObject,
    mut v_h__1_1479_: *mut crate::leanh::LeanObject,
    mut v_h__2_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1478_) == 0 {
        let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1480_);
        v___x_1481_ = crate::leanh::lean_box(0);
        v___x_1482_ = crate::leanh::lean_apply_1(v_h__1_1479_, v___x_1481_);
        return v___x_1482_;
    } else {
        let mut v_head_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1479_);
        v_head_1483_ = crate::leanh::lean_ctor_get(v_x_1478_, 0);
        crate::leanh::lean_inc(v_head_1483_);
        v_tail_1484_ = crate::leanh::lean_ctor_get(v_x_1478_, 1);
        crate::leanh::lean_inc(v_tail_1484_);
        crate::leanh::lean_dec_ref_known(v_x_1478_, 2);
        v_fst_1485_ = crate::leanh::lean_ctor_get(v_head_1483_, 0);
        crate::leanh::lean_inc(v_fst_1485_);
        v_snd_1486_ = crate::leanh::lean_ctor_get(v_head_1483_, 1);
        crate::leanh::lean_inc(v_snd_1486_);
        crate::leanh::lean_dec(v_head_1483_);
        v___x_1487_ =
            crate::leanh::lean_apply_3(v_h__2_1480_, v_fst_1485_, v_snd_1486_, v_tail_1484_);
        return v___x_1487_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(
    mut v_00_u03b1_1488_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1489_: *mut crate::leanh::LeanObject,
    mut v_motive_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
    mut v_h__1_1492_: *mut crate::leanh::LeanObject,
    mut v_h__2_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1491_) == 0 {
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1493_);
        v___x_1494_ = crate::leanh::lean_box(0);
        v___x_1495_ = crate::leanh::lean_apply_1(v_h__1_1492_, v___x_1494_);
        return v___x_1495_;
    } else {
        let mut v_head_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1492_);
        v_head_1496_ = crate::leanh::lean_ctor_get(v_x_1491_, 0);
        crate::leanh::lean_inc(v_head_1496_);
        v_tail_1497_ = crate::leanh::lean_ctor_get(v_x_1491_, 1);
        crate::leanh::lean_inc(v_tail_1497_);
        crate::leanh::lean_dec_ref_known(v_x_1491_, 2);
        v_fst_1498_ = crate::leanh::lean_ctor_get(v_head_1496_, 0);
        crate::leanh::lean_inc(v_fst_1498_);
        v_snd_1499_ = crate::leanh::lean_ctor_get(v_head_1496_, 1);
        crate::leanh::lean_inc(v_snd_1499_);
        crate::leanh::lean_dec(v_head_1496_);
        v___x_1500_ =
            crate::leanh::lean_apply_3(v_h__2_1493_, v_fst_1498_, v_snd_1499_, v_tail_1497_);
        return v___x_1500_;
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x3f___redArg(
    mut v_inst_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_x_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1503_) == 0 {
                    crate::leanh::lean_dec(v_a_1502_);
                    crate::leanh::lean_dec_ref(v_inst_1501_);
                    v___x_1504_ = crate::leanh::lean_box(0);
                    return v___x_1504_;
                } else {
                    v_head_1505_ = crate::leanh::lean_ctor_get(v_x_1503_, 0);
                    crate::leanh::lean_inc(v_head_1505_);
                    v_tail_1506_ = crate::leanh::lean_ctor_get(v_x_1503_, 1);
                    crate::leanh::lean_inc(v_tail_1506_);
                    crate::leanh::lean_dec_ref_known(v_x_1503_, 2);
                    v_fst_1507_ = crate::leanh::lean_ctor_get(v_head_1505_, 0);
                    crate::leanh::lean_inc(v_fst_1507_);
                    v_snd_1508_ = crate::leanh::lean_ctor_get(v_head_1505_, 1);
                    crate::leanh::lean_inc(v_snd_1508_);
                    crate::leanh::lean_dec(v_head_1505_);
                    crate::leanh::lean_inc_ref(v_inst_1501_);
                    crate::leanh::lean_inc(v_a_1502_);
                    v___x_1509_ = crate::leanh::lean_apply_2(v_inst_1501_, v_fst_1507_, v_a_1502_);
                    v___x_1510_ = (crate::leanh::lean_unbox(v___x_1509_) as u8);
                    if v___x_1510_ == 0 {
                        crate::leanh::lean_dec(v_snd_1508_);
                        v_x_1503_ = v_tail_1506_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1506_);
                        crate::leanh::lean_dec(v_a_1502_);
                        crate::leanh::lean_dec_ref(v_inst_1501_);
                        v___x_1512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1512_, 0, v_snd_1508_);
                        return v___x_1512_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x3f(
    mut v_00_u03b1_1513_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1514_: *mut crate::leanh::LeanObject,
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_x_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1515_, v_a_1516_, v_x_1517_);
    return v___x_1518_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(
    mut v_x_1519_: *mut crate::leanh::LeanObject,
    mut v_h__1_1520_: *mut crate::leanh::LeanObject,
    mut v_h__2_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1519_) == 0 {
        let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1521_);
        v___x_1522_ = crate::leanh::lean_box(0);
        v___x_1523_ = crate::leanh::lean_apply_1(v_h__1_1520_, v___x_1522_);
        return v___x_1523_;
    } else {
        let mut v_head_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1520_);
        v_head_1524_ = crate::leanh::lean_ctor_get(v_x_1519_, 0);
        crate::leanh::lean_inc(v_head_1524_);
        v_tail_1525_ = crate::leanh::lean_ctor_get(v_x_1519_, 1);
        crate::leanh::lean_inc(v_tail_1525_);
        crate::leanh::lean_dec_ref_known(v_x_1519_, 2);
        v_fst_1526_ = crate::leanh::lean_ctor_get(v_head_1524_, 0);
        crate::leanh::lean_inc(v_fst_1526_);
        v_snd_1527_ = crate::leanh::lean_ctor_get(v_head_1524_, 1);
        crate::leanh::lean_inc(v_snd_1527_);
        crate::leanh::lean_dec(v_head_1524_);
        v___x_1528_ =
            crate::leanh::lean_apply_3(v_h__2_1521_, v_fst_1526_, v_snd_1527_, v_tail_1525_);
        return v___x_1528_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(
    mut v_00_u03b1_1529_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1530_: *mut crate::leanh::LeanObject,
    mut v_motive_1531_: *mut crate::leanh::LeanObject,
    mut v_x_1532_: *mut crate::leanh::LeanObject,
    mut v_h__1_1533_: *mut crate::leanh::LeanObject,
    mut v_h__2_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1532_) == 0 {
        let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1534_);
        v___x_1535_ = crate::leanh::lean_box(0);
        v___x_1536_ = crate::leanh::lean_apply_1(v_h__1_1533_, v___x_1535_);
        return v___x_1536_;
    } else {
        let mut v_head_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1533_);
        v_head_1537_ = crate::leanh::lean_ctor_get(v_x_1532_, 0);
        crate::leanh::lean_inc(v_head_1537_);
        v_tail_1538_ = crate::leanh::lean_ctor_get(v_x_1532_, 1);
        crate::leanh::lean_inc(v_tail_1538_);
        crate::leanh::lean_dec_ref_known(v_x_1532_, 2);
        v_fst_1539_ = crate::leanh::lean_ctor_get(v_head_1537_, 0);
        crate::leanh::lean_inc(v_fst_1539_);
        v_snd_1540_ = crate::leanh::lean_ctor_get(v_head_1537_, 1);
        crate::leanh::lean_inc(v_snd_1540_);
        crate::leanh::lean_dec(v_head_1537_);
        v___x_1541_ =
            crate::leanh::lean_apply_3(v_h__2_1534_, v_fst_1539_, v_snd_1540_, v_tail_1538_);
        return v___x_1541_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x3f___redArg(
    mut v_inst_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_x_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1544_) == 0 {
                    crate::leanh::lean_dec(v_a_1543_);
                    crate::leanh::lean_dec_ref(v_inst_1542_);
                    v___x_1545_ = crate::leanh::lean_box(0);
                    return v___x_1545_;
                } else {
                    v_head_1546_ = crate::leanh::lean_ctor_get(v_x_1544_, 0);
                    crate::leanh::lean_inc(v_head_1546_);
                    v_tail_1547_ = crate::leanh::lean_ctor_get(v_x_1544_, 1);
                    crate::leanh::lean_inc(v_tail_1547_);
                    crate::leanh::lean_dec_ref_known(v_x_1544_, 2);
                    v_fst_1548_ = crate::leanh::lean_ctor_get(v_head_1546_, 0);
                    crate::leanh::lean_inc(v_fst_1548_);
                    v_snd_1549_ = crate::leanh::lean_ctor_get(v_head_1546_, 1);
                    crate::leanh::lean_inc(v_snd_1549_);
                    crate::leanh::lean_dec(v_head_1546_);
                    crate::leanh::lean_inc_ref(v_inst_1542_);
                    crate::leanh::lean_inc(v_a_1543_);
                    v___x_1550_ = crate::leanh::lean_apply_2(v_inst_1542_, v_fst_1548_, v_a_1543_);
                    v___x_1551_ = (crate::leanh::lean_unbox(v___x_1550_) as u8);
                    if v___x_1551_ == 0 {
                        crate::leanh::lean_dec(v_snd_1549_);
                        v_x_1544_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1547_);
                        crate::leanh::lean_dec(v_a_1543_);
                        crate::leanh::lean_dec_ref(v_inst_1542_);
                        v___x_1553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1553_, 0, v_snd_1549_);
                        return v___x_1553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x3f(
    mut v_00_u03b1_1554_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut crate::leanh::LeanObject,
    mut v_inst_1556_: *mut crate::leanh::LeanObject,
    mut v_inst_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_x_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1556_, v_a_1558_, v_x_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___lam__0(
    mut v_inst_1561_: *mut crate::leanh::LeanObject,
    mut v_inst_1562_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1563_: *mut crate::leanh::LeanObject,
    mut v_x_1564_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_fst_1565_ = crate::leanh::lean_ctor_get(v_x_1564_, 0);
    crate::leanh::lean_inc_n(v_fst_1565_, 2);
    v_snd_1566_ = crate::leanh::lean_ctor_get(v_x_1564_, 1);
    crate::leanh::lean_inc(v_snd_1566_);
    crate::leanh::lean_dec_ref(v_x_1564_);
    v___x_1567_ = crate::leanh::lean_apply_1(v_inst_1561_, v_fst_1565_);
    v___x_1568_ =
        l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1562_, v_fst_1565_, v_l_u2082_1563_);
    v___x_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1569_, 0, v_snd_1566_);
    v___x_1570_ = l_Option_instBEq_beq___redArg(v___x_1567_, v___x_1568_, v___x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___lam__0___boxed(
    mut v_inst_1571_: *mut crate::leanh::LeanObject,
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1573_: *mut crate::leanh::LeanObject,
    mut v_x_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1575_: u8 = 0;
    let mut v_r_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1575_ = l_Std_Internal_List_beqModel___redArg___lam__0(
        v_inst_1571_,
        v_inst_1572_,
        v_l_u2082_1573_,
        v_x_1574_,
    );
    v_r_1576_ = crate::leanh::lean_box((v_res_1575_) as usize);
    return v_r_1576_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg(
    mut v_inst_1577_: *mut crate::leanh::LeanObject,
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1579_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1580_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    v___x_1581_ = l_List_lengthTR___redArg(v_l_u2081_1579_);
    v___x_1582_ = l_List_lengthTR___redArg(v_l_u2082_1580_);
    v___x_1583_ = lean_nat_dec_eq(v___x_1581_, v___x_1582_);
    crate::leanh::lean_dec(v___x_1582_);
    crate::leanh::lean_dec(v___x_1581_);
    if v___x_1583_ == 0 {
        crate::leanh::lean_dec(v_l_u2082_1580_);
        crate::leanh::lean_dec(v_l_u2081_1579_);
        crate::leanh::lean_dec_ref(v_inst_1578_);
        crate::leanh::lean_dec_ref(v_inst_1577_);
        return v___x_1583_;
    } else {
        let mut v___f_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: u8 = 0;
        v___f_1584_ = crate::leanh::lean_alloc_closure(
            l_Std_Internal_List_beqModel___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1584_, 0, v_inst_1578_);
        crate::leanh::lean_closure_set(v___f_1584_, 1, v_inst_1577_);
        crate::leanh::lean_closure_set(v___f_1584_, 2, v_l_u2082_1580_);
        v___x_1585_ = l_List_all___redArg(v_l_u2081_1579_, v___f_1584_);
        return v___x_1585_;
    }
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___boxed(
    mut v_inst_1586_: *mut crate::leanh::LeanObject,
    mut v_inst_1587_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1588_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: u8 = 0;
    let mut v_r_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_Internal_List_beqModel___redArg(
        v_inst_1586_,
        v_inst_1587_,
        v_l_u2081_1588_,
        v_l_u2082_1589_,
    );
    v_r_1591_ = crate::leanh::lean_box((v_res_1590_) as usize);
    return v_r_1591_;
}
pub unsafe fn l_Std_Internal_List_beqModel(
    mut v_00_u03b1_1592_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1593_: *mut crate::leanh::LeanObject,
    mut v_inst_1594_: *mut crate::leanh::LeanObject,
    mut v_inst_1595_: *mut crate::leanh::LeanObject,
    mut v_inst_1596_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1597_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1598_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1599_: u8 = 0;
    v___x_1599_ = l_Std_Internal_List_beqModel___redArg(
        v_inst_1594_,
        v_inst_1596_,
        v_l_u2081_1597_,
        v_l_u2082_1598_,
    );
    return v___x_1599_;
}
pub unsafe fn l_Std_Internal_List_beqModel___boxed(
    mut v_00_u03b1_1600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1601_: *mut crate::leanh::LeanObject,
    mut v_inst_1602_: *mut crate::leanh::LeanObject,
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
    mut v_inst_1604_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1605_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: u8 = 0;
    let mut v_r_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Std_Internal_List_beqModel(
        v_00_u03b1_1600_,
        v_00_u03b2_1601_,
        v_inst_1602_,
        v_inst_1603_,
        v_inst_1604_,
        v_l_u2081_1605_,
        v_l_u2082_1606_,
    );
    v_r_1608_ = crate::leanh::lean_box((v_res_1607_) as usize);
    return v_r_1608_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(
    mut v_x_1609_: *mut crate::leanh::LeanObject,
    mut v_h__1_1610_: *mut crate::leanh::LeanObject,
    mut v_h__2_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1609_) == 0 {
        let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1611_);
        v___x_1612_ = crate::leanh::lean_box(0);
        v___x_1613_ = crate::leanh::lean_apply_1(v_h__1_1610_, v___x_1612_);
        return v___x_1613_;
    } else {
        let mut v_head_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1610_);
        v_head_1614_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
        crate::leanh::lean_inc(v_head_1614_);
        v_tail_1615_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
        crate::leanh::lean_inc(v_tail_1615_);
        crate::leanh::lean_dec_ref_known(v_x_1609_, 2);
        v_fst_1616_ = crate::leanh::lean_ctor_get(v_head_1614_, 0);
        crate::leanh::lean_inc(v_fst_1616_);
        v_snd_1617_ = crate::leanh::lean_ctor_get(v_head_1614_, 1);
        crate::leanh::lean_inc(v_snd_1617_);
        crate::leanh::lean_dec(v_head_1614_);
        v___x_1618_ =
            crate::leanh::lean_apply_3(v_h__2_1611_, v_fst_1616_, v_snd_1617_, v_tail_1615_);
        return v___x_1618_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(
    mut v_00_u03b1_1619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut crate::leanh::LeanObject,
    mut v_motive_1621_: *mut crate::leanh::LeanObject,
    mut v_x_1622_: *mut crate::leanh::LeanObject,
    mut v_h__1_1623_: *mut crate::leanh::LeanObject,
    mut v_h__2_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1622_) == 0 {
        let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1624_);
        v___x_1625_ = crate::leanh::lean_box(0);
        v___x_1626_ = crate::leanh::lean_apply_1(v_h__1_1623_, v___x_1625_);
        return v___x_1626_;
    } else {
        let mut v_head_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1623_);
        v_head_1627_ = crate::leanh::lean_ctor_get(v_x_1622_, 0);
        crate::leanh::lean_inc(v_head_1627_);
        v_tail_1628_ = crate::leanh::lean_ctor_get(v_x_1622_, 1);
        crate::leanh::lean_inc(v_tail_1628_);
        crate::leanh::lean_dec_ref_known(v_x_1622_, 2);
        v_fst_1629_ = crate::leanh::lean_ctor_get(v_head_1627_, 0);
        crate::leanh::lean_inc(v_fst_1629_);
        v_snd_1630_ = crate::leanh::lean_ctor_get(v_head_1627_, 1);
        crate::leanh::lean_inc(v_snd_1630_);
        crate::leanh::lean_dec(v_head_1627_);
        v___x_1631_ =
            crate::leanh::lean_apply_3(v_h__2_1624_, v_fst_1629_, v_snd_1630_, v_tail_1628_);
        return v___x_1631_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___lam__0(
    mut v_inst_1632_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1633_: *mut crate::leanh::LeanObject,
    mut v_inst_1634_: *mut crate::leanh::LeanObject,
    mut v_x_1635_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    v_fst_1636_ = crate::leanh::lean_ctor_get(v_x_1635_, 0);
    crate::leanh::lean_inc(v_fst_1636_);
    v_snd_1637_ = crate::leanh::lean_ctor_get(v_x_1635_, 1);
    crate::leanh::lean_inc(v_snd_1637_);
    crate::leanh::lean_dec_ref(v_x_1635_);
    v___x_1638_ =
        l_Std_Internal_List_getValue_x3f___redArg(v_inst_1632_, v_fst_1636_, v_l_u2082_1633_);
    v___x_1639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1639_, 0, v_snd_1637_);
    v___x_1640_ = l_Option_instBEq_beq___redArg(v_inst_1634_, v___x_1638_, v___x_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(
    mut v_inst_1641_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1642_: *mut crate::leanh::LeanObject,
    mut v_inst_1643_: *mut crate::leanh::LeanObject,
    mut v_x_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1645_: u8 = 0;
    let mut v_r_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(
        v_inst_1641_,
        v_l_u2082_1642_,
        v_inst_1643_,
        v_x_1644_,
    );
    v_r_1646_ = crate::leanh::lean_box((v_res_1645_) as usize);
    return v_r_1646_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg(
    mut v_inst_1647_: *mut crate::leanh::LeanObject,
    mut v_inst_1648_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1649_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1650_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    v___x_1651_ = l_List_lengthTR___redArg(v_l_u2081_1649_);
    v___x_1652_ = l_List_lengthTR___redArg(v_l_u2082_1650_);
    v___x_1653_ = lean_nat_dec_eq(v___x_1651_, v___x_1652_);
    crate::leanh::lean_dec(v___x_1652_);
    crate::leanh::lean_dec(v___x_1651_);
    if v___x_1653_ == 0 {
        crate::leanh::lean_dec(v_l_u2082_1650_);
        crate::leanh::lean_dec(v_l_u2081_1649_);
        crate::leanh::lean_dec_ref(v_inst_1648_);
        crate::leanh::lean_dec_ref(v_inst_1647_);
        return v___x_1653_;
    } else {
        let mut v___f_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: u8 = 0;
        v___f_1654_ = crate::leanh::lean_alloc_closure(
            l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1654_, 0, v_inst_1647_);
        crate::leanh::lean_closure_set(v___f_1654_, 1, v_l_u2082_1650_);
        crate::leanh::lean_closure_set(v___f_1654_, 2, v_inst_1648_);
        v___x_1655_ = l_List_all___redArg(v_l_u2081_1649_, v___f_1654_);
        return v___x_1655_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___boxed(
    mut v_inst_1656_: *mut crate::leanh::LeanObject,
    mut v_inst_1657_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1658_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1660_: u8 = 0;
    let mut v_r_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Std_Internal_List_Const_beqModel___redArg(
        v_inst_1656_,
        v_inst_1657_,
        v_l_u2081_1658_,
        v_l_u2082_1659_,
    );
    v_r_1661_ = crate::leanh::lean_box((v_res_1660_) as usize);
    return v_r_1661_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel(
    mut v_00_u03b1_1662_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1663_: *mut crate::leanh::LeanObject,
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1666_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1667_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1668_: u8 = 0;
    v___x_1668_ = l_Std_Internal_List_Const_beqModel___redArg(
        v_inst_1664_,
        v_inst_1665_,
        v_l_u2081_1666_,
        v_l_u2082_1667_,
    );
    return v___x_1668_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___boxed(
    mut v_00_u03b1_1669_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_1673_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1675_: u8 = 0;
    let mut v_r_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Std_Internal_List_Const_beqModel(
        v_00_u03b1_1669_,
        v_00_u03b2_1670_,
        v_inst_1671_,
        v_inst_1672_,
        v_l_u2081_1673_,
        v_l_u2082_1674_,
    );
    v_r_1676_ = crate::leanh::lean_box((v_res_1675_) as usize);
    return v_r_1676_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
    mut v_x_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1677_) == 0 {
                    crate::leanh::lean_dec(v_x_1678_);
                    v___x_1679_ = crate::leanh::lean_box(0);
                    return v___x_1679_;
                } else {
                    v_val_1680_ = crate::leanh::lean_ctor_get(v_x_1677_, 0);
                    v_isSharedCheck_1688_ = (!crate::leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v___x_1682_ = v_x_1677_;
                        v_isShared_1683_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1680_);
                        crate::leanh::lean_dec(v_x_1677_);
                        v___x_1682_ = crate::leanh::lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1684_ =
                    crate::leanh::lean_apply_2(v_x_1678_, v_val_1680_, crate::leanh::lean_box(0));
                if v_isShared_1683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1684_);
                    v___x_1686_ = v___x_1682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
                    v___x_1686_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(
    mut v_00_u03b1_1689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
    mut v_x_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ =
        l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(
            v_x_1691_, v_x_1692_,
        );
    return v___x_1693_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(
    mut v_x_1694_: *mut crate::leanh::LeanObject,
    mut v_x_1695_: *mut crate::leanh::LeanObject,
    mut v_h__1_1696_: *mut crate::leanh::LeanObject,
    mut v_h__2_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1694_) == 0 {
        let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1697_);
        v___x_1698_ = crate::leanh::lean_apply_1(v_h__1_1696_, v_x_1695_);
        return v___x_1698_;
    } else {
        let mut v_val_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1696_);
        v_val_1699_ = crate::leanh::lean_ctor_get(v_x_1694_, 0);
        crate::leanh::lean_inc(v_val_1699_);
        crate::leanh::lean_dec_ref_known(v_x_1694_, 1);
        v___x_1700_ = crate::leanh::lean_apply_2(v_h__2_1697_, v_val_1699_, v_x_1695_);
        return v___x_1700_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(
    mut v_00_u03b1_1701_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1702_: *mut crate::leanh::LeanObject,
    mut v_motive_1703_: *mut crate::leanh::LeanObject,
    mut v_x_1704_: *mut crate::leanh::LeanObject,
    mut v_x_1705_: *mut crate::leanh::LeanObject,
    mut v_h__1_1706_: *mut crate::leanh::LeanObject,
    mut v_h__2_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1704_) == 0 {
        let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1707_);
        v___x_1708_ = crate::leanh::lean_apply_1(v_h__1_1706_, v_x_1705_);
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1706_);
        v_val_1709_ = crate::leanh::lean_ctor_get(v_x_1704_, 0);
        crate::leanh::lean_inc(v_val_1709_);
        crate::leanh::lean_dec_ref_known(v_x_1704_, 1);
        v___x_1710_ = crate::leanh::lean_apply_2(v_h__2_1707_, v_val_1709_, v_x_1705_);
        return v___x_1710_;
    }
}
pub unsafe fn l_Std_Internal_List_containsKey___redArg(
    mut v_inst_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_x_1713_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1714_: u8 = 0;
    let mut v_head_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1713_) == 0 {
                    crate::leanh::lean_dec(v_a_1712_);
                    crate::leanh::lean_dec_ref(v_inst_1711_);
                    v___x_1714_ = 0;
                    return v___x_1714_;
                } else {
                    v_head_1715_ = crate::leanh::lean_ctor_get(v_x_1713_, 0);
                    crate::leanh::lean_inc(v_head_1715_);
                    v_tail_1716_ = crate::leanh::lean_ctor_get(v_x_1713_, 1);
                    crate::leanh::lean_inc(v_tail_1716_);
                    crate::leanh::lean_dec_ref_known(v_x_1713_, 2);
                    v_fst_1717_ = crate::leanh::lean_ctor_get(v_head_1715_, 0);
                    crate::leanh::lean_inc(v_fst_1717_);
                    crate::leanh::lean_dec(v_head_1715_);
                    crate::leanh::lean_inc_ref(v_inst_1711_);
                    crate::leanh::lean_inc(v_a_1712_);
                    v___x_1718_ = crate::leanh::lean_apply_2(v_inst_1711_, v_fst_1717_, v_a_1712_);
                    v___x_1719_ = (crate::leanh::lean_unbox(v___x_1718_) as u8);
                    if v___x_1719_ == 0 {
                        v_x_1713_ = v_tail_1716_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1716_);
                        crate::leanh::lean_dec(v_a_1712_);
                        crate::leanh::lean_dec_ref(v_inst_1711_);
                        v___x_1721_ = (crate::leanh::lean_unbox(v___x_1718_) as u8);
                        return v___x_1721_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_containsKey___redArg___boxed(
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_x_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1725_: u8 = 0;
    let mut v_r_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Std_Internal_List_containsKey___redArg(v_inst_1722_, v_a_1723_, v_x_1724_);
    v_r_1726_ = crate::leanh::lean_box((v_res_1725_) as usize);
    return v_r_1726_;
}
pub unsafe fn l_Std_Internal_List_containsKey(
    mut v_00_u03b1_1727_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1728_: *mut crate::leanh::LeanObject,
    mut v_inst_1729_: *mut crate::leanh::LeanObject,
    mut v_a_1730_: *mut crate::leanh::LeanObject,
    mut v_x_1731_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1732_: u8 = 0;
    v___x_1732_ = l_Std_Internal_List_containsKey___redArg(v_inst_1729_, v_a_1730_, v_x_1731_);
    return v___x_1732_;
}
pub unsafe fn l_Std_Internal_List_containsKey___boxed(
    mut v_00_u03b1_1733_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1734_: *mut crate::leanh::LeanObject,
    mut v_inst_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1738_: u8 = 0;
    let mut v_r_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1738_ = l_Std_Internal_List_containsKey(
        v_00_u03b1_1733_,
        v_00_u03b2_1734_,
        v_inst_1735_,
        v_a_1736_,
        v_x_1737_,
    );
    v_r_1739_ = crate::leanh::lean_box((v_res_1738_) as usize);
    return v_r_1739_;
}
pub unsafe fn l_Std_Internal_List_getEntry___redArg(
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_l_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1740_, v_a_1741_, v_l_1742_);
    v_val_1744_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
    crate::leanh::lean_inc(v_val_1744_);
    crate::leanh::lean_dec(v___x_1743_);
    return v_val_1744_;
}
pub unsafe fn l_Std_Internal_List_getEntry(
    mut v_00_u03b1_1745_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1746_: *mut crate::leanh::LeanObject,
    mut v_inst_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_l_1749_: *mut crate::leanh::LeanObject,
    mut v_h_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Std_Internal_List_getEntry___redArg(v_inst_1747_, v_a_1748_, v_l_1749_);
    return v___x_1751_;
}
pub unsafe fn l_Std_Internal_List_getValue___redArg(
    mut v_inst_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_l_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1752_, v_a_1753_, v_l_1754_);
    v_val_1756_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
    crate::leanh::lean_inc(v_val_1756_);
    crate::leanh::lean_dec(v___x_1755_);
    return v_val_1756_;
}
pub unsafe fn l_Std_Internal_List_getValue(
    mut v_00_u03b1_1757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1758_: *mut crate::leanh::LeanObject,
    mut v_inst_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_l_1761_: *mut crate::leanh::LeanObject,
    mut v_h_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Std_Internal_List_getValue___redArg(v_inst_1759_, v_a_1760_, v_l_1761_);
    return v___x_1763_;
}
pub unsafe fn l_Std_Internal_List_getValueCast___redArg(
    mut v_inst_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_l_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1764_, v_a_1765_, v_l_1766_);
    v_val_1768_ = crate::leanh::lean_ctor_get(v___x_1767_, 0);
    crate::leanh::lean_inc(v_val_1768_);
    crate::leanh::lean_dec(v___x_1767_);
    return v_val_1768_;
}
pub unsafe fn l_Std_Internal_List_getValueCast(
    mut v_00_u03b1_1769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1770_: *mut crate::leanh::LeanObject,
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_inst_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_l_1774_: *mut crate::leanh::LeanObject,
    mut v_h_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = l_Std_Internal_List_getValueCast___redArg(v_inst_1771_, v_a_1773_, v_l_1774_);
    return v___x_1776_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD___redArg(
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_l_1779_: *mut crate::leanh::LeanObject,
    mut v_fallback_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1777_, v_a_1778_, v_l_1779_);
    if crate::leanh::lean_obj_tag(v___x_1781_) == 0 {
        crate::leanh::lean_inc(v_fallback_1780_);
        return v_fallback_1780_;
    } else {
        let mut v_val_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1782_ = crate::leanh::lean_ctor_get(v___x_1781_, 0);
        crate::leanh::lean_inc(v_val_1782_);
        crate::leanh::lean_dec_ref_known(v___x_1781_, 1);
        return v_val_1782_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCastD___redArg___boxed(
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_l_1785_: *mut crate::leanh::LeanObject,
    mut v_fallback_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_Internal_List_getValueCastD___redArg(
        v_inst_1783_,
        v_a_1784_,
        v_l_1785_,
        v_fallback_1786_,
    );
    crate::leanh::lean_dec(v_fallback_1786_);
    return v_res_1787_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD(
    mut v_00_u03b1_1788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_inst_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_l_1793_: *mut crate::leanh::LeanObject,
    mut v_fallback_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Std_Internal_List_getValueCastD___redArg(
        v_inst_1790_,
        v_a_1792_,
        v_l_1793_,
        v_fallback_1794_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD___boxed(
    mut v_00_u03b1_1796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_l_1801_: *mut crate::leanh::LeanObject,
    mut v_fallback_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1803_ = l_Std_Internal_List_getValueCastD(
        v_00_u03b1_1796_,
        v_00_u03b2_1797_,
        v_inst_1798_,
        v_inst_1799_,
        v_a_1800_,
        v_l_1801_,
        v_fallback_1802_,
    );
    crate::leanh::lean_dec(v_fallback_1802_);
    return v_res_1803_;
}
pub unsafe fn _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Std_Internal_List_getValueCast_x21___redArg___closed__2;
    v___x_1808_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1809_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1810_ = l_Std_Internal_List_getValueCast_x21___redArg___closed__1;
    v___x_1811_ = l_Std_Internal_List_getValueCast_x21___redArg___closed__0;
    v___x_1812_ = l_mkPanicMessageWithDecl(
        v___x_1811_,
        v___x_1810_,
        v___x_1809_,
        v___x_1808_,
        v___x_1807_,
    );
    return v___x_1812_;
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21___redArg(
    mut v_inst_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_inst_1815_: *mut crate::leanh::LeanObject,
    mut v_l_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1813_, v_a_1814_, v_l_1816_);
    if crate::leanh::lean_obj_tag(v___x_1817_) == 0 {
        let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1818_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1819_ = l_panic___redArg(v_inst_1815_, v___x_1818_);
        return v___x_1819_;
    } else {
        let mut v_val_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1820_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
        crate::leanh::lean_inc(v_val_1820_);
        crate::leanh::lean_dec_ref_known(v___x_1817_, 1);
        return v_val_1820_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21___redArg___boxed(
    mut v_inst_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_inst_1823_: *mut crate::leanh::LeanObject,
    mut v_l_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_Std_Internal_List_getValueCast_x21___redArg(
        v_inst_1821_,
        v_a_1822_,
        v_inst_1823_,
        v_l_1824_,
    );
    crate::leanh::lean_dec(v_inst_1823_);
    return v_res_1825_;
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21(
    mut v_00_u03b1_1826_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut crate::leanh::LeanObject,
    mut v_inst_1828_: *mut crate::leanh::LeanObject,
    mut v_inst_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
    mut v_l_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Std_Internal_List_getValueCast_x21___redArg(
        v_inst_1828_,
        v_a_1830_,
        v_inst_1831_,
        v_l_1832_,
    );
    return v___x_1833_;
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21___boxed(
    mut v_00_u03b1_1834_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1835_: *mut crate::leanh::LeanObject,
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_inst_1839_: *mut crate::leanh::LeanObject,
    mut v_l_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Std_Internal_List_getValueCast_x21(
        v_00_u03b1_1834_,
        v_00_u03b2_1835_,
        v_inst_1836_,
        v_inst_1837_,
        v_a_1838_,
        v_inst_1839_,
        v_l_1840_,
    );
    crate::leanh::lean_dec(v_inst_1839_);
    return v_res_1841_;
}
pub unsafe fn l_Std_Internal_List_getValueD___redArg(
    mut v_inst_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_l_1844_: *mut crate::leanh::LeanObject,
    mut v_fallback_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1842_, v_a_1843_, v_l_1844_);
    if crate::leanh::lean_obj_tag(v___x_1846_) == 0 {
        crate::leanh::lean_inc(v_fallback_1845_);
        return v_fallback_1845_;
    } else {
        let mut v_val_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
        crate::leanh::lean_inc(v_val_1847_);
        crate::leanh::lean_dec_ref_known(v___x_1846_, 1);
        return v_val_1847_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueD___redArg___boxed(
    mut v_inst_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_l_1850_: *mut crate::leanh::LeanObject,
    mut v_fallback_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Std_Internal_List_getValueD___redArg(
        v_inst_1848_,
        v_a_1849_,
        v_l_1850_,
        v_fallback_1851_,
    );
    crate::leanh::lean_dec(v_fallback_1851_);
    return v_res_1852_;
}
pub unsafe fn l_Std_Internal_List_getValueD(
    mut v_00_u03b1_1853_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1854_: *mut crate::leanh::LeanObject,
    mut v_inst_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_l_1857_: *mut crate::leanh::LeanObject,
    mut v_fallback_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Std_Internal_List_getValueD___redArg(
        v_inst_1855_,
        v_a_1856_,
        v_l_1857_,
        v_fallback_1858_,
    );
    return v___x_1859_;
}
pub unsafe fn l_Std_Internal_List_getValueD___boxed(
    mut v_00_u03b1_1860_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1861_: *mut crate::leanh::LeanObject,
    mut v_inst_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_l_1864_: *mut crate::leanh::LeanObject,
    mut v_fallback_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_Internal_List_getValueD(
        v_00_u03b1_1860_,
        v_00_u03b2_1861_,
        v_inst_1862_,
        v_a_1863_,
        v_l_1864_,
        v_fallback_1865_,
    );
    crate::leanh::lean_dec(v_fallback_1865_);
    return v_res_1866_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21___redArg(
    mut v_inst_1867_: *mut crate::leanh::LeanObject,
    mut v_inst_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_l_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1867_, v_a_1869_, v_l_1870_);
    if crate::leanh::lean_obj_tag(v___x_1871_) == 0 {
        let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1872_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1873_ = l_panic___redArg(v_inst_1868_, v___x_1872_);
        return v___x_1873_;
    } else {
        let mut v_val_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1874_ = crate::leanh::lean_ctor_get(v___x_1871_, 0);
        crate::leanh::lean_inc(v_val_1874_);
        crate::leanh::lean_dec_ref_known(v___x_1871_, 1);
        return v_val_1874_;
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x21___redArg___boxed(
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_l_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ =
        l_Std_Internal_List_getValue_x21___redArg(v_inst_1875_, v_inst_1876_, v_a_1877_, v_l_1878_);
    crate::leanh::lean_dec(v_inst_1876_);
    return v_res_1879_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21(
    mut v_00_u03b1_1880_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1881_: *mut crate::leanh::LeanObject,
    mut v_inst_1882_: *mut crate::leanh::LeanObject,
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_l_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ =
        l_Std_Internal_List_getValue_x21___redArg(v_inst_1882_, v_inst_1883_, v_a_1884_, v_l_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21___boxed(
    mut v_00_u03b1_1887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1888_: *mut crate::leanh::LeanObject,
    mut v_inst_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_l_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Std_Internal_List_getValue_x21(
        v_00_u03b1_1887_,
        v_00_u03b2_1888_,
        v_inst_1889_,
        v_inst_1890_,
        v_a_1891_,
        v_l_1892_,
    );
    crate::leanh::lean_dec(v_inst_1890_);
    return v_res_1893_;
}
pub unsafe fn l_Std_Internal_List_getKey_x3f___redArg(
    mut v_inst_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1896_) == 0 {
                    crate::leanh::lean_dec(v_a_1895_);
                    crate::leanh::lean_dec_ref(v_inst_1894_);
                    v___x_1897_ = crate::leanh::lean_box(0);
                    return v___x_1897_;
                } else {
                    v_head_1898_ = crate::leanh::lean_ctor_get(v_x_1896_, 0);
                    crate::leanh::lean_inc(v_head_1898_);
                    v_tail_1899_ = crate::leanh::lean_ctor_get(v_x_1896_, 1);
                    crate::leanh::lean_inc(v_tail_1899_);
                    crate::leanh::lean_dec_ref_known(v_x_1896_, 2);
                    v_fst_1900_ = crate::leanh::lean_ctor_get(v_head_1898_, 0);
                    crate::leanh::lean_inc_n(v_fst_1900_, 2);
                    crate::leanh::lean_dec(v_head_1898_);
                    crate::leanh::lean_inc_ref(v_inst_1894_);
                    crate::leanh::lean_inc(v_a_1895_);
                    v___x_1901_ = crate::leanh::lean_apply_2(v_inst_1894_, v_fst_1900_, v_a_1895_);
                    v___x_1902_ = (crate::leanh::lean_unbox(v___x_1901_) as u8);
                    if v___x_1902_ == 0 {
                        crate::leanh::lean_dec(v_fst_1900_);
                        v_x_1896_ = v_tail_1899_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1899_);
                        crate::leanh::lean_dec(v_a_1895_);
                        crate::leanh::lean_dec_ref(v_inst_1894_);
                        v___x_1904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1904_, 0, v_fst_1900_);
                        return v___x_1904_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getKey_x3f(
    mut v_00_u03b1_1905_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1906_: *mut crate::leanh::LeanObject,
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1907_, v_a_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Std_Internal_List_getKey___redArg(
    mut v_inst_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
    mut v_l_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1911_, v_a_1912_, v_l_1913_);
    v_val_1915_ = crate::leanh::lean_ctor_get(v___x_1914_, 0);
    crate::leanh::lean_inc(v_val_1915_);
    crate::leanh::lean_dec(v___x_1914_);
    return v_val_1915_;
}
pub unsafe fn l_Std_Internal_List_getKey(
    mut v_00_u03b1_1916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1917_: *mut crate::leanh::LeanObject,
    mut v_inst_1918_: *mut crate::leanh::LeanObject,
    mut v_a_1919_: *mut crate::leanh::LeanObject,
    mut v_l_1920_: *mut crate::leanh::LeanObject,
    mut v_h_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Std_Internal_List_getKey___redArg(v_inst_1918_, v_a_1919_, v_l_1920_);
    return v___x_1922_;
}
pub unsafe fn l_Std_Internal_List_getKeyD___redArg(
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_a_1924_: *mut crate::leanh::LeanObject,
    mut v_l_1925_: *mut crate::leanh::LeanObject,
    mut v_fallback_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1923_, v_a_1924_, v_l_1925_);
    if crate::leanh::lean_obj_tag(v___x_1927_) == 0 {
        crate::leanh::lean_inc(v_fallback_1926_);
        return v_fallback_1926_;
    } else {
        let mut v_val_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1928_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
        crate::leanh::lean_inc(v_val_1928_);
        crate::leanh::lean_dec_ref_known(v___x_1927_, 1);
        return v_val_1928_;
    }
}
pub unsafe fn l_Std_Internal_List_getKeyD___redArg___boxed(
    mut v_inst_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
    mut v_l_1931_: *mut crate::leanh::LeanObject,
    mut v_fallback_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ =
        l_Std_Internal_List_getKeyD___redArg(v_inst_1929_, v_a_1930_, v_l_1931_, v_fallback_1932_);
    crate::leanh::lean_dec(v_fallback_1932_);
    return v_res_1933_;
}
pub unsafe fn l_Std_Internal_List_getKeyD(
    mut v_00_u03b1_1934_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_l_1938_: *mut crate::leanh::LeanObject,
    mut v_fallback_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ =
        l_Std_Internal_List_getKeyD___redArg(v_inst_1936_, v_a_1937_, v_l_1938_, v_fallback_1939_);
    return v___x_1940_;
}
pub unsafe fn l_Std_Internal_List_getKeyD___boxed(
    mut v_00_u03b1_1941_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1942_: *mut crate::leanh::LeanObject,
    mut v_inst_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
    mut v_l_1945_: *mut crate::leanh::LeanObject,
    mut v_fallback_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Std_Internal_List_getKeyD(
        v_00_u03b1_1941_,
        v_00_u03b2_1942_,
        v_inst_1943_,
        v_a_1944_,
        v_l_1945_,
        v_fallback_1946_,
    );
    crate::leanh::lean_dec(v_fallback_1946_);
    return v_res_1947_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21___redArg(
    mut v_inst_1948_: *mut crate::leanh::LeanObject,
    mut v_inst_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_l_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1948_, v_a_1950_, v_l_1951_);
    if crate::leanh::lean_obj_tag(v___x_1952_) == 0 {
        let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1953_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1954_ = l_panic___redArg(v_inst_1949_, v___x_1953_);
        return v___x_1954_;
    } else {
        let mut v_val_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1955_ = crate::leanh::lean_ctor_get(v___x_1952_, 0);
        crate::leanh::lean_inc(v_val_1955_);
        crate::leanh::lean_dec_ref_known(v___x_1952_, 1);
        return v_val_1955_;
    }
}
pub unsafe fn l_Std_Internal_List_getKey_x21___redArg___boxed(
    mut v_inst_1956_: *mut crate::leanh::LeanObject,
    mut v_inst_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_l_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ =
        l_Std_Internal_List_getKey_x21___redArg(v_inst_1956_, v_inst_1957_, v_a_1958_, v_l_1959_);
    crate::leanh::lean_dec(v_inst_1957_);
    return v_res_1960_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1962_: *mut crate::leanh::LeanObject,
    mut v_inst_1963_: *mut crate::leanh::LeanObject,
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
    mut v_a_1965_: *mut crate::leanh::LeanObject,
    mut v_l_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ =
        l_Std_Internal_List_getKey_x21___redArg(v_inst_1963_, v_inst_1964_, v_a_1965_, v_l_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21___boxed(
    mut v_00_u03b1_1968_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1969_: *mut crate::leanh::LeanObject,
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_l_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1974_ = l_Std_Internal_List_getKey_x21(
        v_00_u03b1_1968_,
        v_00_u03b2_1969_,
        v_inst_1970_,
        v_inst_1971_,
        v_a_1972_,
        v_l_1973_,
    );
    crate::leanh::lean_dec(v_inst_1971_);
    return v_res_1974_;
}
pub unsafe fn l_Std_Internal_List_replaceEntry___redArg(
    mut v_inst_1975_: *mut crate::leanh::LeanObject,
    mut v_k_1976_: *mut crate::leanh::LeanObject,
    mut v_v_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v_fst_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_unused_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1978_) == 0 {
                    crate::leanh::lean_dec(v_v_1977_);
                    crate::leanh::lean_dec(v_k_1976_);
                    crate::leanh::lean_dec_ref(v_inst_1975_);
                    v___x_1979_ = crate::leanh::lean_box(0);
                    return v___x_1979_;
                } else {
                    v_head_1980_ = crate::leanh::lean_ctor_get(v_x_1978_, 0);
                    v_tail_1981_ = crate::leanh::lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1983_ = v_x_1978_;
                        v_isShared_1984_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1981_);
                        crate::leanh::lean_inc(v_head_1980_);
                        crate::leanh::lean_dec(v_x_1978_);
                        v___x_1983_ = crate::leanh::lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1985_ = crate::leanh::lean_ctor_get(v_head_1980_, 0);
                crate::leanh::lean_inc_ref(v_inst_1975_);
                crate::leanh::lean_inc(v_k_1976_);
                crate::leanh::lean_inc(v_fst_1985_);
                v___x_1986_ = crate::leanh::lean_apply_2(v_inst_1975_, v_fst_1985_, v_k_1976_);
                v___x_1987_ = (crate::leanh::lean_unbox(v___x_1986_) as u8);
                if v___x_1987_ == 0 {
                    v___x_1988_ = l_Std_Internal_List_replaceEntry___redArg(
                        v_inst_1975_,
                        v_k_1976_,
                        v_v_1977_,
                        v_tail_1981_,
                    );
                    if v_isShared_1984_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1983_, 1, v___x_1988_);
                        v___x_1990_ = v___x_1983_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1991_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_head_1980_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1988_);
                        v___x_1990_ = v_reuseFailAlloc_1991_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1975_);
                    v_isSharedCheck_2001_ = (!crate::leanh::lean_is_exclusive(v_head_1980_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v_unused_2002_ = crate::leanh::lean_ctor_get(v_head_1980_, 1);
                        crate::leanh::lean_dec(v_unused_2002_);
                        v_unused_2003_ = crate::leanh::lean_ctor_get(v_head_1980_, 0);
                        crate::leanh::lean_dec(v_unused_2003_);
                        v___x_1993_ = v_head_1980_;
                        v_isShared_1994_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_1980_);
                        v___x_1993_ = crate::leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1990_;
            }
            3 => {
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 1, v_v_1977_);
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v_k_1976_);
                    v___x_1996_ = v___x_1993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_k_1976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_v_1977_);
                    v___x_1996_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1983_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1983_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_tail_1981_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_replaceEntry(
    mut v_00_u03b1_2005_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2006_: *mut crate::leanh::LeanObject,
    mut v_inst_2007_: *mut crate::leanh::LeanObject,
    mut v_k_2008_: *mut crate::leanh::LeanObject,
    mut v_v_2009_: *mut crate::leanh::LeanObject,
    mut v_x_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ =
        l_Std_Internal_List_replaceEntry___redArg(v_inst_2007_, v_k_2008_, v_v_2009_, v_x_2010_);
    return v___x_2011_;
}
pub unsafe fn l_Std_Internal_List_eraseKey___redArg(
    mut v_inst_2012_: *mut crate::leanh::LeanObject,
    mut v_k_2013_: *mut crate::leanh::LeanObject,
    mut v_x_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v_fst_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2014_) == 0 {
                    crate::leanh::lean_dec(v_k_2013_);
                    crate::leanh::lean_dec_ref(v_inst_2012_);
                    v___x_2015_ = crate::leanh::lean_box(0);
                    return v___x_2015_;
                } else {
                    v_head_2016_ = crate::leanh::lean_ctor_get(v_x_2014_, 0);
                    v_tail_2017_ = crate::leanh::lean_ctor_get(v_x_2014_, 1);
                    v_isSharedCheck_2028_ = (!crate::leanh::lean_is_exclusive(v_x_2014_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_2019_ = v_x_2014_;
                        v_isShared_2020_ = v_isSharedCheck_2028_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2017_);
                        crate::leanh::lean_inc(v_head_2016_);
                        crate::leanh::lean_dec(v_x_2014_);
                        v___x_2019_ = crate::leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2028_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2021_ = crate::leanh::lean_ctor_get(v_head_2016_, 0);
                crate::leanh::lean_inc_ref(v_inst_2012_);
                crate::leanh::lean_inc(v_k_2013_);
                crate::leanh::lean_inc(v_fst_2021_);
                v___x_2022_ = crate::leanh::lean_apply_2(v_inst_2012_, v_fst_2021_, v_k_2013_);
                v___x_2023_ = (crate::leanh::lean_unbox(v___x_2022_) as u8);
                if v___x_2023_ == 0 {
                    v___x_2024_ = l_Std_Internal_List_eraseKey___redArg(
                        v_inst_2012_,
                        v_k_2013_,
                        v_tail_2017_,
                    );
                    if v_isShared_2020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2024_);
                        v___x_2026_ = v___x_2019_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2027_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_head_2016_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
                        v___x_2026_ = v_reuseFailAlloc_2027_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2019_);
                    crate::leanh::lean_dec(v_head_2016_);
                    crate::leanh::lean_dec(v_k_2013_);
                    crate::leanh::lean_dec_ref(v_inst_2012_);
                    return v_tail_2017_;
                }
            }
            2 => {
                return v___x_2026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_eraseKey(
    mut v_00_u03b1_2029_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2030_: *mut crate::leanh::LeanObject,
    mut v_inst_2031_: *mut crate::leanh::LeanObject,
    mut v_k_2032_: *mut crate::leanh::LeanObject,
    mut v_x_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2031_, v_k_2032_, v_x_2033_);
    return v___x_2034_;
}
pub unsafe fn l_Std_Internal_List_insertEntry___redArg(
    mut v_inst_2035_: *mut crate::leanh::LeanObject,
    mut v_k_2036_: *mut crate::leanh::LeanObject,
    mut v_v_2037_: *mut crate::leanh::LeanObject,
    mut v_l_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2039_: u8 = 0;
    crate::leanh::lean_inc(v_l_2038_);
    crate::leanh::lean_inc(v_k_2036_);
    crate::leanh::lean_inc_ref(v_inst_2035_);
    v___x_2039_ = l_Std_Internal_List_containsKey___redArg(v_inst_2035_, v_k_2036_, v_l_2038_);
    if v___x_2039_ == 0 {
        let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2035_);
        v___x_2040_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2040_, 0, v_k_2036_);
        crate::leanh::lean_ctor_set(v___x_2040_, 1, v_v_2037_);
        v___x_2041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2040_);
        crate::leanh::lean_ctor_set(v___x_2041_, 1, v_l_2038_);
        return v___x_2041_;
    } else {
        let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2042_ = l_Std_Internal_List_replaceEntry___redArg(
            v_inst_2035_,
            v_k_2036_,
            v_v_2037_,
            v_l_2038_,
        );
        return v___x_2042_;
    }
}
pub unsafe fn l_Std_Internal_List_insertEntry(
    mut v_00_u03b1_2043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2044_: *mut crate::leanh::LeanObject,
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_k_2046_: *mut crate::leanh::LeanObject,
    mut v_v_2047_: *mut crate::leanh::LeanObject,
    mut v_l_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_Std_Internal_List_insertEntry___redArg(v_inst_2045_, v_k_2046_, v_v_2047_, v_l_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Std_Internal_List_insertEntryIfNew___redArg(
    mut v_inst_2050_: *mut crate::leanh::LeanObject,
    mut v_k_2051_: *mut crate::leanh::LeanObject,
    mut v_v_2052_: *mut crate::leanh::LeanObject,
    mut v_l_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2054_: u8 = 0;
    crate::leanh::lean_inc(v_l_2053_);
    crate::leanh::lean_inc(v_k_2051_);
    v___x_2054_ = l_Std_Internal_List_containsKey___redArg(v_inst_2050_, v_k_2051_, v_l_2053_);
    if v___x_2054_ == 0 {
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2055_, 0, v_k_2051_);
        crate::leanh::lean_ctor_set(v___x_2055_, 1, v_v_2052_);
        v___x_2056_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2055_);
        crate::leanh::lean_ctor_set(v___x_2056_, 1, v_l_2053_);
        return v___x_2056_;
    } else {
        crate::leanh::lean_dec(v_v_2052_);
        crate::leanh::lean_dec(v_k_2051_);
        return v_l_2053_;
    }
}
pub unsafe fn l_Std_Internal_List_insertEntryIfNew(
    mut v_00_u03b1_2057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2058_: *mut crate::leanh::LeanObject,
    mut v_inst_2059_: *mut crate::leanh::LeanObject,
    mut v_k_2060_: *mut crate::leanh::LeanObject,
    mut v_v_2061_: *mut crate::leanh::LeanObject,
    mut v_l_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l_Std_Internal_List_insertEntryIfNew___redArg(
        v_inst_2059_,
        v_k_2060_,
        v_v_2061_,
        v_l_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_2064_: *mut crate::leanh::LeanObject,
    mut v_h__1_2065_: *mut crate::leanh::LeanObject,
    mut v_h__2_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2064_) == 0 {
        let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2066_);
        v___x_2067_ = crate::leanh::lean_box(0);
        v___x_2068_ = crate::leanh::lean_apply_1(v_h__1_2065_, v___x_2067_);
        return v___x_2068_;
    } else {
        let mut v_val_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2065_);
        v_val_2069_ = crate::leanh::lean_ctor_get(v_x_2064_, 0);
        crate::leanh::lean_inc(v_val_2069_);
        crate::leanh::lean_dec_ref_known(v_x_2064_, 1);
        v___x_2070_ = crate::leanh::lean_apply_1(v_h__2_2066_, v_val_2069_);
        return v___x_2070_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_2071_: *mut crate::leanh::LeanObject,
    mut v_motive_2072_: *mut crate::leanh::LeanObject,
    mut v_x_2073_: *mut crate::leanh::LeanObject,
    mut v_h__1_2074_: *mut crate::leanh::LeanObject,
    mut v_h__2_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2073_) == 0 {
        let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2075_);
        v___x_2076_ = crate::leanh::lean_box(0);
        v___x_2077_ = crate::leanh::lean_apply_1(v_h__1_2074_, v___x_2076_);
        return v___x_2077_;
    } else {
        let mut v_val_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2074_);
        v_val_2078_ = crate::leanh::lean_ctor_get(v_x_2073_, 0);
        crate::leanh::lean_inc(v_val_2078_);
        crate::leanh::lean_dec_ref_known(v_x_2073_, 1);
        v___x_2079_ = crate::leanh::lean_apply_1(v_h__2_2075_, v_val_2078_);
        return v___x_2079_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_2080_: *mut crate::leanh::LeanObject,
    mut v_h__1_2081_: *mut crate::leanh::LeanObject,
    mut v_h__2_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2080_) == 0 {
        let mut v_a_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2082_);
        v_a_2083_ = crate::leanh::lean_ctor_get(v_x_2080_, 0);
        crate::leanh::lean_inc(v_a_2083_);
        crate::leanh::lean_dec_ref_known(v_x_2080_, 1);
        v___x_2084_ = crate::leanh::lean_apply_1(v_h__1_2081_, v_a_2083_);
        return v___x_2084_;
    } else {
        let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2081_);
        v_a_2085_ = crate::leanh::lean_ctor_get(v_x_2080_, 0);
        crate::leanh::lean_inc(v_a_2085_);
        crate::leanh::lean_dec_ref_known(v_x_2080_, 1);
        v___x_2086_ = crate::leanh::lean_apply_1(v_h__2_2082_, v_a_2085_);
        return v___x_2086_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_2087_: *mut crate::leanh::LeanObject,
    mut v_motive_2088_: *mut crate::leanh::LeanObject,
    mut v_x_2089_: *mut crate::leanh::LeanObject,
    mut v_h__1_2090_: *mut crate::leanh::LeanObject,
    mut v_h__2_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2089_) == 0 {
        let mut v_a_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2091_);
        v_a_2092_ = crate::leanh::lean_ctor_get(v_x_2089_, 0);
        crate::leanh::lean_inc(v_a_2092_);
        crate::leanh::lean_dec_ref_known(v_x_2089_, 1);
        v___x_2093_ = crate::leanh::lean_apply_1(v_h__1_2090_, v_a_2092_);
        return v___x_2093_;
    } else {
        let mut v_a_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2090_);
        v_a_2094_ = crate::leanh::lean_ctor_get(v_x_2089_, 0);
        crate::leanh::lean_inc(v_a_2094_);
        crate::leanh::lean_dec_ref_known(v_x_2089_, 1);
        v___x_2095_ = crate::leanh::lean_apply_1(v_h__2_2091_, v_a_2094_);
        return v___x_2095_;
    }
}
pub unsafe fn l_Std_Internal_List_insertList___redArg(
    mut v_inst_2096_: *mut crate::leanh::LeanObject,
    mut v_l_2097_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_toInsert_2098_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2096_);
                    return v_l_2097_;
                } else {
                    v_head_2099_ = crate::leanh::lean_ctor_get(v_toInsert_2098_, 0);
                    crate::leanh::lean_inc(v_head_2099_);
                    v_tail_2100_ = crate::leanh::lean_ctor_get(v_toInsert_2098_, 1);
                    crate::leanh::lean_inc(v_tail_2100_);
                    crate::leanh::lean_dec_ref_known(v_toInsert_2098_, 2);
                    v_fst_2101_ = crate::leanh::lean_ctor_get(v_head_2099_, 0);
                    crate::leanh::lean_inc(v_fst_2101_);
                    v_snd_2102_ = crate::leanh::lean_ctor_get(v_head_2099_, 1);
                    crate::leanh::lean_inc(v_snd_2102_);
                    crate::leanh::lean_dec(v_head_2099_);
                    crate::leanh::lean_inc_ref(v_inst_2096_);
                    v___x_2103_ = l_Std_Internal_List_insertEntry___redArg(
                        v_inst_2096_,
                        v_fst_2101_,
                        v_snd_2102_,
                        v_l_2097_,
                    );
                    v_l_2097_ = v___x_2103_;
                    v_toInsert_2098_ = v_tail_2100_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_insertList(
    mut v_00_u03b1_2105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2106_: *mut crate::leanh::LeanObject,
    mut v_inst_2107_: *mut crate::leanh::LeanObject,
    mut v_l_2108_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ =
        l_Std_Internal_List_insertList___redArg(v_inst_2107_, v_l_2108_, v_toInsert_2109_);
    return v___x_2110_;
}
pub unsafe fn l_Std_Internal_List_insertListIfNew___redArg(
    mut v_inst_2111_: *mut crate::leanh::LeanObject,
    mut v_l_2112_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_toInsert_2113_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2111_);
                    return v_l_2112_;
                } else {
                    v_head_2114_ = crate::leanh::lean_ctor_get(v_toInsert_2113_, 0);
                    crate::leanh::lean_inc(v_head_2114_);
                    v_tail_2115_ = crate::leanh::lean_ctor_get(v_toInsert_2113_, 1);
                    crate::leanh::lean_inc(v_tail_2115_);
                    crate::leanh::lean_dec_ref_known(v_toInsert_2113_, 2);
                    v_fst_2116_ = crate::leanh::lean_ctor_get(v_head_2114_, 0);
                    crate::leanh::lean_inc(v_fst_2116_);
                    v_snd_2117_ = crate::leanh::lean_ctor_get(v_head_2114_, 1);
                    crate::leanh::lean_inc(v_snd_2117_);
                    crate::leanh::lean_dec(v_head_2114_);
                    crate::leanh::lean_inc_ref(v_inst_2111_);
                    v___x_2118_ = l_Std_Internal_List_insertEntryIfNew___redArg(
                        v_inst_2111_,
                        v_fst_2116_,
                        v_snd_2117_,
                        v_l_2112_,
                    );
                    v_l_2112_ = v___x_2118_;
                    v_toInsert_2113_ = v_tail_2115_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_insertListIfNew(
    mut v_00_u03b1_2120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2121_: *mut crate::leanh::LeanObject,
    mut v_inst_2122_: *mut crate::leanh::LeanObject,
    mut v_l_2123_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ =
        l_Std_Internal_List_insertListIfNew___redArg(v_inst_2122_, v_l_2123_, v_toInsert_2124_);
    return v___x_2125_;
}
pub unsafe fn l_Std_Internal_List_insertSmallerList___redArg(
    mut v_inst_2126_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_2127_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    v___x_2129_ = l_List_lengthTR___redArg(v_l_u2081_2127_);
    v___x_2130_ = l_List_lengthTR___redArg(v_l_u2082_2128_);
    v___x_2131_ = lean_nat_dec_le(v___x_2129_, v___x_2130_);
    crate::leanh::lean_dec(v___x_2130_);
    crate::leanh::lean_dec(v___x_2129_);
    if v___x_2131_ == 0 {
        let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2132_ =
            l_Std_Internal_List_insertList___redArg(v_inst_2126_, v_l_u2081_2127_, v_l_u2082_2128_);
        return v___x_2132_;
    } else {
        let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2133_ = l_Std_Internal_List_insertListIfNew___redArg(
            v_inst_2126_,
            v_l_u2082_2128_,
            v_l_u2081_2127_,
        );
        return v___x_2133_;
    }
}
pub unsafe fn l_Std_Internal_List_insertSmallerList(
    mut v_00_u03b1_2134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2135_: *mut crate::leanh::LeanObject,
    mut v_inst_2136_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_2137_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = l_Std_Internal_List_insertSmallerList___redArg(
        v_inst_2136_,
        v_l_u2081_2137_,
        v_l_u2082_2138_,
    );
    return v___x_2139_;
}
pub unsafe fn l_Std_Internal_List_Prod_toSigma___redArg(
    mut v_p_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2145_: u8 = 0;
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2141_ = crate::leanh::lean_ctor_get(v_p_2140_, 0);
                v_snd_2142_ = crate::leanh::lean_ctor_get(v_p_2140_, 1);
                v_isSharedCheck_2149_ = (!crate::leanh::lean_is_exclusive(v_p_2140_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2144_ = v_p_2140_;
                    v_isShared_2145_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2142_);
                    crate::leanh::lean_inc(v_fst_2141_);
                    crate::leanh::lean_dec(v_p_2140_);
                    v___x_2144_ = crate::leanh::lean_box(0);
                    v_isShared_2145_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2145_ == 0 {
                    v___x_2147_ = v___x_2144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_fst_2141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_snd_2142_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_Prod_toSigma(
    mut v_00_u03b1_2150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2151_: *mut crate::leanh::LeanObject,
    mut v_p_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_2152_);
    return v___x_2153_;
}
pub unsafe fn l_Std_Internal_List_insertListConst___redArg(
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_l_2156_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2158_ = l_Std_Internal_List_insertListConst___redArg___closed__0;
    v___x_2159_ = crate::leanh::lean_box(0);
    v___x_2160_ = l_List_mapTR_loop___redArg(v___x_2158_, v_toInsert_2157_, v___x_2159_);
    v___x_2161_ = l_Std_Internal_List_insertList___redArg(v_inst_2155_, v_l_2156_, v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_Internal_List_insertListConst(
    mut v_00_u03b1_2162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2163_: *mut crate::leanh::LeanObject,
    mut v_inst_2164_: *mut crate::leanh::LeanObject,
    mut v_l_2165_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2167_ =
        l_Std_Internal_List_insertListConst___redArg(v_inst_2164_, v_l_2165_, v_toInsert_2166_);
    return v___x_2167_;
}
pub unsafe fn l_Std_Internal_List_insertListIfNewUnit___redArg(
    mut v_inst_2168_: *mut crate::leanh::LeanObject,
    mut v_l_2169_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_toInsert_2170_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2168_);
                    return v_l_2169_;
                } else {
                    v_head_2171_ = crate::leanh::lean_ctor_get(v_toInsert_2170_, 0);
                    crate::leanh::lean_inc(v_head_2171_);
                    v_tail_2172_ = crate::leanh::lean_ctor_get(v_toInsert_2170_, 1);
                    crate::leanh::lean_inc(v_tail_2172_);
                    crate::leanh::lean_dec_ref_known(v_toInsert_2170_, 2);
                    v___x_2173_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_inst_2168_);
                    v___x_2174_ = l_Std_Internal_List_insertEntryIfNew___redArg(
                        v_inst_2168_,
                        v_head_2171_,
                        v___x_2173_,
                        v_l_2169_,
                    );
                    v_l_2169_ = v___x_2174_;
                    v_toInsert_2170_ = v_tail_2172_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_insertListIfNewUnit(
    mut v_00_u03b1_2176_: *mut crate::leanh::LeanObject,
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_l_2178_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ =
        l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_2177_, v_l_2178_, v_toInsert_2179_);
    return v___x_2180_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(
    mut v_toInsert_2181_: *mut crate::leanh::LeanObject,
    mut v_h__1_2182_: *mut crate::leanh::LeanObject,
    mut v_h__2_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_toInsert_2181_) == 0 {
        let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2183_);
        v___x_2184_ = crate::leanh::lean_box(0);
        v___x_2185_ = crate::leanh::lean_apply_1(v_h__1_2182_, v___x_2184_);
        return v___x_2185_;
    } else {
        let mut v_head_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2182_);
        v_head_2186_ = crate::leanh::lean_ctor_get(v_toInsert_2181_, 0);
        crate::leanh::lean_inc(v_head_2186_);
        v_tail_2187_ = crate::leanh::lean_ctor_get(v_toInsert_2181_, 1);
        crate::leanh::lean_inc(v_tail_2187_);
        crate::leanh::lean_dec_ref_known(v_toInsert_2181_, 2);
        v___x_2188_ = crate::leanh::lean_apply_2(v_h__2_2183_, v_head_2186_, v_tail_2187_);
        return v___x_2188_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(
    mut v_00_u03b1_2189_: *mut crate::leanh::LeanObject,
    mut v_motive_2190_: *mut crate::leanh::LeanObject,
    mut v_toInsert_2191_: *mut crate::leanh::LeanObject,
    mut v_h__1_2192_: *mut crate::leanh::LeanObject,
    mut v_h__2_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_toInsert_2191_) == 0 {
        let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2193_);
        v___x_2194_ = crate::leanh::lean_box(0);
        v___x_2195_ = crate::leanh::lean_apply_1(v_h__1_2192_, v___x_2194_);
        return v___x_2195_;
    } else {
        let mut v_head_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2192_);
        v_head_2196_ = crate::leanh::lean_ctor_get(v_toInsert_2191_, 0);
        crate::leanh::lean_inc(v_head_2196_);
        v_tail_2197_ = crate::leanh::lean_ctor_get(v_toInsert_2191_, 1);
        crate::leanh::lean_inc(v_tail_2197_);
        crate::leanh::lean_dec_ref_known(v_toInsert_2191_, 2);
        v___x_2198_ = crate::leanh::lean_apply_2(v_h__2_2193_, v_head_2196_, v_tail_2197_);
        return v___x_2198_;
    }
}
pub unsafe fn l_Std_Internal_List_alterKey___redArg(
    mut v_inst_2199_: *mut crate::leanh::LeanObject,
    mut v_k_2200_: *mut crate::leanh::LeanObject,
    mut v_f_2201_: *mut crate::leanh::LeanObject,
    mut v_l_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_l_2202_);
    crate::leanh::lean_inc(v_k_2200_);
    crate::leanh::lean_inc_ref(v_inst_2199_);
    v___x_2203_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_2199_, v_k_2200_, v_l_2202_);
    v___x_2204_ = crate::leanh::lean_apply_1(v_f_2201_, v___x_2203_);
    if crate::leanh::lean_obj_tag(v___x_2204_) == 0 {
        let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2205_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2199_, v_k_2200_, v_l_2202_);
        return v___x_2205_;
    } else {
        let mut v_val_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2206_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
        crate::leanh::lean_inc(v_val_2206_);
        crate::leanh::lean_dec_ref_known(v___x_2204_, 1);
        v___x_2207_ = l_Std_Internal_List_insertEntry___redArg(
            v_inst_2199_,
            v_k_2200_,
            v_val_2206_,
            v_l_2202_,
        );
        return v___x_2207_;
    }
}
pub unsafe fn l_Std_Internal_List_alterKey(
    mut v_00_u03b1_2208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2209_: *mut crate::leanh::LeanObject,
    mut v_inst_2210_: *mut crate::leanh::LeanObject,
    mut v_inst_2211_: *mut crate::leanh::LeanObject,
    mut v_k_2212_: *mut crate::leanh::LeanObject,
    mut v_f_2213_: *mut crate::leanh::LeanObject,
    mut v_l_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2215_ =
        l_Std_Internal_List_alterKey___redArg(v_inst_2210_, v_k_2212_, v_f_2213_, v_l_2214_);
    return v___x_2215_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(
    mut v_x_2216_: *mut crate::leanh::LeanObject,
    mut v_h__1_2217_: *mut crate::leanh::LeanObject,
    mut v_h__2_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2216_) == 0 {
        let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2218_);
        v___x_2219_ = crate::leanh::lean_box(0);
        v___x_2220_ = crate::leanh::lean_apply_1(v_h__1_2217_, v___x_2219_);
        return v___x_2220_;
    } else {
        let mut v_val_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2217_);
        v_val_2221_ = crate::leanh::lean_ctor_get(v_x_2216_, 0);
        crate::leanh::lean_inc(v_val_2221_);
        crate::leanh::lean_dec_ref_known(v_x_2216_, 1);
        v___x_2222_ = crate::leanh::lean_apply_1(v_h__2_2218_, v_val_2221_);
        return v___x_2222_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(
    mut v_00_u03b1_2223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2224_: *mut crate::leanh::LeanObject,
    mut v_k_2225_: *mut crate::leanh::LeanObject,
    mut v_motive_2226_: *mut crate::leanh::LeanObject,
    mut v_x_2227_: *mut crate::leanh::LeanObject,
    mut v_h__1_2228_: *mut crate::leanh::LeanObject,
    mut v_h__2_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2227_) == 0 {
        let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2229_);
        v___x_2230_ = crate::leanh::lean_box(0);
        v___x_2231_ = crate::leanh::lean_apply_1(v_h__1_2228_, v___x_2230_);
        return v___x_2231_;
    } else {
        let mut v_val_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2228_);
        v_val_2232_ = crate::leanh::lean_ctor_get(v_x_2227_, 0);
        crate::leanh::lean_inc(v_val_2232_);
        crate::leanh::lean_dec_ref_known(v_x_2227_, 1);
        v___x_2233_ = crate::leanh::lean_apply_1(v_h__2_2229_, v_val_2232_);
        return v___x_2233_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(
    mut v_00_u03b1_2234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2235_: *mut crate::leanh::LeanObject,
    mut v_k_2236_: *mut crate::leanh::LeanObject,
    mut v_motive_2237_: *mut crate::leanh::LeanObject,
    mut v_x_2238_: *mut crate::leanh::LeanObject,
    mut v_h__1_2239_: *mut crate::leanh::LeanObject,
    mut v_h__2_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2241_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_2234_, v_00_u03b2_2235_, v_k_2236_, v_motive_2237_, v_x_2238_, v_h__1_2239_, v_h__2_2240_);
    crate::leanh::lean_dec(v_k_2236_);
    return v_res_2241_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_2242_: *mut crate::leanh::LeanObject,
    mut v_h__1_2243_: *mut crate::leanh::LeanObject,
    mut v_h__2_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2242_) == 0 {
        let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2244_);
        v___x_2245_ = crate::leanh::lean_box(0);
        v___x_2246_ = crate::leanh::lean_apply_1(v_h__1_2243_, v___x_2245_);
        return v___x_2246_;
    } else {
        let mut v_val_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2243_);
        v_val_2247_ = crate::leanh::lean_ctor_get(v_x_2242_, 0);
        crate::leanh::lean_inc(v_val_2247_);
        crate::leanh::lean_dec_ref_known(v_x_2242_, 1);
        v___x_2248_ = crate::leanh::lean_apply_1(v_h__2_2244_, v_val_2247_);
        return v___x_2248_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_2249_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2250_: *mut crate::leanh::LeanObject,
    mut v_k_2251_: *mut crate::leanh::LeanObject,
    mut v_motive_2252_: *mut crate::leanh::LeanObject,
    mut v_x_2253_: *mut crate::leanh::LeanObject,
    mut v_h__1_2254_: *mut crate::leanh::LeanObject,
    mut v_h__2_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2253_) == 0 {
        let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2255_);
        v___x_2256_ = crate::leanh::lean_box(0);
        v___x_2257_ = crate::leanh::lean_apply_1(v_h__1_2254_, v___x_2256_);
        return v___x_2257_;
    } else {
        let mut v_val_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2254_);
        v_val_2258_ = crate::leanh::lean_ctor_get(v_x_2253_, 0);
        crate::leanh::lean_inc(v_val_2258_);
        crate::leanh::lean_dec_ref_known(v_x_2253_, 1);
        v___x_2259_ = crate::leanh::lean_apply_1(v_h__2_2255_, v_val_2258_);
        return v___x_2259_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_2260_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2261_: *mut crate::leanh::LeanObject,
    mut v_k_2262_: *mut crate::leanh::LeanObject,
    mut v_motive_2263_: *mut crate::leanh::LeanObject,
    mut v_x_2264_: *mut crate::leanh::LeanObject,
    mut v_h__1_2265_: *mut crate::leanh::LeanObject,
    mut v_h__2_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_2260_, v_00_u03b2_2261_, v_k_2262_, v_motive_2263_, v_x_2264_, v_h__1_2265_, v_h__2_2266_);
    crate::leanh::lean_dec(v_k_2262_);
    return v_res_2267_;
}
pub unsafe fn l_Std_Internal_List_Const_alterKey___redArg(
    mut v_inst_2268_: *mut crate::leanh::LeanObject,
    mut v_k_2269_: *mut crate::leanh::LeanObject,
    mut v_f_2270_: *mut crate::leanh::LeanObject,
    mut v_l_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_l_2271_);
    crate::leanh::lean_inc(v_k_2269_);
    crate::leanh::lean_inc_ref(v_inst_2268_);
    v___x_2272_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_2268_, v_k_2269_, v_l_2271_);
    v___x_2273_ = crate::leanh::lean_apply_1(v_f_2270_, v___x_2272_);
    if crate::leanh::lean_obj_tag(v___x_2273_) == 0 {
        let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2274_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2268_, v_k_2269_, v_l_2271_);
        return v___x_2274_;
    } else {
        let mut v_val_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2275_ = crate::leanh::lean_ctor_get(v___x_2273_, 0);
        crate::leanh::lean_inc(v_val_2275_);
        crate::leanh::lean_dec_ref_known(v___x_2273_, 1);
        v___x_2276_ = l_Std_Internal_List_insertEntry___redArg(
            v_inst_2268_,
            v_k_2269_,
            v_val_2275_,
            v_l_2271_,
        );
        return v___x_2276_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_alterKey(
    mut v_00_u03b1_2277_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2278_: *mut crate::leanh::LeanObject,
    mut v_inst_2279_: *mut crate::leanh::LeanObject,
    mut v_k_2280_: *mut crate::leanh::LeanObject,
    mut v_f_2281_: *mut crate::leanh::LeanObject,
    mut v_l_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ =
        l_Std_Internal_List_Const_alterKey___redArg(v_inst_2279_, v_k_2280_, v_f_2281_, v_l_2282_);
    return v___x_2283_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(
    mut v_x_2284_: *mut crate::leanh::LeanObject,
    mut v_h__1_2285_: *mut crate::leanh::LeanObject,
    mut v_h__2_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2284_) == 0 {
        let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2286_);
        v___x_2287_ = crate::leanh::lean_box(0);
        v___x_2288_ = crate::leanh::lean_apply_1(v_h__1_2285_, v___x_2287_);
        return v___x_2288_;
    } else {
        let mut v_val_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2285_);
        v_val_2289_ = crate::leanh::lean_ctor_get(v_x_2284_, 0);
        crate::leanh::lean_inc(v_val_2289_);
        crate::leanh::lean_dec_ref_known(v_x_2284_, 1);
        v___x_2290_ = crate::leanh::lean_apply_1(v_h__2_2286_, v_val_2289_);
        return v___x_2290_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(
    mut v_00_u03b2_2291_: *mut crate::leanh::LeanObject,
    mut v_motive_2292_: *mut crate::leanh::LeanObject,
    mut v_x_2293_: *mut crate::leanh::LeanObject,
    mut v_h__1_2294_: *mut crate::leanh::LeanObject,
    mut v_h__2_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2293_) == 0 {
        let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2295_);
        v___x_2296_ = crate::leanh::lean_box(0);
        v___x_2297_ = crate::leanh::lean_apply_1(v_h__1_2294_, v___x_2296_);
        return v___x_2297_;
    } else {
        let mut v_val_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2294_);
        v_val_2298_ = crate::leanh::lean_ctor_get(v_x_2293_, 0);
        crate::leanh::lean_inc(v_val_2298_);
        crate::leanh::lean_dec_ref_known(v_x_2293_, 1);
        v___x_2299_ = crate::leanh::lean_apply_1(v_h__2_2295_, v_val_2298_);
        return v___x_2299_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_2300_: *mut crate::leanh::LeanObject,
    mut v_h__1_2301_: *mut crate::leanh::LeanObject,
    mut v_h__2_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2300_) == 0 {
        let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2302_);
        v___x_2303_ = crate::leanh::lean_box(0);
        v___x_2304_ = crate::leanh::lean_apply_1(v_h__1_2301_, v___x_2303_);
        return v___x_2304_;
    } else {
        let mut v_val_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2301_);
        v_val_2305_ = crate::leanh::lean_ctor_get(v_x_2300_, 0);
        crate::leanh::lean_inc(v_val_2305_);
        crate::leanh::lean_dec_ref_known(v_x_2300_, 1);
        v___x_2306_ = crate::leanh::lean_apply_1(v_h__2_2302_, v_val_2305_);
        return v___x_2306_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b2_2307_: *mut crate::leanh::LeanObject,
    mut v_motive_2308_: *mut crate::leanh::LeanObject,
    mut v_x_2309_: *mut crate::leanh::LeanObject,
    mut v_h__1_2310_: *mut crate::leanh::LeanObject,
    mut v_h__2_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2309_) == 0 {
        let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2311_);
        v___x_2312_ = crate::leanh::lean_box(0);
        v___x_2313_ = crate::leanh::lean_apply_1(v_h__1_2310_, v___x_2312_);
        return v___x_2313_;
    } else {
        let mut v_val_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2310_);
        v_val_2314_ = crate::leanh::lean_ctor_get(v_x_2309_, 0);
        crate::leanh::lean_inc(v_val_2314_);
        crate::leanh::lean_dec_ref_known(v_x_2309_, 1);
        v___x_2315_ = crate::leanh::lean_apply_1(v_h__2_2311_, v_val_2314_);
        return v___x_2315_;
    }
}
pub unsafe fn l_Std_Internal_List_modifyKey___redArg(
    mut v_inst_2316_: *mut crate::leanh::LeanObject,
    mut v_k_2317_: *mut crate::leanh::LeanObject,
    mut v_f_2318_: *mut crate::leanh::LeanObject,
    mut v_l_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_l_2319_);
    crate::leanh::lean_inc(v_k_2317_);
    crate::leanh::lean_inc_ref(v_inst_2316_);
    v___x_2320_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_2316_, v_k_2317_, v_l_2319_);
    if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
        crate::leanh::lean_dec(v_f_2318_);
        crate::leanh::lean_dec(v_k_2317_);
        crate::leanh::lean_dec_ref(v_inst_2316_);
        return v_l_2319_;
    } else {
        let mut v_val_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2321_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
        crate::leanh::lean_inc(v_val_2321_);
        crate::leanh::lean_dec_ref_known(v___x_2320_, 1);
        v___x_2322_ = crate::leanh::lean_apply_1(v_f_2318_, v_val_2321_);
        v___x_2323_ = l_Std_Internal_List_replaceEntry___redArg(
            v_inst_2316_,
            v_k_2317_,
            v___x_2322_,
            v_l_2319_,
        );
        return v___x_2323_;
    }
}
pub unsafe fn l_Std_Internal_List_modifyKey(
    mut v_00_u03b1_2324_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2325_: *mut crate::leanh::LeanObject,
    mut v_inst_2326_: *mut crate::leanh::LeanObject,
    mut v_inst_2327_: *mut crate::leanh::LeanObject,
    mut v_k_2328_: *mut crate::leanh::LeanObject,
    mut v_f_2329_: *mut crate::leanh::LeanObject,
    mut v_l_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ =
        l_Std_Internal_List_modifyKey___redArg(v_inst_2326_, v_k_2328_, v_f_2329_, v_l_2330_);
    return v___x_2331_;
}
pub unsafe fn l_Std_Internal_List_Const_modifyKey___redArg(
    mut v_inst_2332_: *mut crate::leanh::LeanObject,
    mut v_k_2333_: *mut crate::leanh::LeanObject,
    mut v_f_2334_: *mut crate::leanh::LeanObject,
    mut v_l_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_l_2335_);
    crate::leanh::lean_inc(v_k_2333_);
    crate::leanh::lean_inc_ref(v_inst_2332_);
    v___x_2336_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_2332_, v_k_2333_, v_l_2335_);
    if crate::leanh::lean_obj_tag(v___x_2336_) == 0 {
        crate::leanh::lean_dec(v_f_2334_);
        crate::leanh::lean_dec(v_k_2333_);
        crate::leanh::lean_dec_ref(v_inst_2332_);
        return v_l_2335_;
    } else {
        let mut v_val_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2337_ = crate::leanh::lean_ctor_get(v___x_2336_, 0);
        crate::leanh::lean_inc(v_val_2337_);
        crate::leanh::lean_dec_ref_known(v___x_2336_, 1);
        v___x_2338_ = crate::leanh::lean_apply_1(v_f_2334_, v_val_2337_);
        v___x_2339_ = l_Std_Internal_List_replaceEntry___redArg(
            v_inst_2332_,
            v_k_2333_,
            v___x_2338_,
            v_l_2335_,
        );
        return v___x_2339_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_modifyKey(
    mut v_00_u03b1_2340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
    mut v_k_2343_: *mut crate::leanh::LeanObject,
    mut v_f_2344_: *mut crate::leanh::LeanObject,
    mut v_l_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l_Std_Internal_List_Const_modifyKey___redArg(v_inst_2342_, v_k_2343_, v_f_2344_, v_l_2345_);
    return v___x_2346_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_2347_: *mut crate::leanh::LeanObject,
    mut v_h__1_2348_: *mut crate::leanh::LeanObject,
    mut v_h__2_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2347_) == 0 {
        let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2348_);
        v___x_2350_ = crate::leanh::lean_box(0);
        v___x_2351_ = crate::leanh::lean_apply_1(v_h__2_2349_, v___x_2350_);
        return v___x_2351_;
    } else {
        let mut v_val_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2349_);
        v_val_2352_ = crate::leanh::lean_ctor_get(v_x_2347_, 0);
        crate::leanh::lean_inc(v_val_2352_);
        crate::leanh::lean_dec_ref_known(v_x_2347_, 1);
        v___x_2353_ = crate::leanh::lean_apply_1(v_h__1_2348_, v_val_2352_);
        return v___x_2353_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_2354_: *mut crate::leanh::LeanObject,
    mut v_motive_2355_: *mut crate::leanh::LeanObject,
    mut v_x_2356_: *mut crate::leanh::LeanObject,
    mut v_h__1_2357_: *mut crate::leanh::LeanObject,
    mut v_h__2_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2356_) == 0 {
        let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2357_);
        v___x_2359_ = crate::leanh::lean_box(0);
        v___x_2360_ = crate::leanh::lean_apply_1(v_h__2_2358_, v___x_2359_);
        return v___x_2360_;
    } else {
        let mut v_val_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2358_);
        v_val_2361_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
        crate::leanh::lean_inc(v_val_2361_);
        crate::leanh::lean_dec_ref_known(v_x_2356_, 1);
        v___x_2362_ = crate::leanh::lean_apply_1(v_h__1_2357_, v_val_2361_);
        return v___x_2362_;
    }
}
pub unsafe fn l_Std_Internal_List_eraseList___redArg(
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v_l_2364_: *mut crate::leanh::LeanObject,
    mut v_toErase_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_toErase_2365_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2363_);
                    return v_l_2364_;
                } else {
                    v_head_2366_ = crate::leanh::lean_ctor_get(v_toErase_2365_, 0);
                    crate::leanh::lean_inc(v_head_2366_);
                    v_tail_2367_ = crate::leanh::lean_ctor_get(v_toErase_2365_, 1);
                    crate::leanh::lean_inc(v_tail_2367_);
                    crate::leanh::lean_dec_ref_known(v_toErase_2365_, 2);
                    crate::leanh::lean_inc_ref(v_inst_2363_);
                    v___x_2368_ = l_Std_Internal_List_eraseKey___redArg(
                        v_inst_2363_,
                        v_head_2366_,
                        v_l_2364_,
                    );
                    v_l_2364_ = v___x_2368_;
                    v_toErase_2365_ = v_tail_2367_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_eraseList(
    mut v_00_u03b1_2370_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2371_: *mut crate::leanh::LeanObject,
    mut v_inst_2372_: *mut crate::leanh::LeanObject,
    mut v_l_2373_: *mut crate::leanh::LeanObject,
    mut v_toErase_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = l_Std_Internal_List_eraseList___redArg(v_inst_2372_, v_l_2373_, v_toErase_2374_);
    return v___x_2375_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(
    mut v_opt_2376_: *mut crate::leanh::LeanObject,
    mut v_h__1_2377_: *mut crate::leanh::LeanObject,
    mut v_h__2_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_opt_2376_) == 0 {
        let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2377_);
        v___x_2379_ = crate::leanh::lean_box(0);
        v___x_2380_ = crate::leanh::lean_apply_1(v_h__2_2378_, v___x_2379_);
        return v___x_2380_;
    } else {
        let mut v_val_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2378_);
        v_val_2381_ = crate::leanh::lean_ctor_get(v_opt_2376_, 0);
        crate::leanh::lean_inc(v_val_2381_);
        crate::leanh::lean_dec_ref_known(v_opt_2376_, 1);
        v___x_2382_ = crate::leanh::lean_apply_1(v_h__1_2377_, v_val_2381_);
        return v___x_2382_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(
    mut v_00_u03b1_2383_: *mut crate::leanh::LeanObject,
    mut v_motive_2384_: *mut crate::leanh::LeanObject,
    mut v_opt_2385_: *mut crate::leanh::LeanObject,
    mut v_h__1_2386_: *mut crate::leanh::LeanObject,
    mut v_h__2_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_opt_2385_) == 0 {
        let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2386_);
        v___x_2388_ = crate::leanh::lean_box(0);
        v___x_2389_ = crate::leanh::lean_apply_1(v_h__2_2387_, v___x_2388_);
        return v___x_2389_;
    } else {
        let mut v_val_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2387_);
        v_val_2390_ = crate::leanh::lean_ctor_get(v_opt_2385_, 0);
        crate::leanh::lean_inc(v_val_2390_);
        crate::leanh::lean_dec_ref_known(v_opt_2385_, 1);
        v___x_2391_ = crate::leanh::lean_apply_1(v_h__1_2386_, v_val_2390_);
        return v___x_2391_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(
    mut v_00_u03b1_2392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2393_: *mut crate::leanh::LeanObject,
    mut v_inst_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = crate::leanh::lean_box(0);
    return v___x_2395_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(
    mut v_00_u03b1_2396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2397_: *mut crate::leanh::LeanObject,
    mut v_inst_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(
        v_00_u03b1_2396_,
        v_00_u03b2_2397_,
        v_inst_2398_,
    );
    crate::leanh::lean_dec_ref(v_inst_2398_);
    return v_res_2399_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(
    mut v_inst_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_b_2402_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v_fst_2403_ = crate::leanh::lean_ctor_get(v_a_2401_, 0);
    crate::leanh::lean_inc(v_fst_2403_);
    crate::leanh::lean_dec_ref(v_a_2401_);
    v_fst_2404_ = crate::leanh::lean_ctor_get(v_b_2402_, 0);
    crate::leanh::lean_inc(v_fst_2404_);
    crate::leanh::lean_dec_ref(v_b_2402_);
    v___x_2405_ = crate::leanh::lean_apply_2(v_inst_2400_, v_fst_2403_, v_fst_2404_);
    v___x_2406_ = (crate::leanh::lean_unbox(v___x_2405_) as u8);
    if v___x_2406_ == 2 {
        let mut v___x_2407_: u8 = 0;
        v___x_2407_ = 0;
        return v___x_2407_;
    } else {
        let mut v___x_2408_: u8 = 0;
        v___x_2408_ = 1;
        return v___x_2408_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(
    mut v_inst_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_b_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: u8 = 0;
    let mut v_r_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_2409_, v_a_2410_, v_b_2411_);
    v_r_2413_ = crate::leanh::lean_box((v_res_2412_) as usize);
    return v_r_2413_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(
    mut v_00_u03b1_2414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2415_: *mut crate::leanh::LeanObject,
    mut v_inst_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_b_2418_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2419_: u8 = 0;
    v___x_2419_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_2416_, v_a_2417_, v_b_2418_);
    return v___x_2419_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(
    mut v_00_u03b1_2420_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2421_: *mut crate::leanh::LeanObject,
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_b_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2425_: u8 = 0;
    let mut v_r_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_2420_, v_00_u03b2_2421_, v_inst_2422_, v_a_2423_, v_b_2424_);
    v_r_2426_ = crate::leanh::lean_box((v_res_2425_) as usize);
    return v_r_2426_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(
    mut v_inst_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_b_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: u8 = 0;
    v_fst_2430_ = crate::leanh::lean_ctor_get(v_a_2428_, 0);
    v_fst_2431_ = crate::leanh::lean_ctor_get(v_b_2429_, 0);
    crate::leanh::lean_inc(v_fst_2431_);
    crate::leanh::lean_inc(v_fst_2430_);
    v___x_2432_ = crate::leanh::lean_apply_2(v_inst_2427_, v_fst_2430_, v_fst_2431_);
    v___x_2433_ = (crate::leanh::lean_unbox(v___x_2432_) as u8);
    if v___x_2433_ == 2 {
        crate::leanh::lean_dec_ref(v_a_2428_);
        return v_b_2429_;
    } else {
        crate::leanh::lean_dec_ref(v_b_2429_);
        return v_a_2428_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(
    mut v_inst_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2435_ = crate::leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___f_2435_, 0, v_inst_2434_);
    return v___f_2435_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(
    mut v_00_u03b1_2436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2437_: *mut crate::leanh::LeanObject,
    mut v_inst_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2439_ = crate::leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___f_2439_, 0, v_inst_2438_);
    return v___f_2439_;
}
pub unsafe fn l_Std_Internal_List_minEntry_x3f___redArg(
    mut v_inst_2440_: *mut crate::leanh::LeanObject,
    mut v_xs_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2442_ = crate::leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___f_2442_, 0, v_inst_2440_);
    v___x_2443_ = l_List_min_x3f___redArg(v___f_2442_, v_xs_2441_);
    return v___x_2443_;
}
pub unsafe fn l_Std_Internal_List_minEntry_x3f(
    mut v_00_u03b1_2444_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2445_: *mut crate::leanh::LeanObject,
    mut v_inst_2446_: *mut crate::leanh::LeanObject,
    mut v_xs_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_2446_, v_xs_2447_);
    return v___x_2448_;
}
pub unsafe fn l_Std_Internal_List_minKey_x3f___redArg(
    mut v_inst_2449_: *mut crate::leanh::LeanObject,
    mut v_xs_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v_fst_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2451_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_2449_, v_xs_2450_);
                if crate::leanh::lean_obj_tag(v___x_2451_) == 0 {
                    v___x_2452_ = crate::leanh::lean_box(0);
                    return v___x_2452_;
                } else {
                    v_val_2453_ = crate::leanh::lean_ctor_get(v___x_2451_, 0);
                    v_isSharedCheck_2461_ = (!crate::leanh::lean_is_exclusive(v___x_2451_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v___x_2455_ = v___x_2451_;
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2453_);
                        crate::leanh::lean_dec(v___x_2451_);
                        v___x_2455_ = crate::leanh::lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2457_ = crate::leanh::lean_ctor_get(v_val_2453_, 0);
                crate::leanh::lean_inc(v_fst_2457_);
                crate::leanh::lean_dec(v_val_2453_);
                if v_isShared_2456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2455_, 0, v_fst_2457_);
                    v___x_2459_ = v___x_2455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2457_);
                    v___x_2459_ = v_reuseFailAlloc_2460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_minKey_x3f(
    mut v_00_u03b1_2462_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2463_: *mut crate::leanh::LeanObject,
    mut v_inst_2464_: *mut crate::leanh::LeanObject,
    mut v_xs_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2464_, v_xs_2465_);
    return v___x_2466_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(
    mut v_x_2467_: *mut crate::leanh::LeanObject,
    mut v_h__1_2468_: *mut crate::leanh::LeanObject,
    mut v_h__2_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2467_) == 0 {
        let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2469_);
        v___x_2470_ = crate::leanh::lean_box(0);
        v___x_2471_ = crate::leanh::lean_apply_1(v_h__1_2468_, v___x_2470_);
        return v___x_2471_;
    } else {
        let mut v_val_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2468_);
        v_val_2472_ = crate::leanh::lean_ctor_get(v_x_2467_, 0);
        crate::leanh::lean_inc(v_val_2472_);
        crate::leanh::lean_dec_ref_known(v_x_2467_, 1);
        v___x_2473_ = crate::leanh::lean_apply_1(v_h__2_2469_, v_val_2472_);
        return v___x_2473_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(
    mut v_00_u03b1_2474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2475_: *mut crate::leanh::LeanObject,
    mut v_motive_2476_: *mut crate::leanh::LeanObject,
    mut v_x_2477_: *mut crate::leanh::LeanObject,
    mut v_h__1_2478_: *mut crate::leanh::LeanObject,
    mut v_h__2_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2477_) == 0 {
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2479_);
        v___x_2480_ = crate::leanh::lean_box(0);
        v___x_2481_ = crate::leanh::lean_apply_1(v_h__1_2478_, v___x_2480_);
        return v___x_2481_;
    } else {
        let mut v_val_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2478_);
        v_val_2482_ = crate::leanh::lean_ctor_get(v_x_2477_, 0);
        crate::leanh::lean_inc(v_val_2482_);
        crate::leanh::lean_dec_ref_known(v_x_2477_, 1);
        v___x_2483_ = crate::leanh::lean_apply_1(v_h__2_2479_, v_val_2482_);
        return v___x_2483_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_2484_: *mut crate::leanh::LeanObject,
    mut v_h__1_2485_: *mut crate::leanh::LeanObject,
    mut v_h__2_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2484_) == 0 {
        let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2486_);
        v___x_2487_ = crate::leanh::lean_box(0);
        v___x_2488_ = crate::leanh::lean_apply_1(v_h__1_2485_, v___x_2487_);
        return v___x_2488_;
    } else {
        let mut v_head_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2485_);
        v_head_2489_ = crate::leanh::lean_ctor_get(v_x_2484_, 0);
        crate::leanh::lean_inc(v_head_2489_);
        v_tail_2490_ = crate::leanh::lean_ctor_get(v_x_2484_, 1);
        crate::leanh::lean_inc(v_tail_2490_);
        crate::leanh::lean_dec_ref_known(v_x_2484_, 2);
        v___x_2491_ = crate::leanh::lean_apply_2(v_h__2_2486_, v_head_2489_, v_tail_2490_);
        return v___x_2491_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_2492_: *mut crate::leanh::LeanObject,
    mut v_motive_2493_: *mut crate::leanh::LeanObject,
    mut v_x_2494_: *mut crate::leanh::LeanObject,
    mut v_h__1_2495_: *mut crate::leanh::LeanObject,
    mut v_h__2_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2494_) == 0 {
        let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2496_);
        v___x_2497_ = crate::leanh::lean_box(0);
        v___x_2498_ = crate::leanh::lean_apply_1(v_h__1_2495_, v___x_2497_);
        return v___x_2498_;
    } else {
        let mut v_head_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2495_);
        v_head_2499_ = crate::leanh::lean_ctor_get(v_x_2494_, 0);
        crate::leanh::lean_inc(v_head_2499_);
        v_tail_2500_ = crate::leanh::lean_ctor_get(v_x_2494_, 1);
        crate::leanh::lean_inc(v_tail_2500_);
        crate::leanh::lean_dec_ref_known(v_x_2494_, 2);
        v___x_2501_ = crate::leanh::lean_apply_2(v_h__2_2496_, v_head_2499_, v_tail_2500_);
        return v___x_2501_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(
    mut v_x_2502_: *mut crate::leanh::LeanObject,
    mut v_h__1_2503_: *mut crate::leanh::LeanObject,
    mut v_h__2_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2502_) == 0 {
        let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2504_);
        v___x_2505_ = crate::leanh::lean_box(0);
        v___x_2506_ = crate::leanh::lean_apply_1(v_h__1_2503_, v___x_2505_);
        return v___x_2506_;
    } else {
        let mut v_val_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2503_);
        v_val_2507_ = crate::leanh::lean_ctor_get(v_x_2502_, 0);
        crate::leanh::lean_inc(v_val_2507_);
        crate::leanh::lean_dec_ref_known(v_x_2502_, 1);
        v___x_2508_ = crate::leanh::lean_apply_1(v_h__2_2504_, v_val_2507_);
        return v___x_2508_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(
    mut v_00_u03b1_2509_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2510_: *mut crate::leanh::LeanObject,
    mut v_motive_2511_: *mut crate::leanh::LeanObject,
    mut v_x_2512_: *mut crate::leanh::LeanObject,
    mut v_h__1_2513_: *mut crate::leanh::LeanObject,
    mut v_h__2_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2512_) == 0 {
        let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2514_);
        v___x_2515_ = crate::leanh::lean_box(0);
        v___x_2516_ = crate::leanh::lean_apply_1(v_h__1_2513_, v___x_2515_);
        return v___x_2516_;
    } else {
        let mut v_val_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2513_);
        v_val_2517_ = crate::leanh::lean_ctor_get(v_x_2512_, 0);
        crate::leanh::lean_inc(v_val_2517_);
        crate::leanh::lean_dec_ref_known(v_x_2512_, 1);
        v___x_2518_ = crate::leanh::lean_apply_1(v_h__2_2514_, v_val_2517_);
        return v___x_2518_;
    }
}
pub unsafe fn l_Std_Internal_List_minKey___redArg(
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_xs_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2519_, v_xs_2520_);
    v_val_2522_ = crate::leanh::lean_ctor_get(v___x_2521_, 0);
    crate::leanh::lean_inc(v_val_2522_);
    crate::leanh::lean_dec(v___x_2521_);
    return v_val_2522_;
}
pub unsafe fn l_Std_Internal_List_minKey(
    mut v_00_u03b1_2523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2524_: *mut crate::leanh::LeanObject,
    mut v_inst_2525_: *mut crate::leanh::LeanObject,
    mut v_xs_2526_: *mut crate::leanh::LeanObject,
    mut v_h_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ = l_Std_Internal_List_minKey___redArg(v_inst_2525_, v_xs_2526_);
    return v___x_2528_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21___redArg(
    mut v_inst_2529_: *mut crate::leanh::LeanObject,
    mut v_inst_2530_: *mut crate::leanh::LeanObject,
    mut v_xs_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2529_, v_xs_2531_);
    if crate::leanh::lean_obj_tag(v___x_2532_) == 0 {
        let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2533_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_2534_ = l_panic___redArg(v_inst_2530_, v___x_2533_);
        return v___x_2534_;
    } else {
        let mut v_val_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2535_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
        crate::leanh::lean_inc(v_val_2535_);
        crate::leanh::lean_dec_ref_known(v___x_2532_, 1);
        return v_val_2535_;
    }
}
pub unsafe fn l_Std_Internal_List_minKey_x21___redArg___boxed(
    mut v_inst_2536_: *mut crate::leanh::LeanObject,
    mut v_inst_2537_: *mut crate::leanh::LeanObject,
    mut v_xs_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_2536_, v_inst_2537_, v_xs_2538_);
    crate::leanh::lean_dec(v_inst_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21(
    mut v_00_u03b1_2540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2541_: *mut crate::leanh::LeanObject,
    mut v_inst_2542_: *mut crate::leanh::LeanObject,
    mut v_inst_2543_: *mut crate::leanh::LeanObject,
    mut v_xs_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_2542_, v_inst_2543_, v_xs_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21___boxed(
    mut v_00_u03b1_2546_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2547_: *mut crate::leanh::LeanObject,
    mut v_inst_2548_: *mut crate::leanh::LeanObject,
    mut v_inst_2549_: *mut crate::leanh::LeanObject,
    mut v_xs_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_Internal_List_minKey_x21(
        v_00_u03b1_2546_,
        v_00_u03b2_2547_,
        v_inst_2548_,
        v_inst_2549_,
        v_xs_2550_,
    );
    crate::leanh::lean_dec(v_inst_2549_);
    return v_res_2551_;
}
pub unsafe fn l_Std_Internal_List_minKeyD___redArg(
    mut v_inst_2552_: *mut crate::leanh::LeanObject,
    mut v_xs_2553_: *mut crate::leanh::LeanObject,
    mut v_fallback_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2552_, v_xs_2553_);
    if crate::leanh::lean_obj_tag(v___x_2555_) == 0 {
        crate::leanh::lean_inc(v_fallback_2554_);
        return v_fallback_2554_;
    } else {
        let mut v_val_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2556_ = crate::leanh::lean_ctor_get(v___x_2555_, 0);
        crate::leanh::lean_inc(v_val_2556_);
        crate::leanh::lean_dec_ref_known(v___x_2555_, 1);
        return v_val_2556_;
    }
}
pub unsafe fn l_Std_Internal_List_minKeyD___redArg___boxed(
    mut v_inst_2557_: *mut crate::leanh::LeanObject,
    mut v_xs_2558_: *mut crate::leanh::LeanObject,
    mut v_fallback_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Std_Internal_List_minKeyD___redArg(v_inst_2557_, v_xs_2558_, v_fallback_2559_);
    crate::leanh::lean_dec(v_fallback_2559_);
    return v_res_2560_;
}
pub unsafe fn l_Std_Internal_List_minKeyD(
    mut v_00_u03b1_2561_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2562_: *mut crate::leanh::LeanObject,
    mut v_inst_2563_: *mut crate::leanh::LeanObject,
    mut v_xs_2564_: *mut crate::leanh::LeanObject,
    mut v_fallback_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Std_Internal_List_minKeyD___redArg(v_inst_2563_, v_xs_2564_, v_fallback_2565_);
    return v___x_2566_;
}
pub unsafe fn l_Std_Internal_List_minKeyD___boxed(
    mut v_00_u03b1_2567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2568_: *mut crate::leanh::LeanObject,
    mut v_inst_2569_: *mut crate::leanh::LeanObject,
    mut v_xs_2570_: *mut crate::leanh::LeanObject,
    mut v_fallback_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_Internal_List_minKeyD(
        v_00_u03b1_2567_,
        v_00_u03b2_2568_,
        v_inst_2569_,
        v_xs_2570_,
        v_fallback_2571_,
    );
    crate::leanh::lean_dec(v_fallback_2571_);
    return v_res_2572_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x3f___redArg(
    mut v_inst_2573_: *mut crate::leanh::LeanObject,
    mut v_xs_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2575_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2575_, 0, v_inst_2573_);
    v___x_2576_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2575_, v_xs_2574_);
    return v___x_2576_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x3f(
    mut v_00_u03b1_2577_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2578_: *mut crate::leanh::LeanObject,
    mut v_inst_2579_: *mut crate::leanh::LeanObject,
    mut v_xs_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2581_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2581_, 0, v_inst_2579_);
    v___x_2582_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2581_, v_xs_2580_);
    return v___x_2582_;
}
pub unsafe fn l_Std_Internal_List_maxKey___redArg(
    mut v_inst_2583_: *mut crate::leanh::LeanObject,
    mut v_xs_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2585_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2585_, 0, v_inst_2583_);
    v___x_2586_ = l_Std_Internal_List_minKey___redArg(v___f_2585_, v_xs_2584_);
    return v___x_2586_;
}
pub unsafe fn l_Std_Internal_List_maxKey(
    mut v_00_u03b1_2587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2588_: *mut crate::leanh::LeanObject,
    mut v_inst_2589_: *mut crate::leanh::LeanObject,
    mut v_xs_2590_: *mut crate::leanh::LeanObject,
    mut v_h_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2592_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2592_, 0, v_inst_2589_);
    v___x_2593_ = l_Std_Internal_List_minKey___redArg(v___f_2592_, v_xs_2590_);
    return v___x_2593_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___redArg(
    mut v_inst_2594_: *mut crate::leanh::LeanObject,
    mut v_inst_2595_: *mut crate::leanh::LeanObject,
    mut v_xs_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2597_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2597_, 0, v_inst_2594_);
    v___x_2598_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2597_, v_xs_2596_);
    if crate::leanh::lean_obj_tag(v___x_2598_) == 0 {
        let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2599_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_2600_ = l_panic___redArg(v_inst_2595_, v___x_2599_);
        return v___x_2600_;
    } else {
        let mut v_val_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2601_ = crate::leanh::lean_ctor_get(v___x_2598_, 0);
        crate::leanh::lean_inc(v_val_2601_);
        crate::leanh::lean_dec_ref_known(v___x_2598_, 1);
        return v_val_2601_;
    }
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___redArg___boxed(
    mut v_inst_2602_: *mut crate::leanh::LeanObject,
    mut v_inst_2603_: *mut crate::leanh::LeanObject,
    mut v_xs_2604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2605_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_2602_, v_inst_2603_, v_xs_2604_);
    crate::leanh::lean_dec(v_inst_2603_);
    return v_res_2605_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21(
    mut v_00_u03b1_2606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2607_: *mut crate::leanh::LeanObject,
    mut v_inst_2608_: *mut crate::leanh::LeanObject,
    mut v_inst_2609_: *mut crate::leanh::LeanObject,
    mut v_xs_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_2608_, v_inst_2609_, v_xs_2610_);
    return v___x_2611_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___boxed(
    mut v_00_u03b1_2612_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2613_: *mut crate::leanh::LeanObject,
    mut v_inst_2614_: *mut crate::leanh::LeanObject,
    mut v_inst_2615_: *mut crate::leanh::LeanObject,
    mut v_xs_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Std_Internal_List_maxKey_x21(
        v_00_u03b1_2612_,
        v_00_u03b2_2613_,
        v_inst_2614_,
        v_inst_2615_,
        v_xs_2616_,
    );
    crate::leanh::lean_dec(v_inst_2615_);
    return v_res_2617_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___redArg(
    mut v_inst_2618_: *mut crate::leanh::LeanObject,
    mut v_xs_2619_: *mut crate::leanh::LeanObject,
    mut v_fallback_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2621_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2621_, 0, v_inst_2618_);
    v___x_2622_ = l_Std_Internal_List_minKeyD___redArg(v___f_2621_, v_xs_2619_, v_fallback_2620_);
    return v___x_2622_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___redArg___boxed(
    mut v_inst_2623_: *mut crate::leanh::LeanObject,
    mut v_xs_2624_: *mut crate::leanh::LeanObject,
    mut v_fallback_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2626_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_2623_, v_xs_2624_, v_fallback_2625_);
    crate::leanh::lean_dec(v_fallback_2625_);
    return v_res_2626_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD(
    mut v_00_u03b1_2627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2628_: *mut crate::leanh::LeanObject,
    mut v_inst_2629_: *mut crate::leanh::LeanObject,
    mut v_xs_2630_: *mut crate::leanh::LeanObject,
    mut v_fallback_2631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2632_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2632_, 0, v_inst_2629_);
    v___x_2633_ = l_Std_Internal_List_minKeyD___redArg(v___f_2632_, v_xs_2630_, v_fallback_2631_);
    return v___x_2633_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___boxed(
    mut v_00_u03b1_2634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2635_: *mut crate::leanh::LeanObject,
    mut v_inst_2636_: *mut crate::leanh::LeanObject,
    mut v_xs_2637_: *mut crate::leanh::LeanObject,
    mut v_fallback_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Std_Internal_List_maxKeyD(
        v_00_u03b1_2634_,
        v_00_u03b2_2635_,
        v_inst_2636_,
        v_xs_2637_,
        v_fallback_2638_,
    );
    crate::leanh::lean_dec(v_fallback_2638_);
    return v_res_2639_;
}
pub unsafe fn l_Std_Internal_List_interSmallerFn___redArg(
    mut v_inst_2640_: *mut crate::leanh::LeanObject,
    mut v_l_2641_: *mut crate::leanh::LeanObject,
    mut v_sofar_2642_: *mut crate::leanh::LeanObject,
    mut v_k_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2640_);
    v___x_2644_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_2640_, v_k_2643_, v_l_2641_);
    if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
        crate::leanh::lean_dec_ref(v_inst_2640_);
        return v_sofar_2642_;
    } else {
        let mut v_val_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2645_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
        crate::leanh::lean_inc(v_val_2645_);
        crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
        v_fst_2646_ = crate::leanh::lean_ctor_get(v_val_2645_, 0);
        crate::leanh::lean_inc(v_fst_2646_);
        v_snd_2647_ = crate::leanh::lean_ctor_get(v_val_2645_, 1);
        crate::leanh::lean_inc(v_snd_2647_);
        crate::leanh::lean_dec(v_val_2645_);
        v___x_2648_ = l_Std_Internal_List_insertEntry___redArg(
            v_inst_2640_,
            v_fst_2646_,
            v_snd_2647_,
            v_sofar_2642_,
        );
        return v___x_2648_;
    }
}
pub unsafe fn l_Std_Internal_List_interSmallerFn(
    mut v_00_u03b1_2649_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2650_: *mut crate::leanh::LeanObject,
    mut v_inst_2651_: *mut crate::leanh::LeanObject,
    mut v_l_2652_: *mut crate::leanh::LeanObject,
    mut v_sofar_2653_: *mut crate::leanh::LeanObject,
    mut v_k_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Std_Internal_List_interSmallerFn___redArg(
        v_inst_2651_,
        v_l_2652_,
        v_sofar_2653_,
        v_k_2654_,
    );
    return v___x_2655_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(
    mut v_x_2656_: *mut crate::leanh::LeanObject,
    mut v_h__1_2657_: *mut crate::leanh::LeanObject,
    mut v_h__2_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2656_) == 0 {
        let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2657_);
        v___x_2659_ = crate::leanh::lean_box(0);
        v___x_2660_ = crate::leanh::lean_apply_1(v_h__2_2658_, v___x_2659_);
        return v___x_2660_;
    } else {
        let mut v_val_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2658_);
        v_val_2661_ = crate::leanh::lean_ctor_get(v_x_2656_, 0);
        crate::leanh::lean_inc(v_val_2661_);
        crate::leanh::lean_dec_ref_known(v_x_2656_, 1);
        v___x_2662_ = crate::leanh::lean_apply_1(v_h__1_2657_, v_val_2661_);
        return v___x_2662_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_2663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2664_: *mut crate::leanh::LeanObject,
    mut v_motive_2665_: *mut crate::leanh::LeanObject,
    mut v_x_2666_: *mut crate::leanh::LeanObject,
    mut v_h__1_2667_: *mut crate::leanh::LeanObject,
    mut v_h__2_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2666_) == 0 {
        let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2667_);
        v___x_2669_ = crate::leanh::lean_box(0);
        v___x_2670_ = crate::leanh::lean_apply_1(v_h__2_2668_, v___x_2669_);
        return v___x_2670_;
    } else {
        let mut v_val_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2668_);
        v_val_2671_ = crate::leanh::lean_ctor_get(v_x_2666_, 0);
        crate::leanh::lean_inc(v_val_2671_);
        crate::leanh::lean_dec_ref_known(v_x_2666_, 1);
        v___x_2672_ = crate::leanh::lean_apply_1(v_h__1_2667_, v_val_2671_);
        return v___x_2672_;
    }
}
pub unsafe fn l_Std_Internal_List_interSmaller___redArg___lam__0(
    mut v_inst_2673_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_2674_: *mut crate::leanh::LeanObject,
    mut v_sofar_2675_: *mut crate::leanh::LeanObject,
    mut v_kv_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2677_ = crate::leanh::lean_ctor_get(v_kv_2676_, 0);
    crate::leanh::lean_inc(v_fst_2677_);
    crate::leanh::lean_dec_ref(v_kv_2676_);
    v___x_2678_ = l_Std_Internal_List_interSmallerFn___redArg(
        v_inst_2673_,
        v_l_u2081_2674_,
        v_sofar_2675_,
        v_fst_2677_,
    );
    return v___x_2678_;
}
pub unsafe fn l_Std_Internal_List_interSmaller___redArg(
    mut v_inst_2679_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_2680_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2682_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_List_interSmaller___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2682_, 0, v_inst_2679_);
    crate::leanh::lean_closure_set(v___f_2682_, 1, v_l_u2081_2680_);
    v___x_2683_ = crate::leanh::lean_box(0);
    v___x_2684_ = l_List_foldl___redArg(v___f_2682_, v___x_2683_, v_l_u2082_2681_);
    return v___x_2684_;
}
pub unsafe fn l_Std_Internal_List_interSmaller(
    mut v_00_u03b1_2685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2686_: *mut crate::leanh::LeanObject,
    mut v_inst_2687_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_2688_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ =
        l_Std_Internal_List_interSmaller___redArg(v_inst_2687_, v_l_u2081_2688_, v_l_u2082_2689_);
    return v___x_2690_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Internal_List_Associative(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_LemmasExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
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
pub unsafe fn meta_initialize_Std_Data_Internal_List_Associative(
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
pub unsafe fn initialize_Std_Data_Internal_List_Associative(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_LemmasExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Internal_List_Associative(builtin);
}
