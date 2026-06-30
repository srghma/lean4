// Lean compiler output
// Module: Std.Data.Internal.List.Associative
// Imports: Init.Data.Option.Attach Init.Data.List.Perm Std.Data.Internal.List.Defs Std.Data.Internal.List.Defs Init.Data.Order.LemmasExtra Init.Data.Bool Init.ByCases Init.Data.List.Count Init.Data.List.Erase Init.Data.List.Find Init.Data.List.MinMax Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.Prod Init.Omega
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le};
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
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__0_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__1_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_List_getEntry_x21___redArg___closed__2_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getEntry_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_List_getEntry_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_List_getValueCast_x21___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_List_insertListConst___redArg___closed__0_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_List_Prod_toSigma as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_List_insertListConst___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_List_insertListConst___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Internal_List_getEntry_x3f___redArg(
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_x_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1348_) == 0 {
                    leanh::lean_dec(v_a_1347_);
                    leanh::lean_dec_ref(v_inst_1346_);
                    v___x_1349_ = leanh::lean_box(0);
                    return v___x_1349_;
                } else {
                    v_head_1350_ = leanh::lean_ctor_get(v_x_1348_, 0);
                    leanh::lean_inc(v_head_1350_);
                    v_tail_1351_ = leanh::lean_ctor_get(v_x_1348_, 1);
                    leanh::lean_inc(v_tail_1351_);
                    leanh::lean_dec_ref_known(v_x_1348_, 2);
                    v_fst_1352_ = leanh::lean_ctor_get(v_head_1350_, 0);
                    leanh::lean_inc_ref(v_inst_1346_);
                    leanh::lean_inc(v_a_1347_);
                    leanh::lean_inc(v_fst_1352_);
                    v___x_1353_ = leanh::lean_apply_2(v_inst_1346_, v_fst_1352_, v_a_1347_);
                    v___x_1354_ = (leanh::lean_unbox(v___x_1353_) as u8);
                    if v___x_1354_ == 0 {
                        leanh::lean_dec(v_head_1350_);
                        v_x_1348_ = v_tail_1351_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1351_);
                        leanh::lean_dec(v_a_1347_);
                        leanh::lean_dec_ref(v_inst_1346_);
                        v___x_1356_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1356_, 0, v_head_1350_);
                        return v___x_1356_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntry_x3f(
    mut v_00_u03b1_1357_: *mut leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_x_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1359_, v_a_1360_, v_x_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Std_Internal_List_getEntryD___redArg(
    mut v_inst_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
    mut v_fallback_1365_: *mut leanh::LeanObject,
    mut v_x_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1366_) == 0 {
                    leanh::lean_dec(v_a_1364_);
                    leanh::lean_dec_ref(v_inst_1363_);
                    leanh::lean_inc_ref(v_fallback_1365_);
                    return v_fallback_1365_;
                } else {
                    v_head_1367_ = leanh::lean_ctor_get(v_x_1366_, 0);
                    leanh::lean_inc(v_head_1367_);
                    v_tail_1368_ = leanh::lean_ctor_get(v_x_1366_, 1);
                    leanh::lean_inc(v_tail_1368_);
                    leanh::lean_dec_ref_known(v_x_1366_, 2);
                    v_fst_1369_ = leanh::lean_ctor_get(v_head_1367_, 0);
                    leanh::lean_inc_ref(v_inst_1363_);
                    leanh::lean_inc(v_a_1364_);
                    leanh::lean_inc(v_fst_1369_);
                    v___x_1370_ = leanh::lean_apply_2(v_inst_1363_, v_fst_1369_, v_a_1364_);
                    v___x_1371_ = (leanh::lean_unbox(v___x_1370_) as u8);
                    if v___x_1371_ == 0 {
                        leanh::lean_dec(v_head_1367_);
                        v_x_1366_ = v_tail_1368_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1368_);
                        leanh::lean_dec(v_a_1364_);
                        leanh::lean_dec_ref(v_inst_1363_);
                        return v_head_1367_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntryD___redArg___boxed(
    mut v_inst_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_fallback_1375_: *mut leanh::LeanObject,
    mut v_x_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1377_ = l_Std_Internal_List_getEntryD___redArg(
        v_inst_1373_,
        v_a_1374_,
        v_fallback_1375_,
        v_x_1376_,
    );
    leanh::lean_dec_ref(v_fallback_1375_);
    return v_res_1377_;
}
pub unsafe fn l_Std_Internal_List_getEntryD(
    mut v_00_u03b1_1378_: *mut leanh::LeanObject,
    mut v_00_u03b2_1379_: *mut leanh::LeanObject,
    mut v_inst_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_fallback_1382_: *mut leanh::LeanObject,
    mut v_x_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Std_Internal_List_getEntryD___redArg(
        v_inst_1380_,
        v_a_1381_,
        v_fallback_1382_,
        v_x_1383_,
    );
    return v___x_1384_;
}
pub unsafe fn l_Std_Internal_List_getEntryD___boxed(
    mut v_00_u03b1_1385_: *mut leanh::LeanObject,
    mut v_00_u03b2_1386_: *mut leanh::LeanObject,
    mut v_inst_1387_: *mut leanh::LeanObject,
    mut v_a_1388_: *mut leanh::LeanObject,
    mut v_fallback_1389_: *mut leanh::LeanObject,
    mut v_x_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Std_Internal_List_getEntryD(
        v_00_u03b1_1385_,
        v_00_u03b2_1386_,
        v_inst_1387_,
        v_a_1388_,
        v_fallback_1389_,
        v_x_1390_,
    );
    leanh::lean_dec_ref(v_fallback_1389_);
    return v_res_1391_;
}
pub unsafe fn _init_l_Std_Internal_List_getEntry_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Std_Internal_List_getEntry_x21___redArg___closed__2;
    v___x_1396_ = leanh::lean_unsigned_to_nat(10);
    v___x_1397_ = leanh::lean_unsigned_to_nat(67);
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
    mut v_inst_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_inst_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1404_) == 0 {
                    leanh::lean_dec(v_a_1402_);
                    leanh::lean_dec_ref(v_inst_1401_);
                    v___x_1405_ = leanh::lean_obj_once(
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
                    v_head_1407_ = leanh::lean_ctor_get(v_x_1404_, 0);
                    leanh::lean_inc(v_head_1407_);
                    v_tail_1408_ = leanh::lean_ctor_get(v_x_1404_, 1);
                    leanh::lean_inc(v_tail_1408_);
                    leanh::lean_dec_ref_known(v_x_1404_, 2);
                    v_fst_1409_ = leanh::lean_ctor_get(v_head_1407_, 0);
                    leanh::lean_inc_ref(v_inst_1401_);
                    leanh::lean_inc(v_a_1402_);
                    leanh::lean_inc(v_fst_1409_);
                    v___x_1410_ = leanh::lean_apply_2(v_inst_1401_, v_fst_1409_, v_a_1402_);
                    v___x_1411_ = (leanh::lean_unbox(v___x_1410_) as u8);
                    if v___x_1411_ == 0 {
                        leanh::lean_dec(v_head_1407_);
                        v_x_1404_ = v_tail_1408_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1408_);
                        leanh::lean_dec(v_a_1402_);
                        leanh::lean_dec_ref(v_inst_1401_);
                        return v_head_1407_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getEntry_x21___redArg___boxed(
    mut v_inst_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_inst_1415_: *mut leanh::LeanObject,
    mut v_x_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ =
        l_Std_Internal_List_getEntry_x21___redArg(v_inst_1413_, v_a_1414_, v_inst_1415_, v_x_1416_);
    leanh::lean_dec_ref(v_inst_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Std_Internal_List_getEntry_x21(
    mut v_00_u03b1_1418_: *mut leanh::LeanObject,
    mut v_00_u03b2_1419_: *mut leanh::LeanObject,
    mut v_inst_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_inst_1422_: *mut leanh::LeanObject,
    mut v_x_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ =
        l_Std_Internal_List_getEntry_x21___redArg(v_inst_1420_, v_a_1421_, v_inst_1422_, v_x_1423_);
    return v___x_1424_;
}
pub unsafe fn l_Std_Internal_List_getEntry_x21___boxed(
    mut v_00_u03b1_1425_: *mut leanh::LeanObject,
    mut v_00_u03b2_1426_: *mut leanh::LeanObject,
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
    mut v_inst_1429_: *mut leanh::LeanObject,
    mut v_x_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Std_Internal_List_getEntry_x21(
        v_00_u03b1_1425_,
        v_00_u03b2_1426_,
        v_inst_1427_,
        v_a_1428_,
        v_inst_1429_,
        v_x_1430_,
    );
    leanh::lean_dec_ref(v_inst_1429_);
    return v_res_1431_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v_h__1_1433_: *mut leanh::LeanObject,
    mut v_h__2_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1432_) == 0 {
        let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1434_);
        v___x_1435_ = leanh::lean_box(0);
        v___x_1436_ = leanh::lean_apply_1(v_h__1_1433_, v___x_1435_);
        return v___x_1436_;
    } else {
        let mut v_head_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1433_);
        v_head_1437_ = leanh::lean_ctor_get(v_x_1432_, 0);
        leanh::lean_inc(v_head_1437_);
        v_tail_1438_ = leanh::lean_ctor_get(v_x_1432_, 1);
        leanh::lean_inc(v_tail_1438_);
        leanh::lean_dec_ref_known(v_x_1432_, 2);
        v_fst_1439_ = leanh::lean_ctor_get(v_head_1437_, 0);
        leanh::lean_inc(v_fst_1439_);
        v_snd_1440_ = leanh::lean_ctor_get(v_head_1437_, 1);
        leanh::lean_inc(v_snd_1440_);
        leanh::lean_dec(v_head_1437_);
        v___x_1441_ =
            leanh::lean_apply_3(v_h__2_1434_, v_fst_1439_, v_snd_1440_, v_tail_1438_);
        return v___x_1441_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1442_: *mut leanh::LeanObject,
    mut v_00_u03b2_1443_: *mut leanh::LeanObject,
    mut v_motive_1444_: *mut leanh::LeanObject,
    mut v_x_1445_: *mut leanh::LeanObject,
    mut v_h__1_1446_: *mut leanh::LeanObject,
    mut v_h__2_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1445_) == 0 {
        let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1447_);
        v___x_1448_ = leanh::lean_box(0);
        v___x_1449_ = leanh::lean_apply_1(v_h__1_1446_, v___x_1448_);
        return v___x_1449_;
    } else {
        let mut v_head_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1446_);
        v_head_1450_ = leanh::lean_ctor_get(v_x_1445_, 0);
        leanh::lean_inc(v_head_1450_);
        v_tail_1451_ = leanh::lean_ctor_get(v_x_1445_, 1);
        leanh::lean_inc(v_tail_1451_);
        leanh::lean_dec_ref_known(v_x_1445_, 2);
        v_fst_1452_ = leanh::lean_ctor_get(v_head_1450_, 0);
        leanh::lean_inc(v_fst_1452_);
        v_snd_1453_ = leanh::lean_ctor_get(v_head_1450_, 1);
        leanh::lean_inc(v_snd_1453_);
        leanh::lean_dec(v_head_1450_);
        v___x_1454_ =
            leanh::lean_apply_3(v_h__2_1447_, v_fst_1452_, v_snd_1453_, v_tail_1451_);
        return v___x_1454_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_h__1_1456_: *mut leanh::LeanObject,
    mut v_h__2_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1455_) == 0 {
        let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1457_);
        v___x_1458_ = leanh::lean_box(0);
        v___x_1459_ = leanh::lean_apply_1(v_h__1_1456_, v___x_1458_);
        return v___x_1459_;
    } else {
        let mut v_head_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1456_);
        v_head_1460_ = leanh::lean_ctor_get(v_x_1455_, 0);
        leanh::lean_inc(v_head_1460_);
        v_tail_1461_ = leanh::lean_ctor_get(v_x_1455_, 1);
        leanh::lean_inc(v_tail_1461_);
        leanh::lean_dec_ref_known(v_x_1455_, 2);
        v_fst_1462_ = leanh::lean_ctor_get(v_head_1460_, 0);
        leanh::lean_inc(v_fst_1462_);
        v_snd_1463_ = leanh::lean_ctor_get(v_head_1460_, 1);
        leanh::lean_inc(v_snd_1463_);
        leanh::lean_dec(v_head_1460_);
        v___x_1464_ =
            leanh::lean_apply_3(v_h__2_1457_, v_fst_1462_, v_snd_1463_, v_tail_1461_);
        return v___x_1464_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(
    mut v_00_u03b1_1465_: *mut leanh::LeanObject,
    mut v_00_u03b2_1466_: *mut leanh::LeanObject,
    mut v_motive_1467_: *mut leanh::LeanObject,
    mut v_x_1468_: *mut leanh::LeanObject,
    mut v_h__1_1469_: *mut leanh::LeanObject,
    mut v_h__2_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1468_) == 0 {
        let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1470_);
        v___x_1471_ = leanh::lean_box(0);
        v___x_1472_ = leanh::lean_apply_1(v_h__1_1469_, v___x_1471_);
        return v___x_1472_;
    } else {
        let mut v_head_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1469_);
        v_head_1473_ = leanh::lean_ctor_get(v_x_1468_, 0);
        leanh::lean_inc(v_head_1473_);
        v_tail_1474_ = leanh::lean_ctor_get(v_x_1468_, 1);
        leanh::lean_inc(v_tail_1474_);
        leanh::lean_dec_ref_known(v_x_1468_, 2);
        v_fst_1475_ = leanh::lean_ctor_get(v_head_1473_, 0);
        leanh::lean_inc(v_fst_1475_);
        v_snd_1476_ = leanh::lean_ctor_get(v_head_1473_, 1);
        leanh::lean_inc(v_snd_1476_);
        leanh::lean_dec(v_head_1473_);
        v___x_1477_ =
            leanh::lean_apply_3(v_h__2_1470_, v_fst_1475_, v_snd_1476_, v_tail_1474_);
        return v___x_1477_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(
    mut v_x_1478_: *mut leanh::LeanObject,
    mut v_h__1_1479_: *mut leanh::LeanObject,
    mut v_h__2_1480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1478_) == 0 {
        let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1480_);
        v___x_1481_ = leanh::lean_box(0);
        v___x_1482_ = leanh::lean_apply_1(v_h__1_1479_, v___x_1481_);
        return v___x_1482_;
    } else {
        let mut v_head_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1479_);
        v_head_1483_ = leanh::lean_ctor_get(v_x_1478_, 0);
        leanh::lean_inc(v_head_1483_);
        v_tail_1484_ = leanh::lean_ctor_get(v_x_1478_, 1);
        leanh::lean_inc(v_tail_1484_);
        leanh::lean_dec_ref_known(v_x_1478_, 2);
        v_fst_1485_ = leanh::lean_ctor_get(v_head_1483_, 0);
        leanh::lean_inc(v_fst_1485_);
        v_snd_1486_ = leanh::lean_ctor_get(v_head_1483_, 1);
        leanh::lean_inc(v_snd_1486_);
        leanh::lean_dec(v_head_1483_);
        v___x_1487_ =
            leanh::lean_apply_3(v_h__2_1480_, v_fst_1485_, v_snd_1486_, v_tail_1484_);
        return v___x_1487_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(
    mut v_00_u03b1_1488_: *mut leanh::LeanObject,
    mut v_00_u03b2_1489_: *mut leanh::LeanObject,
    mut v_motive_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
    mut v_h__1_1492_: *mut leanh::LeanObject,
    mut v_h__2_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1491_) == 0 {
        let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1493_);
        v___x_1494_ = leanh::lean_box(0);
        v___x_1495_ = leanh::lean_apply_1(v_h__1_1492_, v___x_1494_);
        return v___x_1495_;
    } else {
        let mut v_head_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1492_);
        v_head_1496_ = leanh::lean_ctor_get(v_x_1491_, 0);
        leanh::lean_inc(v_head_1496_);
        v_tail_1497_ = leanh::lean_ctor_get(v_x_1491_, 1);
        leanh::lean_inc(v_tail_1497_);
        leanh::lean_dec_ref_known(v_x_1491_, 2);
        v_fst_1498_ = leanh::lean_ctor_get(v_head_1496_, 0);
        leanh::lean_inc(v_fst_1498_);
        v_snd_1499_ = leanh::lean_ctor_get(v_head_1496_, 1);
        leanh::lean_inc(v_snd_1499_);
        leanh::lean_dec(v_head_1496_);
        v___x_1500_ =
            leanh::lean_apply_3(v_h__2_1493_, v_fst_1498_, v_snd_1499_, v_tail_1497_);
        return v___x_1500_;
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x3f___redArg(
    mut v_inst_1501_: *mut leanh::LeanObject,
    mut v_a_1502_: *mut leanh::LeanObject,
    mut v_x_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1503_) == 0 {
                    leanh::lean_dec(v_a_1502_);
                    leanh::lean_dec_ref(v_inst_1501_);
                    v___x_1504_ = leanh::lean_box(0);
                    return v___x_1504_;
                } else {
                    v_head_1505_ = leanh::lean_ctor_get(v_x_1503_, 0);
                    leanh::lean_inc(v_head_1505_);
                    v_tail_1506_ = leanh::lean_ctor_get(v_x_1503_, 1);
                    leanh::lean_inc(v_tail_1506_);
                    leanh::lean_dec_ref_known(v_x_1503_, 2);
                    v_fst_1507_ = leanh::lean_ctor_get(v_head_1505_, 0);
                    leanh::lean_inc(v_fst_1507_);
                    v_snd_1508_ = leanh::lean_ctor_get(v_head_1505_, 1);
                    leanh::lean_inc(v_snd_1508_);
                    leanh::lean_dec(v_head_1505_);
                    leanh::lean_inc_ref(v_inst_1501_);
                    leanh::lean_inc(v_a_1502_);
                    v___x_1509_ = leanh::lean_apply_2(v_inst_1501_, v_fst_1507_, v_a_1502_);
                    v___x_1510_ = (leanh::lean_unbox(v___x_1509_) as u8);
                    if v___x_1510_ == 0 {
                        leanh::lean_dec(v_snd_1508_);
                        v_x_1503_ = v_tail_1506_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1506_);
                        leanh::lean_dec(v_a_1502_);
                        leanh::lean_dec_ref(v_inst_1501_);
                        v___x_1512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1512_, 0, v_snd_1508_);
                        return v___x_1512_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x3f(
    mut v_00_u03b1_1513_: *mut leanh::LeanObject,
    mut v_00_u03b2_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_x_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1515_, v_a_1516_, v_x_1517_);
    return v___x_1518_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(
    mut v_x_1519_: *mut leanh::LeanObject,
    mut v_h__1_1520_: *mut leanh::LeanObject,
    mut v_h__2_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1519_) == 0 {
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1521_);
        v___x_1522_ = leanh::lean_box(0);
        v___x_1523_ = leanh::lean_apply_1(v_h__1_1520_, v___x_1522_);
        return v___x_1523_;
    } else {
        let mut v_head_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1520_);
        v_head_1524_ = leanh::lean_ctor_get(v_x_1519_, 0);
        leanh::lean_inc(v_head_1524_);
        v_tail_1525_ = leanh::lean_ctor_get(v_x_1519_, 1);
        leanh::lean_inc(v_tail_1525_);
        leanh::lean_dec_ref_known(v_x_1519_, 2);
        v_fst_1526_ = leanh::lean_ctor_get(v_head_1524_, 0);
        leanh::lean_inc(v_fst_1526_);
        v_snd_1527_ = leanh::lean_ctor_get(v_head_1524_, 1);
        leanh::lean_inc(v_snd_1527_);
        leanh::lean_dec(v_head_1524_);
        v___x_1528_ =
            leanh::lean_apply_3(v_h__2_1521_, v_fst_1526_, v_snd_1527_, v_tail_1525_);
        return v___x_1528_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(
    mut v_00_u03b1_1529_: *mut leanh::LeanObject,
    mut v_00_u03b2_1530_: *mut leanh::LeanObject,
    mut v_motive_1531_: *mut leanh::LeanObject,
    mut v_x_1532_: *mut leanh::LeanObject,
    mut v_h__1_1533_: *mut leanh::LeanObject,
    mut v_h__2_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1532_) == 0 {
        let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1534_);
        v___x_1535_ = leanh::lean_box(0);
        v___x_1536_ = leanh::lean_apply_1(v_h__1_1533_, v___x_1535_);
        return v___x_1536_;
    } else {
        let mut v_head_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1533_);
        v_head_1537_ = leanh::lean_ctor_get(v_x_1532_, 0);
        leanh::lean_inc(v_head_1537_);
        v_tail_1538_ = leanh::lean_ctor_get(v_x_1532_, 1);
        leanh::lean_inc(v_tail_1538_);
        leanh::lean_dec_ref_known(v_x_1532_, 2);
        v_fst_1539_ = leanh::lean_ctor_get(v_head_1537_, 0);
        leanh::lean_inc(v_fst_1539_);
        v_snd_1540_ = leanh::lean_ctor_get(v_head_1537_, 1);
        leanh::lean_inc(v_snd_1540_);
        leanh::lean_dec(v_head_1537_);
        v___x_1541_ =
            leanh::lean_apply_3(v_h__2_1534_, v_fst_1539_, v_snd_1540_, v_tail_1538_);
        return v___x_1541_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x3f___redArg(
    mut v_inst_1542_: *mut leanh::LeanObject,
    mut v_a_1543_: *mut leanh::LeanObject,
    mut v_x_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1544_) == 0 {
                    leanh::lean_dec(v_a_1543_);
                    leanh::lean_dec_ref(v_inst_1542_);
                    v___x_1545_ = leanh::lean_box(0);
                    return v___x_1545_;
                } else {
                    v_head_1546_ = leanh::lean_ctor_get(v_x_1544_, 0);
                    leanh::lean_inc(v_head_1546_);
                    v_tail_1547_ = leanh::lean_ctor_get(v_x_1544_, 1);
                    leanh::lean_inc(v_tail_1547_);
                    leanh::lean_dec_ref_known(v_x_1544_, 2);
                    v_fst_1548_ = leanh::lean_ctor_get(v_head_1546_, 0);
                    leanh::lean_inc(v_fst_1548_);
                    v_snd_1549_ = leanh::lean_ctor_get(v_head_1546_, 1);
                    leanh::lean_inc(v_snd_1549_);
                    leanh::lean_dec(v_head_1546_);
                    leanh::lean_inc_ref(v_inst_1542_);
                    leanh::lean_inc(v_a_1543_);
                    v___x_1550_ = leanh::lean_apply_2(v_inst_1542_, v_fst_1548_, v_a_1543_);
                    v___x_1551_ = (leanh::lean_unbox(v___x_1550_) as u8);
                    if v___x_1551_ == 0 {
                        leanh::lean_dec(v_snd_1549_);
                        v_x_1544_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1547_);
                        leanh::lean_dec(v_a_1543_);
                        leanh::lean_dec_ref(v_inst_1542_);
                        v___x_1553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1553_, 0, v_snd_1549_);
                        return v___x_1553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x3f(
    mut v_00_u03b1_1554_: *mut leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
    mut v_inst_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_x_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1556_, v_a_1558_, v_x_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___lam__0(
    mut v_inst_1561_: *mut leanh::LeanObject,
    mut v_inst_1562_: *mut leanh::LeanObject,
    mut v_l_u2082_1563_: *mut leanh::LeanObject,
    mut v_x_1564_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_fst_1565_ = leanh::lean_ctor_get(v_x_1564_, 0);
    leanh::lean_inc_n(v_fst_1565_, 2);
    v_snd_1566_ = leanh::lean_ctor_get(v_x_1564_, 1);
    leanh::lean_inc(v_snd_1566_);
    leanh::lean_dec_ref(v_x_1564_);
    v___x_1567_ = leanh::lean_apply_1(v_inst_1561_, v_fst_1565_);
    v___x_1568_ =
        l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1562_, v_fst_1565_, v_l_u2082_1563_);
    v___x_1569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1569_, 0, v_snd_1566_);
    v___x_1570_ = l_Option_instBEq_beq___redArg(v___x_1567_, v___x_1568_, v___x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___lam__0___boxed(
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_l_u2082_1573_: *mut leanh::LeanObject,
    mut v_x_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1575_: u8 = 0;
    let mut v_r_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1575_ = l_Std_Internal_List_beqModel___redArg___lam__0(
        v_inst_1571_,
        v_inst_1572_,
        v_l_u2082_1573_,
        v_x_1574_,
    );
    v_r_1576_ = leanh::lean_box((v_res_1575_) as usize);
    return v_r_1576_;
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg(
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_l_u2081_1579_: *mut leanh::LeanObject,
    mut v_l_u2082_1580_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    v___x_1581_ = l_List_lengthTR___redArg(v_l_u2081_1579_);
    v___x_1582_ = l_List_lengthTR___redArg(v_l_u2082_1580_);
    v___x_1583_ = lean_nat_dec_eq(v___x_1581_, v___x_1582_);
    leanh::lean_dec(v___x_1582_);
    leanh::lean_dec(v___x_1581_);
    if v___x_1583_ == 0 {
        leanh::lean_dec(v_l_u2082_1580_);
        leanh::lean_dec(v_l_u2081_1579_);
        leanh::lean_dec_ref(v_inst_1578_);
        leanh::lean_dec_ref(v_inst_1577_);
        return v___x_1583_;
    } else {
        let mut v___f_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: u8 = 0;
        v___f_1584_ = leanh::lean_alloc_closure(
            l_Std_Internal_List_beqModel___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1584_, 0, v_inst_1578_);
        leanh::lean_closure_set(v___f_1584_, 1, v_inst_1577_);
        leanh::lean_closure_set(v___f_1584_, 2, v_l_u2082_1580_);
        v___x_1585_ = l_List_all___redArg(v_l_u2081_1579_, v___f_1584_);
        return v___x_1585_;
    }
}
pub unsafe fn l_Std_Internal_List_beqModel___redArg___boxed(
    mut v_inst_1586_: *mut leanh::LeanObject,
    mut v_inst_1587_: *mut leanh::LeanObject,
    mut v_l_u2081_1588_: *mut leanh::LeanObject,
    mut v_l_u2082_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: u8 = 0;
    let mut v_r_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_Internal_List_beqModel___redArg(
        v_inst_1586_,
        v_inst_1587_,
        v_l_u2081_1588_,
        v_l_u2082_1589_,
    );
    v_r_1591_ = leanh::lean_box((v_res_1590_) as usize);
    return v_r_1591_;
}
pub unsafe fn l_Std_Internal_List_beqModel(
    mut v_00_u03b1_1592_: *mut leanh::LeanObject,
    mut v_00_u03b2_1593_: *mut leanh::LeanObject,
    mut v_inst_1594_: *mut leanh::LeanObject,
    mut v_inst_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
    mut v_l_u2081_1597_: *mut leanh::LeanObject,
    mut v_l_u2082_1598_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_1600_: *mut leanh::LeanObject,
    mut v_00_u03b2_1601_: *mut leanh::LeanObject,
    mut v_inst_1602_: *mut leanh::LeanObject,
    mut v_inst_1603_: *mut leanh::LeanObject,
    mut v_inst_1604_: *mut leanh::LeanObject,
    mut v_l_u2081_1605_: *mut leanh::LeanObject,
    mut v_l_u2082_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1607_: u8 = 0;
    let mut v_r_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Std_Internal_List_beqModel(
        v_00_u03b1_1600_,
        v_00_u03b2_1601_,
        v_inst_1602_,
        v_inst_1603_,
        v_inst_1604_,
        v_l_u2081_1605_,
        v_l_u2082_1606_,
    );
    v_r_1608_ = leanh::lean_box((v_res_1607_) as usize);
    return v_r_1608_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(
    mut v_x_1609_: *mut leanh::LeanObject,
    mut v_h__1_1610_: *mut leanh::LeanObject,
    mut v_h__2_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1609_) == 0 {
        let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1611_);
        v___x_1612_ = leanh::lean_box(0);
        v___x_1613_ = leanh::lean_apply_1(v_h__1_1610_, v___x_1612_);
        return v___x_1613_;
    } else {
        let mut v_head_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1610_);
        v_head_1614_ = leanh::lean_ctor_get(v_x_1609_, 0);
        leanh::lean_inc(v_head_1614_);
        v_tail_1615_ = leanh::lean_ctor_get(v_x_1609_, 1);
        leanh::lean_inc(v_tail_1615_);
        leanh::lean_dec_ref_known(v_x_1609_, 2);
        v_fst_1616_ = leanh::lean_ctor_get(v_head_1614_, 0);
        leanh::lean_inc(v_fst_1616_);
        v_snd_1617_ = leanh::lean_ctor_get(v_head_1614_, 1);
        leanh::lean_inc(v_snd_1617_);
        leanh::lean_dec(v_head_1614_);
        v___x_1618_ =
            leanh::lean_apply_3(v_h__2_1611_, v_fst_1616_, v_snd_1617_, v_tail_1615_);
        return v___x_1618_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(
    mut v_00_u03b1_1619_: *mut leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut leanh::LeanObject,
    mut v_motive_1621_: *mut leanh::LeanObject,
    mut v_x_1622_: *mut leanh::LeanObject,
    mut v_h__1_1623_: *mut leanh::LeanObject,
    mut v_h__2_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1622_) == 0 {
        let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1624_);
        v___x_1625_ = leanh::lean_box(0);
        v___x_1626_ = leanh::lean_apply_1(v_h__1_1623_, v___x_1625_);
        return v___x_1626_;
    } else {
        let mut v_head_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1623_);
        v_head_1627_ = leanh::lean_ctor_get(v_x_1622_, 0);
        leanh::lean_inc(v_head_1627_);
        v_tail_1628_ = leanh::lean_ctor_get(v_x_1622_, 1);
        leanh::lean_inc(v_tail_1628_);
        leanh::lean_dec_ref_known(v_x_1622_, 2);
        v_fst_1629_ = leanh::lean_ctor_get(v_head_1627_, 0);
        leanh::lean_inc(v_fst_1629_);
        v_snd_1630_ = leanh::lean_ctor_get(v_head_1627_, 1);
        leanh::lean_inc(v_snd_1630_);
        leanh::lean_dec(v_head_1627_);
        v___x_1631_ =
            leanh::lean_apply_3(v_h__2_1624_, v_fst_1629_, v_snd_1630_, v_tail_1628_);
        return v___x_1631_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___lam__0(
    mut v_inst_1632_: *mut leanh::LeanObject,
    mut v_l_u2082_1633_: *mut leanh::LeanObject,
    mut v_inst_1634_: *mut leanh::LeanObject,
    mut v_x_1635_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    v_fst_1636_ = leanh::lean_ctor_get(v_x_1635_, 0);
    leanh::lean_inc(v_fst_1636_);
    v_snd_1637_ = leanh::lean_ctor_get(v_x_1635_, 1);
    leanh::lean_inc(v_snd_1637_);
    leanh::lean_dec_ref(v_x_1635_);
    v___x_1638_ =
        l_Std_Internal_List_getValue_x3f___redArg(v_inst_1632_, v_fst_1636_, v_l_u2082_1633_);
    v___x_1639_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1639_, 0, v_snd_1637_);
    v___x_1640_ = l_Option_instBEq_beq___redArg(v_inst_1634_, v___x_1638_, v___x_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(
    mut v_inst_1641_: *mut leanh::LeanObject,
    mut v_l_u2082_1642_: *mut leanh::LeanObject,
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1645_: u8 = 0;
    let mut v_r_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(
        v_inst_1641_,
        v_l_u2082_1642_,
        v_inst_1643_,
        v_x_1644_,
    );
    v_r_1646_ = leanh::lean_box((v_res_1645_) as usize);
    return v_r_1646_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg(
    mut v_inst_1647_: *mut leanh::LeanObject,
    mut v_inst_1648_: *mut leanh::LeanObject,
    mut v_l_u2081_1649_: *mut leanh::LeanObject,
    mut v_l_u2082_1650_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    v___x_1651_ = l_List_lengthTR___redArg(v_l_u2081_1649_);
    v___x_1652_ = l_List_lengthTR___redArg(v_l_u2082_1650_);
    v___x_1653_ = lean_nat_dec_eq(v___x_1651_, v___x_1652_);
    leanh::lean_dec(v___x_1652_);
    leanh::lean_dec(v___x_1651_);
    if v___x_1653_ == 0 {
        leanh::lean_dec(v_l_u2082_1650_);
        leanh::lean_dec(v_l_u2081_1649_);
        leanh::lean_dec_ref(v_inst_1648_);
        leanh::lean_dec_ref(v_inst_1647_);
        return v___x_1653_;
    } else {
        let mut v___f_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: u8 = 0;
        v___f_1654_ = leanh::lean_alloc_closure(
            l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1654_, 0, v_inst_1647_);
        leanh::lean_closure_set(v___f_1654_, 1, v_l_u2082_1650_);
        leanh::lean_closure_set(v___f_1654_, 2, v_inst_1648_);
        v___x_1655_ = l_List_all___redArg(v_l_u2081_1649_, v___f_1654_);
        return v___x_1655_;
    }
}
pub unsafe fn l_Std_Internal_List_Const_beqModel___redArg___boxed(
    mut v_inst_1656_: *mut leanh::LeanObject,
    mut v_inst_1657_: *mut leanh::LeanObject,
    mut v_l_u2081_1658_: *mut leanh::LeanObject,
    mut v_l_u2082_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1660_: u8 = 0;
    let mut v_r_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Std_Internal_List_Const_beqModel___redArg(
        v_inst_1656_,
        v_inst_1657_,
        v_l_u2081_1658_,
        v_l_u2082_1659_,
    );
    v_r_1661_ = leanh::lean_box((v_res_1660_) as usize);
    return v_r_1661_;
}
pub unsafe fn l_Std_Internal_List_Const_beqModel(
    mut v_00_u03b1_1662_: *mut leanh::LeanObject,
    mut v_00_u03b2_1663_: *mut leanh::LeanObject,
    mut v_inst_1664_: *mut leanh::LeanObject,
    mut v_inst_1665_: *mut leanh::LeanObject,
    mut v_l_u2081_1666_: *mut leanh::LeanObject,
    mut v_l_u2082_1667_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_1669_: *mut leanh::LeanObject,
    mut v_00_u03b2_1670_: *mut leanh::LeanObject,
    mut v_inst_1671_: *mut leanh::LeanObject,
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_l_u2081_1673_: *mut leanh::LeanObject,
    mut v_l_u2082_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1675_: u8 = 0;
    let mut v_r_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Std_Internal_List_Const_beqModel(
        v_00_u03b1_1669_,
        v_00_u03b2_1670_,
        v_inst_1671_,
        v_inst_1672_,
        v_l_u2081_1673_,
        v_l_u2082_1674_,
    );
    v_r_1676_ = leanh::lean_box((v_res_1675_) as usize);
    return v_r_1676_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(
    mut v_x_1677_: *mut leanh::LeanObject,
    mut v_x_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1677_) == 0 {
                    leanh::lean_dec(v_x_1678_);
                    v___x_1679_ = leanh::lean_box(0);
                    return v___x_1679_;
                } else {
                    v_val_1680_ = leanh::lean_ctor_get(v_x_1677_, 0);
                    v_isSharedCheck_1688_ = (!leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v___x_1682_ = v_x_1677_;
                        v_isShared_1683_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1680_);
                        leanh::lean_dec(v_x_1677_);
                        v___x_1682_ = leanh::lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1684_ =
                    leanh::lean_apply_2(v_x_1678_, v_val_1680_, leanh::lean_box(0));
                if v_isShared_1683_ == 0 {
                    leanh::lean_ctor_set(v___x_1682_, 0, v___x_1684_);
                    v___x_1686_ = v___x_1682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
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
    mut v_00_u03b1_1689_: *mut leanh::LeanObject,
    mut v_00_u03b2_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
    mut v_x_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ =
        l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(
            v_x_1691_, v_x_1692_,
        );
    return v___x_1693_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(
    mut v_x_1694_: *mut leanh::LeanObject,
    mut v_x_1695_: *mut leanh::LeanObject,
    mut v_h__1_1696_: *mut leanh::LeanObject,
    mut v_h__2_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1694_) == 0 {
        let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1697_);
        v___x_1698_ = leanh::lean_apply_1(v_h__1_1696_, v_x_1695_);
        return v___x_1698_;
    } else {
        let mut v_val_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1696_);
        v_val_1699_ = leanh::lean_ctor_get(v_x_1694_, 0);
        leanh::lean_inc(v_val_1699_);
        leanh::lean_dec_ref_known(v_x_1694_, 1);
        v___x_1700_ = leanh::lean_apply_2(v_h__2_1697_, v_val_1699_, v_x_1695_);
        return v___x_1700_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(
    mut v_00_u03b1_1701_: *mut leanh::LeanObject,
    mut v_00_u03b2_1702_: *mut leanh::LeanObject,
    mut v_motive_1703_: *mut leanh::LeanObject,
    mut v_x_1704_: *mut leanh::LeanObject,
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v_h__1_1706_: *mut leanh::LeanObject,
    mut v_h__2_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1704_) == 0 {
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1707_);
        v___x_1708_ = leanh::lean_apply_1(v_h__1_1706_, v_x_1705_);
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1706_);
        v_val_1709_ = leanh::lean_ctor_get(v_x_1704_, 0);
        leanh::lean_inc(v_val_1709_);
        leanh::lean_dec_ref_known(v_x_1704_, 1);
        v___x_1710_ = leanh::lean_apply_2(v_h__2_1707_, v_val_1709_, v_x_1705_);
        return v___x_1710_;
    }
}
pub unsafe fn l_Std_Internal_List_containsKey___redArg(
    mut v_inst_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_x_1713_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1714_: u8 = 0;
    let mut v_head_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1713_) == 0 {
                    leanh::lean_dec(v_a_1712_);
                    leanh::lean_dec_ref(v_inst_1711_);
                    v___x_1714_ = 0;
                    return v___x_1714_;
                } else {
                    v_head_1715_ = leanh::lean_ctor_get(v_x_1713_, 0);
                    leanh::lean_inc(v_head_1715_);
                    v_tail_1716_ = leanh::lean_ctor_get(v_x_1713_, 1);
                    leanh::lean_inc(v_tail_1716_);
                    leanh::lean_dec_ref_known(v_x_1713_, 2);
                    v_fst_1717_ = leanh::lean_ctor_get(v_head_1715_, 0);
                    leanh::lean_inc(v_fst_1717_);
                    leanh::lean_dec(v_head_1715_);
                    leanh::lean_inc_ref(v_inst_1711_);
                    leanh::lean_inc(v_a_1712_);
                    v___x_1718_ = leanh::lean_apply_2(v_inst_1711_, v_fst_1717_, v_a_1712_);
                    v___x_1719_ = (leanh::lean_unbox(v___x_1718_) as u8);
                    if v___x_1719_ == 0 {
                        v_x_1713_ = v_tail_1716_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1716_);
                        leanh::lean_dec(v_a_1712_);
                        leanh::lean_dec_ref(v_inst_1711_);
                        v___x_1721_ = (leanh::lean_unbox(v___x_1718_) as u8);
                        return v___x_1721_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_containsKey___redArg___boxed(
    mut v_inst_1722_: *mut leanh::LeanObject,
    mut v_a_1723_: *mut leanh::LeanObject,
    mut v_x_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1725_: u8 = 0;
    let mut v_r_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Std_Internal_List_containsKey___redArg(v_inst_1722_, v_a_1723_, v_x_1724_);
    v_r_1726_ = leanh::lean_box((v_res_1725_) as usize);
    return v_r_1726_;
}
pub unsafe fn l_Std_Internal_List_containsKey(
    mut v_00_u03b1_1727_: *mut leanh::LeanObject,
    mut v_00_u03b2_1728_: *mut leanh::LeanObject,
    mut v_inst_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_x_1731_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1732_: u8 = 0;
    v___x_1732_ = l_Std_Internal_List_containsKey___redArg(v_inst_1729_, v_a_1730_, v_x_1731_);
    return v___x_1732_;
}
pub unsafe fn l_Std_Internal_List_containsKey___boxed(
    mut v_00_u03b1_1733_: *mut leanh::LeanObject,
    mut v_00_u03b2_1734_: *mut leanh::LeanObject,
    mut v_inst_1735_: *mut leanh::LeanObject,
    mut v_a_1736_: *mut leanh::LeanObject,
    mut v_x_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1738_: u8 = 0;
    let mut v_r_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1738_ = l_Std_Internal_List_containsKey(
        v_00_u03b1_1733_,
        v_00_u03b2_1734_,
        v_inst_1735_,
        v_a_1736_,
        v_x_1737_,
    );
    v_r_1739_ = leanh::lean_box((v_res_1738_) as usize);
    return v_r_1739_;
}
pub unsafe fn l_Std_Internal_List_getEntry___redArg(
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_l_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1740_, v_a_1741_, v_l_1742_);
    v_val_1744_ = leanh::lean_ctor_get(v___x_1743_, 0);
    leanh::lean_inc(v_val_1744_);
    leanh::lean_dec(v___x_1743_);
    return v_val_1744_;
}
pub unsafe fn l_Std_Internal_List_getEntry(
    mut v_00_u03b1_1745_: *mut leanh::LeanObject,
    mut v_00_u03b2_1746_: *mut leanh::LeanObject,
    mut v_inst_1747_: *mut leanh::LeanObject,
    mut v_a_1748_: *mut leanh::LeanObject,
    mut v_l_1749_: *mut leanh::LeanObject,
    mut v_h_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Std_Internal_List_getEntry___redArg(v_inst_1747_, v_a_1748_, v_l_1749_);
    return v___x_1751_;
}
pub unsafe fn l_Std_Internal_List_getValue___redArg(
    mut v_inst_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
    mut v_l_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1752_, v_a_1753_, v_l_1754_);
    v_val_1756_ = leanh::lean_ctor_get(v___x_1755_, 0);
    leanh::lean_inc(v_val_1756_);
    leanh::lean_dec(v___x_1755_);
    return v_val_1756_;
}
pub unsafe fn l_Std_Internal_List_getValue(
    mut v_00_u03b1_1757_: *mut leanh::LeanObject,
    mut v_00_u03b2_1758_: *mut leanh::LeanObject,
    mut v_inst_1759_: *mut leanh::LeanObject,
    mut v_a_1760_: *mut leanh::LeanObject,
    mut v_l_1761_: *mut leanh::LeanObject,
    mut v_h_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Std_Internal_List_getValue___redArg(v_inst_1759_, v_a_1760_, v_l_1761_);
    return v___x_1763_;
}
pub unsafe fn l_Std_Internal_List_getValueCast___redArg(
    mut v_inst_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_l_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1764_, v_a_1765_, v_l_1766_);
    v_val_1768_ = leanh::lean_ctor_get(v___x_1767_, 0);
    leanh::lean_inc(v_val_1768_);
    leanh::lean_dec(v___x_1767_);
    return v_val_1768_;
}
pub unsafe fn l_Std_Internal_List_getValueCast(
    mut v_00_u03b1_1769_: *mut leanh::LeanObject,
    mut v_00_u03b2_1770_: *mut leanh::LeanObject,
    mut v_inst_1771_: *mut leanh::LeanObject,
    mut v_inst_1772_: *mut leanh::LeanObject,
    mut v_a_1773_: *mut leanh::LeanObject,
    mut v_l_1774_: *mut leanh::LeanObject,
    mut v_h_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = l_Std_Internal_List_getValueCast___redArg(v_inst_1771_, v_a_1773_, v_l_1774_);
    return v___x_1776_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD___redArg(
    mut v_inst_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_l_1779_: *mut leanh::LeanObject,
    mut v_fallback_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1777_, v_a_1778_, v_l_1779_);
    if leanh::lean_obj_tag(v___x_1781_) == 0 {
        leanh::lean_inc(v_fallback_1780_);
        return v_fallback_1780_;
    } else {
        let mut v_val_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1782_ = leanh::lean_ctor_get(v___x_1781_, 0);
        leanh::lean_inc(v_val_1782_);
        leanh::lean_dec_ref_known(v___x_1781_, 1);
        return v_val_1782_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCastD___redArg___boxed(
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_a_1784_: *mut leanh::LeanObject,
    mut v_l_1785_: *mut leanh::LeanObject,
    mut v_fallback_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_Internal_List_getValueCastD___redArg(
        v_inst_1783_,
        v_a_1784_,
        v_l_1785_,
        v_fallback_1786_,
    );
    leanh::lean_dec(v_fallback_1786_);
    return v_res_1787_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD(
    mut v_00_u03b1_1788_: *mut leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut leanh::LeanObject,
    mut v_inst_1790_: *mut leanh::LeanObject,
    mut v_inst_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_l_1793_: *mut leanh::LeanObject,
    mut v_fallback_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Std_Internal_List_getValueCastD___redArg(
        v_inst_1790_,
        v_a_1792_,
        v_l_1793_,
        v_fallback_1794_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Std_Internal_List_getValueCastD___boxed(
    mut v_00_u03b1_1796_: *mut leanh::LeanObject,
    mut v_00_u03b2_1797_: *mut leanh::LeanObject,
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
    mut v_l_1801_: *mut leanh::LeanObject,
    mut v_fallback_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1803_ = l_Std_Internal_List_getValueCastD(
        v_00_u03b1_1796_,
        v_00_u03b2_1797_,
        v_inst_1798_,
        v_inst_1799_,
        v_a_1800_,
        v_l_1801_,
        v_fallback_1802_,
    );
    leanh::lean_dec(v_fallback_1802_);
    return v_res_1803_;
}
pub unsafe fn _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Std_Internal_List_getValueCast_x21___redArg___closed__2;
    v___x_1808_ = leanh::lean_unsigned_to_nat(14);
    v___x_1809_ = leanh::lean_unsigned_to_nat(22);
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
    mut v_inst_1813_: *mut leanh::LeanObject,
    mut v_a_1814_: *mut leanh::LeanObject,
    mut v_inst_1815_: *mut leanh::LeanObject,
    mut v_l_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_1813_, v_a_1814_, v_l_1816_);
    if leanh::lean_obj_tag(v___x_1817_) == 0 {
        let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1818_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1819_ = l_panic___redArg(v_inst_1815_, v___x_1818_);
        return v___x_1819_;
    } else {
        let mut v_val_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1820_ = leanh::lean_ctor_get(v___x_1817_, 0);
        leanh::lean_inc(v_val_1820_);
        leanh::lean_dec_ref_known(v___x_1817_, 1);
        return v_val_1820_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21___redArg___boxed(
    mut v_inst_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_l_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_Std_Internal_List_getValueCast_x21___redArg(
        v_inst_1821_,
        v_a_1822_,
        v_inst_1823_,
        v_l_1824_,
    );
    leanh::lean_dec(v_inst_1823_);
    return v_res_1825_;
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21(
    mut v_00_u03b1_1826_: *mut leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut leanh::LeanObject,
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
    mut v_inst_1831_: *mut leanh::LeanObject,
    mut v_l_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Std_Internal_List_getValueCast_x21___redArg(
        v_inst_1828_,
        v_a_1830_,
        v_inst_1831_,
        v_l_1832_,
    );
    return v___x_1833_;
}
pub unsafe fn l_Std_Internal_List_getValueCast_x21___boxed(
    mut v_00_u03b1_1834_: *mut leanh::LeanObject,
    mut v_00_u03b2_1835_: *mut leanh::LeanObject,
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_inst_1839_: *mut leanh::LeanObject,
    mut v_l_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Std_Internal_List_getValueCast_x21(
        v_00_u03b1_1834_,
        v_00_u03b2_1835_,
        v_inst_1836_,
        v_inst_1837_,
        v_a_1838_,
        v_inst_1839_,
        v_l_1840_,
    );
    leanh::lean_dec(v_inst_1839_);
    return v_res_1841_;
}
pub unsafe fn l_Std_Internal_List_getValueD___redArg(
    mut v_inst_1842_: *mut leanh::LeanObject,
    mut v_a_1843_: *mut leanh::LeanObject,
    mut v_l_1844_: *mut leanh::LeanObject,
    mut v_fallback_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1842_, v_a_1843_, v_l_1844_);
    if leanh::lean_obj_tag(v___x_1846_) == 0 {
        leanh::lean_inc(v_fallback_1845_);
        return v_fallback_1845_;
    } else {
        let mut v_val_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1847_ = leanh::lean_ctor_get(v___x_1846_, 0);
        leanh::lean_inc(v_val_1847_);
        leanh::lean_dec_ref_known(v___x_1846_, 1);
        return v_val_1847_;
    }
}
pub unsafe fn l_Std_Internal_List_getValueD___redArg___boxed(
    mut v_inst_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_l_1850_: *mut leanh::LeanObject,
    mut v_fallback_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Std_Internal_List_getValueD___redArg(
        v_inst_1848_,
        v_a_1849_,
        v_l_1850_,
        v_fallback_1851_,
    );
    leanh::lean_dec(v_fallback_1851_);
    return v_res_1852_;
}
pub unsafe fn l_Std_Internal_List_getValueD(
    mut v_00_u03b1_1853_: *mut leanh::LeanObject,
    mut v_00_u03b2_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_l_1857_: *mut leanh::LeanObject,
    mut v_fallback_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Std_Internal_List_getValueD___redArg(
        v_inst_1855_,
        v_a_1856_,
        v_l_1857_,
        v_fallback_1858_,
    );
    return v___x_1859_;
}
pub unsafe fn l_Std_Internal_List_getValueD___boxed(
    mut v_00_u03b1_1860_: *mut leanh::LeanObject,
    mut v_00_u03b2_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_a_1863_: *mut leanh::LeanObject,
    mut v_l_1864_: *mut leanh::LeanObject,
    mut v_fallback_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_Internal_List_getValueD(
        v_00_u03b1_1860_,
        v_00_u03b2_1861_,
        v_inst_1862_,
        v_a_1863_,
        v_l_1864_,
        v_fallback_1865_,
    );
    leanh::lean_dec(v_fallback_1865_);
    return v_res_1866_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21___redArg(
    mut v_inst_1867_: *mut leanh::LeanObject,
    mut v_inst_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
    mut v_l_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_1867_, v_a_1869_, v_l_1870_);
    if leanh::lean_obj_tag(v___x_1871_) == 0 {
        let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1872_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1873_ = l_panic___redArg(v_inst_1868_, v___x_1872_);
        return v___x_1873_;
    } else {
        let mut v_val_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1874_ = leanh::lean_ctor_get(v___x_1871_, 0);
        leanh::lean_inc(v_val_1874_);
        leanh::lean_dec_ref_known(v___x_1871_, 1);
        return v_val_1874_;
    }
}
pub unsafe fn l_Std_Internal_List_getValue_x21___redArg___boxed(
    mut v_inst_1875_: *mut leanh::LeanObject,
    mut v_inst_1876_: *mut leanh::LeanObject,
    mut v_a_1877_: *mut leanh::LeanObject,
    mut v_l_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ =
        l_Std_Internal_List_getValue_x21___redArg(v_inst_1875_, v_inst_1876_, v_a_1877_, v_l_1878_);
    leanh::lean_dec(v_inst_1876_);
    return v_res_1879_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21(
    mut v_00_u03b1_1880_: *mut leanh::LeanObject,
    mut v_00_u03b2_1881_: *mut leanh::LeanObject,
    mut v_inst_1882_: *mut leanh::LeanObject,
    mut v_inst_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
    mut v_l_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ =
        l_Std_Internal_List_getValue_x21___redArg(v_inst_1882_, v_inst_1883_, v_a_1884_, v_l_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Std_Internal_List_getValue_x21___boxed(
    mut v_00_u03b1_1887_: *mut leanh::LeanObject,
    mut v_00_u03b2_1888_: *mut leanh::LeanObject,
    mut v_inst_1889_: *mut leanh::LeanObject,
    mut v_inst_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
    mut v_l_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Std_Internal_List_getValue_x21(
        v_00_u03b1_1887_,
        v_00_u03b2_1888_,
        v_inst_1889_,
        v_inst_1890_,
        v_a_1891_,
        v_l_1892_,
    );
    leanh::lean_dec(v_inst_1890_);
    return v_res_1893_;
}
pub unsafe fn l_Std_Internal_List_getKey_x3f___redArg(
    mut v_inst_1894_: *mut leanh::LeanObject,
    mut v_a_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1896_) == 0 {
                    leanh::lean_dec(v_a_1895_);
                    leanh::lean_dec_ref(v_inst_1894_);
                    v___x_1897_ = leanh::lean_box(0);
                    return v___x_1897_;
                } else {
                    v_head_1898_ = leanh::lean_ctor_get(v_x_1896_, 0);
                    leanh::lean_inc(v_head_1898_);
                    v_tail_1899_ = leanh::lean_ctor_get(v_x_1896_, 1);
                    leanh::lean_inc(v_tail_1899_);
                    leanh::lean_dec_ref_known(v_x_1896_, 2);
                    v_fst_1900_ = leanh::lean_ctor_get(v_head_1898_, 0);
                    leanh::lean_inc_n(v_fst_1900_, 2);
                    leanh::lean_dec(v_head_1898_);
                    leanh::lean_inc_ref(v_inst_1894_);
                    leanh::lean_inc(v_a_1895_);
                    v___x_1901_ = leanh::lean_apply_2(v_inst_1894_, v_fst_1900_, v_a_1895_);
                    v___x_1902_ = (leanh::lean_unbox(v___x_1901_) as u8);
                    if v___x_1902_ == 0 {
                        leanh::lean_dec(v_fst_1900_);
                        v_x_1896_ = v_tail_1899_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1899_);
                        leanh::lean_dec(v_a_1895_);
                        leanh::lean_dec_ref(v_inst_1894_);
                        v___x_1904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1904_, 0, v_fst_1900_);
                        return v___x_1904_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_getKey_x3f(
    mut v_00_u03b1_1905_: *mut leanh::LeanObject,
    mut v_00_u03b2_1906_: *mut leanh::LeanObject,
    mut v_inst_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_x_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1907_, v_a_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Std_Internal_List_getKey___redArg(
    mut v_inst_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_l_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1911_, v_a_1912_, v_l_1913_);
    v_val_1915_ = leanh::lean_ctor_get(v___x_1914_, 0);
    leanh::lean_inc(v_val_1915_);
    leanh::lean_dec(v___x_1914_);
    return v_val_1915_;
}
pub unsafe fn l_Std_Internal_List_getKey(
    mut v_00_u03b1_1916_: *mut leanh::LeanObject,
    mut v_00_u03b2_1917_: *mut leanh::LeanObject,
    mut v_inst_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
    mut v_l_1920_: *mut leanh::LeanObject,
    mut v_h_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Std_Internal_List_getKey___redArg(v_inst_1918_, v_a_1919_, v_l_1920_);
    return v___x_1922_;
}
pub unsafe fn l_Std_Internal_List_getKeyD___redArg(
    mut v_inst_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_l_1925_: *mut leanh::LeanObject,
    mut v_fallback_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1923_, v_a_1924_, v_l_1925_);
    if leanh::lean_obj_tag(v___x_1927_) == 0 {
        leanh::lean_inc(v_fallback_1926_);
        return v_fallback_1926_;
    } else {
        let mut v_val_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1928_ = leanh::lean_ctor_get(v___x_1927_, 0);
        leanh::lean_inc(v_val_1928_);
        leanh::lean_dec_ref_known(v___x_1927_, 1);
        return v_val_1928_;
    }
}
pub unsafe fn l_Std_Internal_List_getKeyD___redArg___boxed(
    mut v_inst_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_l_1931_: *mut leanh::LeanObject,
    mut v_fallback_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ =
        l_Std_Internal_List_getKeyD___redArg(v_inst_1929_, v_a_1930_, v_l_1931_, v_fallback_1932_);
    leanh::lean_dec(v_fallback_1932_);
    return v_res_1933_;
}
pub unsafe fn l_Std_Internal_List_getKeyD(
    mut v_00_u03b1_1934_: *mut leanh::LeanObject,
    mut v_00_u03b2_1935_: *mut leanh::LeanObject,
    mut v_inst_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
    mut v_l_1938_: *mut leanh::LeanObject,
    mut v_fallback_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ =
        l_Std_Internal_List_getKeyD___redArg(v_inst_1936_, v_a_1937_, v_l_1938_, v_fallback_1939_);
    return v___x_1940_;
}
pub unsafe fn l_Std_Internal_List_getKeyD___boxed(
    mut v_00_u03b1_1941_: *mut leanh::LeanObject,
    mut v_00_u03b2_1942_: *mut leanh::LeanObject,
    mut v_inst_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_l_1945_: *mut leanh::LeanObject,
    mut v_fallback_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Std_Internal_List_getKeyD(
        v_00_u03b1_1941_,
        v_00_u03b2_1942_,
        v_inst_1943_,
        v_a_1944_,
        v_l_1945_,
        v_fallback_1946_,
    );
    leanh::lean_dec(v_fallback_1946_);
    return v_res_1947_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21___redArg(
    mut v_inst_1948_: *mut leanh::LeanObject,
    mut v_inst_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_l_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_1948_, v_a_1950_, v_l_1951_);
    if leanh::lean_obj_tag(v___x_1952_) == 0 {
        let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1953_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_1954_ = l_panic___redArg(v_inst_1949_, v___x_1953_);
        return v___x_1954_;
    } else {
        let mut v_val_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1955_ = leanh::lean_ctor_get(v___x_1952_, 0);
        leanh::lean_inc(v_val_1955_);
        leanh::lean_dec_ref_known(v___x_1952_, 1);
        return v_val_1955_;
    }
}
pub unsafe fn l_Std_Internal_List_getKey_x21___redArg___boxed(
    mut v_inst_1956_: *mut leanh::LeanObject,
    mut v_inst_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
    mut v_l_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ =
        l_Std_Internal_List_getKey_x21___redArg(v_inst_1956_, v_inst_1957_, v_a_1958_, v_l_1959_);
    leanh::lean_dec(v_inst_1957_);
    return v_res_1960_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21(
    mut v_00_u03b1_1961_: *mut leanh::LeanObject,
    mut v_00_u03b2_1962_: *mut leanh::LeanObject,
    mut v_inst_1963_: *mut leanh::LeanObject,
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
    mut v_l_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ =
        l_Std_Internal_List_getKey_x21___redArg(v_inst_1963_, v_inst_1964_, v_a_1965_, v_l_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Std_Internal_List_getKey_x21___boxed(
    mut v_00_u03b1_1968_: *mut leanh::LeanObject,
    mut v_00_u03b2_1969_: *mut leanh::LeanObject,
    mut v_inst_1970_: *mut leanh::LeanObject,
    mut v_inst_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_l_1973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1974_ = l_Std_Internal_List_getKey_x21(
        v_00_u03b1_1968_,
        v_00_u03b2_1969_,
        v_inst_1970_,
        v_inst_1971_,
        v_a_1972_,
        v_l_1973_,
    );
    leanh::lean_dec(v_inst_1971_);
    return v_res_1974_;
}
pub unsafe fn l_Std_Internal_List_replaceEntry___redArg(
    mut v_inst_1975_: *mut leanh::LeanObject,
    mut v_k_1976_: *mut leanh::LeanObject,
    mut v_v_1977_: *mut leanh::LeanObject,
    mut v_x_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v_fst_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_unused_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1978_) == 0 {
                    leanh::lean_dec(v_v_1977_);
                    leanh::lean_dec(v_k_1976_);
                    leanh::lean_dec_ref(v_inst_1975_);
                    v___x_1979_ = leanh::lean_box(0);
                    return v___x_1979_;
                } else {
                    v_head_1980_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_tail_1981_ = leanh::lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2004_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1983_ = v_x_1978_;
                        v_isShared_1984_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1981_);
                        leanh::lean_inc(v_head_1980_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_1983_ = leanh::lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1985_ = leanh::lean_ctor_get(v_head_1980_, 0);
                leanh::lean_inc_ref(v_inst_1975_);
                leanh::lean_inc(v_k_1976_);
                leanh::lean_inc(v_fst_1985_);
                v___x_1986_ = leanh::lean_apply_2(v_inst_1975_, v_fst_1985_, v_k_1976_);
                v___x_1987_ = (leanh::lean_unbox(v___x_1986_) as u8);
                if v___x_1987_ == 0 {
                    v___x_1988_ = l_Std_Internal_List_replaceEntry___redArg(
                        v_inst_1975_,
                        v_k_1976_,
                        v_v_1977_,
                        v_tail_1981_,
                    );
                    if v_isShared_1984_ == 0 {
                        leanh::lean_ctor_set(v___x_1983_, 1, v___x_1988_);
                        v___x_1990_ = v___x_1983_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1991_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_head_1980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1988_);
                        v___x_1990_ = v_reuseFailAlloc_1991_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1975_);
                    v_isSharedCheck_2001_ = (!leanh::lean_is_exclusive(v_head_1980_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v_unused_2002_ = leanh::lean_ctor_get(v_head_1980_, 1);
                        leanh::lean_dec(v_unused_2002_);
                        v_unused_2003_ = leanh::lean_ctor_get(v_head_1980_, 0);
                        leanh::lean_dec(v_unused_2003_);
                        v___x_1993_ = v_head_1980_;
                        v_isShared_1994_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1980_);
                        v___x_1993_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1993_, 1, v_v_1977_);
                    leanh::lean_ctor_set(v___x_1993_, 0, v_k_1976_);
                    v___x_1996_ = v___x_1993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_k_1976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_v_1977_);
                    v___x_1996_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1984_ == 0 {
                    leanh::lean_ctor_set(v___x_1983_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1983_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_tail_1981_);
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
    mut v_00_u03b1_2005_: *mut leanh::LeanObject,
    mut v_00_u03b2_2006_: *mut leanh::LeanObject,
    mut v_inst_2007_: *mut leanh::LeanObject,
    mut v_k_2008_: *mut leanh::LeanObject,
    mut v_v_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ =
        l_Std_Internal_List_replaceEntry___redArg(v_inst_2007_, v_k_2008_, v_v_2009_, v_x_2010_);
    return v___x_2011_;
}
pub unsafe fn l_Std_Internal_List_eraseKey___redArg(
    mut v_inst_2012_: *mut leanh::LeanObject,
    mut v_k_2013_: *mut leanh::LeanObject,
    mut v_x_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v_fst_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2014_) == 0 {
                    leanh::lean_dec(v_k_2013_);
                    leanh::lean_dec_ref(v_inst_2012_);
                    v___x_2015_ = leanh::lean_box(0);
                    return v___x_2015_;
                } else {
                    v_head_2016_ = leanh::lean_ctor_get(v_x_2014_, 0);
                    v_tail_2017_ = leanh::lean_ctor_get(v_x_2014_, 1);
                    v_isSharedCheck_2028_ = (!leanh::lean_is_exclusive(v_x_2014_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_2019_ = v_x_2014_;
                        v_isShared_2020_ = v_isSharedCheck_2028_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2017_);
                        leanh::lean_inc(v_head_2016_);
                        leanh::lean_dec(v_x_2014_);
                        v___x_2019_ = leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2028_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2021_ = leanh::lean_ctor_get(v_head_2016_, 0);
                leanh::lean_inc_ref(v_inst_2012_);
                leanh::lean_inc(v_k_2013_);
                leanh::lean_inc(v_fst_2021_);
                v___x_2022_ = leanh::lean_apply_2(v_inst_2012_, v_fst_2021_, v_k_2013_);
                v___x_2023_ = (leanh::lean_unbox(v___x_2022_) as u8);
                if v___x_2023_ == 0 {
                    v___x_2024_ = l_Std_Internal_List_eraseKey___redArg(
                        v_inst_2012_,
                        v_k_2013_,
                        v_tail_2017_,
                    );
                    if v_isShared_2020_ == 0 {
                        leanh::lean_ctor_set(v___x_2019_, 1, v___x_2024_);
                        v___x_2026_ = v___x_2019_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2027_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_head_2016_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
                        v___x_2026_ = v_reuseFailAlloc_2027_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2019_);
                    leanh::lean_dec(v_head_2016_);
                    leanh::lean_dec(v_k_2013_);
                    leanh::lean_dec_ref(v_inst_2012_);
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
    mut v_00_u03b1_2029_: *mut leanh::LeanObject,
    mut v_00_u03b2_2030_: *mut leanh::LeanObject,
    mut v_inst_2031_: *mut leanh::LeanObject,
    mut v_k_2032_: *mut leanh::LeanObject,
    mut v_x_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2031_, v_k_2032_, v_x_2033_);
    return v___x_2034_;
}
pub unsafe fn l_Std_Internal_List_insertEntry___redArg(
    mut v_inst_2035_: *mut leanh::LeanObject,
    mut v_k_2036_: *mut leanh::LeanObject,
    mut v_v_2037_: *mut leanh::LeanObject,
    mut v_l_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2039_: u8 = 0;
    leanh::lean_inc(v_l_2038_);
    leanh::lean_inc(v_k_2036_);
    leanh::lean_inc_ref(v_inst_2035_);
    v___x_2039_ = l_Std_Internal_List_containsKey___redArg(v_inst_2035_, v_k_2036_, v_l_2038_);
    if v___x_2039_ == 0 {
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2035_);
        v___x_2040_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2040_, 0, v_k_2036_);
        leanh::lean_ctor_set(v___x_2040_, 1, v_v_2037_);
        v___x_2041_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2041_, 0, v___x_2040_);
        leanh::lean_ctor_set(v___x_2041_, 1, v_l_2038_);
        return v___x_2041_;
    } else {
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2043_: *mut leanh::LeanObject,
    mut v_00_u03b2_2044_: *mut leanh::LeanObject,
    mut v_inst_2045_: *mut leanh::LeanObject,
    mut v_k_2046_: *mut leanh::LeanObject,
    mut v_v_2047_: *mut leanh::LeanObject,
    mut v_l_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_Std_Internal_List_insertEntry___redArg(v_inst_2045_, v_k_2046_, v_v_2047_, v_l_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Std_Internal_List_insertEntryIfNew___redArg(
    mut v_inst_2050_: *mut leanh::LeanObject,
    mut v_k_2051_: *mut leanh::LeanObject,
    mut v_v_2052_: *mut leanh::LeanObject,
    mut v_l_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2054_: u8 = 0;
    leanh::lean_inc(v_l_2053_);
    leanh::lean_inc(v_k_2051_);
    v___x_2054_ = l_Std_Internal_List_containsKey___redArg(v_inst_2050_, v_k_2051_, v_l_2053_);
    if v___x_2054_ == 0 {
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2055_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2055_, 0, v_k_2051_);
        leanh::lean_ctor_set(v___x_2055_, 1, v_v_2052_);
        v___x_2056_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2056_, 0, v___x_2055_);
        leanh::lean_ctor_set(v___x_2056_, 1, v_l_2053_);
        return v___x_2056_;
    } else {
        leanh::lean_dec(v_v_2052_);
        leanh::lean_dec(v_k_2051_);
        return v_l_2053_;
    }
}
pub unsafe fn l_Std_Internal_List_insertEntryIfNew(
    mut v_00_u03b1_2057_: *mut leanh::LeanObject,
    mut v_00_u03b2_2058_: *mut leanh::LeanObject,
    mut v_inst_2059_: *mut leanh::LeanObject,
    mut v_k_2060_: *mut leanh::LeanObject,
    mut v_v_2061_: *mut leanh::LeanObject,
    mut v_l_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l_Std_Internal_List_insertEntryIfNew___redArg(
        v_inst_2059_,
        v_k_2060_,
        v_v_2061_,
        v_l_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_2064_: *mut leanh::LeanObject,
    mut v_h__1_2065_: *mut leanh::LeanObject,
    mut v_h__2_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2064_) == 0 {
        let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2066_);
        v___x_2067_ = leanh::lean_box(0);
        v___x_2068_ = leanh::lean_apply_1(v_h__1_2065_, v___x_2067_);
        return v___x_2068_;
    } else {
        let mut v_val_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2065_);
        v_val_2069_ = leanh::lean_ctor_get(v_x_2064_, 0);
        leanh::lean_inc(v_val_2069_);
        leanh::lean_dec_ref_known(v_x_2064_, 1);
        v___x_2070_ = leanh::lean_apply_1(v_h__2_2066_, v_val_2069_);
        return v___x_2070_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_2071_: *mut leanh::LeanObject,
    mut v_motive_2072_: *mut leanh::LeanObject,
    mut v_x_2073_: *mut leanh::LeanObject,
    mut v_h__1_2074_: *mut leanh::LeanObject,
    mut v_h__2_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2073_) == 0 {
        let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2075_);
        v___x_2076_ = leanh::lean_box(0);
        v___x_2077_ = leanh::lean_apply_1(v_h__1_2074_, v___x_2076_);
        return v___x_2077_;
    } else {
        let mut v_val_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2074_);
        v_val_2078_ = leanh::lean_ctor_get(v_x_2073_, 0);
        leanh::lean_inc(v_val_2078_);
        leanh::lean_dec_ref_known(v_x_2073_, 1);
        v___x_2079_ = leanh::lean_apply_1(v_h__2_2075_, v_val_2078_);
        return v___x_2079_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_2080_: *mut leanh::LeanObject,
    mut v_h__1_2081_: *mut leanh::LeanObject,
    mut v_h__2_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2080_) == 0 {
        let mut v_a_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2082_);
        v_a_2083_ = leanh::lean_ctor_get(v_x_2080_, 0);
        leanh::lean_inc(v_a_2083_);
        leanh::lean_dec_ref_known(v_x_2080_, 1);
        v___x_2084_ = leanh::lean_apply_1(v_h__1_2081_, v_a_2083_);
        return v___x_2084_;
    } else {
        let mut v_a_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2081_);
        v_a_2085_ = leanh::lean_ctor_get(v_x_2080_, 0);
        leanh::lean_inc(v_a_2085_);
        leanh::lean_dec_ref_known(v_x_2080_, 1);
        v___x_2086_ = leanh::lean_apply_1(v_h__2_2082_, v_a_2085_);
        return v___x_2086_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_2087_: *mut leanh::LeanObject,
    mut v_motive_2088_: *mut leanh::LeanObject,
    mut v_x_2089_: *mut leanh::LeanObject,
    mut v_h__1_2090_: *mut leanh::LeanObject,
    mut v_h__2_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2089_) == 0 {
        let mut v_a_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2091_);
        v_a_2092_ = leanh::lean_ctor_get(v_x_2089_, 0);
        leanh::lean_inc(v_a_2092_);
        leanh::lean_dec_ref_known(v_x_2089_, 1);
        v___x_2093_ = leanh::lean_apply_1(v_h__1_2090_, v_a_2092_);
        return v___x_2093_;
    } else {
        let mut v_a_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2090_);
        v_a_2094_ = leanh::lean_ctor_get(v_x_2089_, 0);
        leanh::lean_inc(v_a_2094_);
        leanh::lean_dec_ref_known(v_x_2089_, 1);
        v___x_2095_ = leanh::lean_apply_1(v_h__2_2091_, v_a_2094_);
        return v___x_2095_;
    }
}
pub unsafe fn l_Std_Internal_List_insertList___redArg(
    mut v_inst_2096_: *mut leanh::LeanObject,
    mut v_l_2097_: *mut leanh::LeanObject,
    mut v_toInsert_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_toInsert_2098_) == 0 {
                    leanh::lean_dec_ref(v_inst_2096_);
                    return v_l_2097_;
                } else {
                    v_head_2099_ = leanh::lean_ctor_get(v_toInsert_2098_, 0);
                    leanh::lean_inc(v_head_2099_);
                    v_tail_2100_ = leanh::lean_ctor_get(v_toInsert_2098_, 1);
                    leanh::lean_inc(v_tail_2100_);
                    leanh::lean_dec_ref_known(v_toInsert_2098_, 2);
                    v_fst_2101_ = leanh::lean_ctor_get(v_head_2099_, 0);
                    leanh::lean_inc(v_fst_2101_);
                    v_snd_2102_ = leanh::lean_ctor_get(v_head_2099_, 1);
                    leanh::lean_inc(v_snd_2102_);
                    leanh::lean_dec(v_head_2099_);
                    leanh::lean_inc_ref(v_inst_2096_);
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
    mut v_00_u03b1_2105_: *mut leanh::LeanObject,
    mut v_00_u03b2_2106_: *mut leanh::LeanObject,
    mut v_inst_2107_: *mut leanh::LeanObject,
    mut v_l_2108_: *mut leanh::LeanObject,
    mut v_toInsert_2109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ =
        l_Std_Internal_List_insertList___redArg(v_inst_2107_, v_l_2108_, v_toInsert_2109_);
    return v___x_2110_;
}
pub unsafe fn l_Std_Internal_List_insertListIfNew___redArg(
    mut v_inst_2111_: *mut leanh::LeanObject,
    mut v_l_2112_: *mut leanh::LeanObject,
    mut v_toInsert_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_toInsert_2113_) == 0 {
                    leanh::lean_dec_ref(v_inst_2111_);
                    return v_l_2112_;
                } else {
                    v_head_2114_ = leanh::lean_ctor_get(v_toInsert_2113_, 0);
                    leanh::lean_inc(v_head_2114_);
                    v_tail_2115_ = leanh::lean_ctor_get(v_toInsert_2113_, 1);
                    leanh::lean_inc(v_tail_2115_);
                    leanh::lean_dec_ref_known(v_toInsert_2113_, 2);
                    v_fst_2116_ = leanh::lean_ctor_get(v_head_2114_, 0);
                    leanh::lean_inc(v_fst_2116_);
                    v_snd_2117_ = leanh::lean_ctor_get(v_head_2114_, 1);
                    leanh::lean_inc(v_snd_2117_);
                    leanh::lean_dec(v_head_2114_);
                    leanh::lean_inc_ref(v_inst_2111_);
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
    mut v_00_u03b1_2120_: *mut leanh::LeanObject,
    mut v_00_u03b2_2121_: *mut leanh::LeanObject,
    mut v_inst_2122_: *mut leanh::LeanObject,
    mut v_l_2123_: *mut leanh::LeanObject,
    mut v_toInsert_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ =
        l_Std_Internal_List_insertListIfNew___redArg(v_inst_2122_, v_l_2123_, v_toInsert_2124_);
    return v___x_2125_;
}
pub unsafe fn l_Std_Internal_List_insertSmallerList___redArg(
    mut v_inst_2126_: *mut leanh::LeanObject,
    mut v_l_u2081_2127_: *mut leanh::LeanObject,
    mut v_l_u2082_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    v___x_2129_ = l_List_lengthTR___redArg(v_l_u2081_2127_);
    v___x_2130_ = l_List_lengthTR___redArg(v_l_u2082_2128_);
    v___x_2131_ = lean_nat_dec_le(v___x_2129_, v___x_2130_);
    leanh::lean_dec(v___x_2130_);
    leanh::lean_dec(v___x_2129_);
    if v___x_2131_ == 0 {
        let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2132_ =
            l_Std_Internal_List_insertList___redArg(v_inst_2126_, v_l_u2081_2127_, v_l_u2082_2128_);
        return v___x_2132_;
    } else {
        let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2133_ = l_Std_Internal_List_insertListIfNew___redArg(
            v_inst_2126_,
            v_l_u2082_2128_,
            v_l_u2081_2127_,
        );
        return v___x_2133_;
    }
}
pub unsafe fn l_Std_Internal_List_insertSmallerList(
    mut v_00_u03b1_2134_: *mut leanh::LeanObject,
    mut v_00_u03b2_2135_: *mut leanh::LeanObject,
    mut v_inst_2136_: *mut leanh::LeanObject,
    mut v_l_u2081_2137_: *mut leanh::LeanObject,
    mut v_l_u2082_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = l_Std_Internal_List_insertSmallerList___redArg(
        v_inst_2136_,
        v_l_u2081_2137_,
        v_l_u2082_2138_,
    );
    return v___x_2139_;
}
pub unsafe fn l_Std_Internal_List_Prod_toSigma___redArg(
    mut v_p_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2145_: u8 = 0;
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2141_ = leanh::lean_ctor_get(v_p_2140_, 0);
                v_snd_2142_ = leanh::lean_ctor_get(v_p_2140_, 1);
                v_isSharedCheck_2149_ = (!leanh::lean_is_exclusive(v_p_2140_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2144_ = v_p_2140_;
                    v_isShared_2145_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2142_);
                    leanh::lean_inc(v_fst_2141_);
                    leanh::lean_dec(v_p_2140_);
                    v___x_2144_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2148_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_fst_2141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_snd_2142_);
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
    mut v_00_u03b1_2150_: *mut leanh::LeanObject,
    mut v_00_u03b2_2151_: *mut leanh::LeanObject,
    mut v_p_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_2152_);
    return v___x_2153_;
}
pub unsafe fn l_Std_Internal_List_insertListConst___redArg(
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_l_2156_: *mut leanh::LeanObject,
    mut v_toInsert_2157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2158_ = l_Std_Internal_List_insertListConst___redArg___closed__0;
    v___x_2159_ = leanh::lean_box(0);
    v___x_2160_ = l_List_mapTR_loop___redArg(v___x_2158_, v_toInsert_2157_, v___x_2159_);
    v___x_2161_ = l_Std_Internal_List_insertList___redArg(v_inst_2155_, v_l_2156_, v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_Internal_List_insertListConst(
    mut v_00_u03b1_2162_: *mut leanh::LeanObject,
    mut v_00_u03b2_2163_: *mut leanh::LeanObject,
    mut v_inst_2164_: *mut leanh::LeanObject,
    mut v_l_2165_: *mut leanh::LeanObject,
    mut v_toInsert_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2167_ =
        l_Std_Internal_List_insertListConst___redArg(v_inst_2164_, v_l_2165_, v_toInsert_2166_);
    return v___x_2167_;
}
pub unsafe fn l_Std_Internal_List_insertListIfNewUnit___redArg(
    mut v_inst_2168_: *mut leanh::LeanObject,
    mut v_l_2169_: *mut leanh::LeanObject,
    mut v_toInsert_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_toInsert_2170_) == 0 {
                    leanh::lean_dec_ref(v_inst_2168_);
                    return v_l_2169_;
                } else {
                    v_head_2171_ = leanh::lean_ctor_get(v_toInsert_2170_, 0);
                    leanh::lean_inc(v_head_2171_);
                    v_tail_2172_ = leanh::lean_ctor_get(v_toInsert_2170_, 1);
                    leanh::lean_inc(v_tail_2172_);
                    leanh::lean_dec_ref_known(v_toInsert_2170_, 2);
                    v___x_2173_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_inst_2168_);
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
    mut v_00_u03b1_2176_: *mut leanh::LeanObject,
    mut v_inst_2177_: *mut leanh::LeanObject,
    mut v_l_2178_: *mut leanh::LeanObject,
    mut v_toInsert_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ =
        l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_2177_, v_l_2178_, v_toInsert_2179_);
    return v___x_2180_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(
    mut v_toInsert_2181_: *mut leanh::LeanObject,
    mut v_h__1_2182_: *mut leanh::LeanObject,
    mut v_h__2_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_toInsert_2181_) == 0 {
        let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2183_);
        v___x_2184_ = leanh::lean_box(0);
        v___x_2185_ = leanh::lean_apply_1(v_h__1_2182_, v___x_2184_);
        return v___x_2185_;
    } else {
        let mut v_head_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2182_);
        v_head_2186_ = leanh::lean_ctor_get(v_toInsert_2181_, 0);
        leanh::lean_inc(v_head_2186_);
        v_tail_2187_ = leanh::lean_ctor_get(v_toInsert_2181_, 1);
        leanh::lean_inc(v_tail_2187_);
        leanh::lean_dec_ref_known(v_toInsert_2181_, 2);
        v___x_2188_ = leanh::lean_apply_2(v_h__2_2183_, v_head_2186_, v_tail_2187_);
        return v___x_2188_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(
    mut v_00_u03b1_2189_: *mut leanh::LeanObject,
    mut v_motive_2190_: *mut leanh::LeanObject,
    mut v_toInsert_2191_: *mut leanh::LeanObject,
    mut v_h__1_2192_: *mut leanh::LeanObject,
    mut v_h__2_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_toInsert_2191_) == 0 {
        let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2193_);
        v___x_2194_ = leanh::lean_box(0);
        v___x_2195_ = leanh::lean_apply_1(v_h__1_2192_, v___x_2194_);
        return v___x_2195_;
    } else {
        let mut v_head_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2192_);
        v_head_2196_ = leanh::lean_ctor_get(v_toInsert_2191_, 0);
        leanh::lean_inc(v_head_2196_);
        v_tail_2197_ = leanh::lean_ctor_get(v_toInsert_2191_, 1);
        leanh::lean_inc(v_tail_2197_);
        leanh::lean_dec_ref_known(v_toInsert_2191_, 2);
        v___x_2198_ = leanh::lean_apply_2(v_h__2_2193_, v_head_2196_, v_tail_2197_);
        return v___x_2198_;
    }
}
pub unsafe fn l_Std_Internal_List_alterKey___redArg(
    mut v_inst_2199_: *mut leanh::LeanObject,
    mut v_k_2200_: *mut leanh::LeanObject,
    mut v_f_2201_: *mut leanh::LeanObject,
    mut v_l_2202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_l_2202_);
    leanh::lean_inc(v_k_2200_);
    leanh::lean_inc_ref(v_inst_2199_);
    v___x_2203_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_2199_, v_k_2200_, v_l_2202_);
    v___x_2204_ = leanh::lean_apply_1(v_f_2201_, v___x_2203_);
    if leanh::lean_obj_tag(v___x_2204_) == 0 {
        let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2205_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2199_, v_k_2200_, v_l_2202_);
        return v___x_2205_;
    } else {
        let mut v_val_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2206_ = leanh::lean_ctor_get(v___x_2204_, 0);
        leanh::lean_inc(v_val_2206_);
        leanh::lean_dec_ref_known(v___x_2204_, 1);
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
    mut v_00_u03b1_2208_: *mut leanh::LeanObject,
    mut v_00_u03b2_2209_: *mut leanh::LeanObject,
    mut v_inst_2210_: *mut leanh::LeanObject,
    mut v_inst_2211_: *mut leanh::LeanObject,
    mut v_k_2212_: *mut leanh::LeanObject,
    mut v_f_2213_: *mut leanh::LeanObject,
    mut v_l_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2215_ =
        l_Std_Internal_List_alterKey___redArg(v_inst_2210_, v_k_2212_, v_f_2213_, v_l_2214_);
    return v___x_2215_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(
    mut v_x_2216_: *mut leanh::LeanObject,
    mut v_h__1_2217_: *mut leanh::LeanObject,
    mut v_h__2_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2216_) == 0 {
        let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2218_);
        v___x_2219_ = leanh::lean_box(0);
        v___x_2220_ = leanh::lean_apply_1(v_h__1_2217_, v___x_2219_);
        return v___x_2220_;
    } else {
        let mut v_val_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2217_);
        v_val_2221_ = leanh::lean_ctor_get(v_x_2216_, 0);
        leanh::lean_inc(v_val_2221_);
        leanh::lean_dec_ref_known(v_x_2216_, 1);
        v___x_2222_ = leanh::lean_apply_1(v_h__2_2218_, v_val_2221_);
        return v___x_2222_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(
    mut v_00_u03b1_2223_: *mut leanh::LeanObject,
    mut v_00_u03b2_2224_: *mut leanh::LeanObject,
    mut v_k_2225_: *mut leanh::LeanObject,
    mut v_motive_2226_: *mut leanh::LeanObject,
    mut v_x_2227_: *mut leanh::LeanObject,
    mut v_h__1_2228_: *mut leanh::LeanObject,
    mut v_h__2_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2227_) == 0 {
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2229_);
        v___x_2230_ = leanh::lean_box(0);
        v___x_2231_ = leanh::lean_apply_1(v_h__1_2228_, v___x_2230_);
        return v___x_2231_;
    } else {
        let mut v_val_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2228_);
        v_val_2232_ = leanh::lean_ctor_get(v_x_2227_, 0);
        leanh::lean_inc(v_val_2232_);
        leanh::lean_dec_ref_known(v_x_2227_, 1);
        v___x_2233_ = leanh::lean_apply_1(v_h__2_2229_, v_val_2232_);
        return v___x_2233_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(
    mut v_00_u03b1_2234_: *mut leanh::LeanObject,
    mut v_00_u03b2_2235_: *mut leanh::LeanObject,
    mut v_k_2236_: *mut leanh::LeanObject,
    mut v_motive_2237_: *mut leanh::LeanObject,
    mut v_x_2238_: *mut leanh::LeanObject,
    mut v_h__1_2239_: *mut leanh::LeanObject,
    mut v_h__2_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2241_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_2234_, v_00_u03b2_2235_, v_k_2236_, v_motive_2237_, v_x_2238_, v_h__1_2239_, v_h__2_2240_);
    leanh::lean_dec(v_k_2236_);
    return v_res_2241_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_2242_: *mut leanh::LeanObject,
    mut v_h__1_2243_: *mut leanh::LeanObject,
    mut v_h__2_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2242_) == 0 {
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2244_);
        v___x_2245_ = leanh::lean_box(0);
        v___x_2246_ = leanh::lean_apply_1(v_h__1_2243_, v___x_2245_);
        return v___x_2246_;
    } else {
        let mut v_val_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2243_);
        v_val_2247_ = leanh::lean_ctor_get(v_x_2242_, 0);
        leanh::lean_inc(v_val_2247_);
        leanh::lean_dec_ref_known(v_x_2242_, 1);
        v___x_2248_ = leanh::lean_apply_1(v_h__2_2244_, v_val_2247_);
        return v___x_2248_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_2249_: *mut leanh::LeanObject,
    mut v_00_u03b2_2250_: *mut leanh::LeanObject,
    mut v_k_2251_: *mut leanh::LeanObject,
    mut v_motive_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
    mut v_h__1_2254_: *mut leanh::LeanObject,
    mut v_h__2_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2253_) == 0 {
        let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2255_);
        v___x_2256_ = leanh::lean_box(0);
        v___x_2257_ = leanh::lean_apply_1(v_h__1_2254_, v___x_2256_);
        return v___x_2257_;
    } else {
        let mut v_val_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2254_);
        v_val_2258_ = leanh::lean_ctor_get(v_x_2253_, 0);
        leanh::lean_inc(v_val_2258_);
        leanh::lean_dec_ref_known(v_x_2253_, 1);
        v___x_2259_ = leanh::lean_apply_1(v_h__2_2255_, v_val_2258_);
        return v___x_2259_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_2260_: *mut leanh::LeanObject,
    mut v_00_u03b2_2261_: *mut leanh::LeanObject,
    mut v_k_2262_: *mut leanh::LeanObject,
    mut v_motive_2263_: *mut leanh::LeanObject,
    mut v_x_2264_: *mut leanh::LeanObject,
    mut v_h__1_2265_: *mut leanh::LeanObject,
    mut v_h__2_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_2260_, v_00_u03b2_2261_, v_k_2262_, v_motive_2263_, v_x_2264_, v_h__1_2265_, v_h__2_2266_);
    leanh::lean_dec(v_k_2262_);
    return v_res_2267_;
}
pub unsafe fn l_Std_Internal_List_Const_alterKey___redArg(
    mut v_inst_2268_: *mut leanh::LeanObject,
    mut v_k_2269_: *mut leanh::LeanObject,
    mut v_f_2270_: *mut leanh::LeanObject,
    mut v_l_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_l_2271_);
    leanh::lean_inc(v_k_2269_);
    leanh::lean_inc_ref(v_inst_2268_);
    v___x_2272_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_2268_, v_k_2269_, v_l_2271_);
    v___x_2273_ = leanh::lean_apply_1(v_f_2270_, v___x_2272_);
    if leanh::lean_obj_tag(v___x_2273_) == 0 {
        let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2274_ = l_Std_Internal_List_eraseKey___redArg(v_inst_2268_, v_k_2269_, v_l_2271_);
        return v___x_2274_;
    } else {
        let mut v_val_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2275_ = leanh::lean_ctor_get(v___x_2273_, 0);
        leanh::lean_inc(v_val_2275_);
        leanh::lean_dec_ref_known(v___x_2273_, 1);
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
    mut v_00_u03b1_2277_: *mut leanh::LeanObject,
    mut v_00_u03b2_2278_: *mut leanh::LeanObject,
    mut v_inst_2279_: *mut leanh::LeanObject,
    mut v_k_2280_: *mut leanh::LeanObject,
    mut v_f_2281_: *mut leanh::LeanObject,
    mut v_l_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ =
        l_Std_Internal_List_Const_alterKey___redArg(v_inst_2279_, v_k_2280_, v_f_2281_, v_l_2282_);
    return v___x_2283_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(
    mut v_x_2284_: *mut leanh::LeanObject,
    mut v_h__1_2285_: *mut leanh::LeanObject,
    mut v_h__2_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2284_) == 0 {
        let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2286_);
        v___x_2287_ = leanh::lean_box(0);
        v___x_2288_ = leanh::lean_apply_1(v_h__1_2285_, v___x_2287_);
        return v___x_2288_;
    } else {
        let mut v_val_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2285_);
        v_val_2289_ = leanh::lean_ctor_get(v_x_2284_, 0);
        leanh::lean_inc(v_val_2289_);
        leanh::lean_dec_ref_known(v_x_2284_, 1);
        v___x_2290_ = leanh::lean_apply_1(v_h__2_2286_, v_val_2289_);
        return v___x_2290_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(
    mut v_00_u03b2_2291_: *mut leanh::LeanObject,
    mut v_motive_2292_: *mut leanh::LeanObject,
    mut v_x_2293_: *mut leanh::LeanObject,
    mut v_h__1_2294_: *mut leanh::LeanObject,
    mut v_h__2_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2293_) == 0 {
        let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2295_);
        v___x_2296_ = leanh::lean_box(0);
        v___x_2297_ = leanh::lean_apply_1(v_h__1_2294_, v___x_2296_);
        return v___x_2297_;
    } else {
        let mut v_val_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2294_);
        v_val_2298_ = leanh::lean_ctor_get(v_x_2293_, 0);
        leanh::lean_inc(v_val_2298_);
        leanh::lean_dec_ref_known(v_x_2293_, 1);
        v___x_2299_ = leanh::lean_apply_1(v_h__2_2295_, v_val_2298_);
        return v___x_2299_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_2300_: *mut leanh::LeanObject,
    mut v_h__1_2301_: *mut leanh::LeanObject,
    mut v_h__2_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2300_) == 0 {
        let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2302_);
        v___x_2303_ = leanh::lean_box(0);
        v___x_2304_ = leanh::lean_apply_1(v_h__1_2301_, v___x_2303_);
        return v___x_2304_;
    } else {
        let mut v_val_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2301_);
        v_val_2305_ = leanh::lean_ctor_get(v_x_2300_, 0);
        leanh::lean_inc(v_val_2305_);
        leanh::lean_dec_ref_known(v_x_2300_, 1);
        v___x_2306_ = leanh::lean_apply_1(v_h__2_2302_, v_val_2305_);
        return v___x_2306_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b2_2307_: *mut leanh::LeanObject,
    mut v_motive_2308_: *mut leanh::LeanObject,
    mut v_x_2309_: *mut leanh::LeanObject,
    mut v_h__1_2310_: *mut leanh::LeanObject,
    mut v_h__2_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2309_) == 0 {
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2311_);
        v___x_2312_ = leanh::lean_box(0);
        v___x_2313_ = leanh::lean_apply_1(v_h__1_2310_, v___x_2312_);
        return v___x_2313_;
    } else {
        let mut v_val_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2310_);
        v_val_2314_ = leanh::lean_ctor_get(v_x_2309_, 0);
        leanh::lean_inc(v_val_2314_);
        leanh::lean_dec_ref_known(v_x_2309_, 1);
        v___x_2315_ = leanh::lean_apply_1(v_h__2_2311_, v_val_2314_);
        return v___x_2315_;
    }
}
pub unsafe fn l_Std_Internal_List_modifyKey___redArg(
    mut v_inst_2316_: *mut leanh::LeanObject,
    mut v_k_2317_: *mut leanh::LeanObject,
    mut v_f_2318_: *mut leanh::LeanObject,
    mut v_l_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_l_2319_);
    leanh::lean_inc(v_k_2317_);
    leanh::lean_inc_ref(v_inst_2316_);
    v___x_2320_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_2316_, v_k_2317_, v_l_2319_);
    if leanh::lean_obj_tag(v___x_2320_) == 0 {
        leanh::lean_dec(v_f_2318_);
        leanh::lean_dec(v_k_2317_);
        leanh::lean_dec_ref(v_inst_2316_);
        return v_l_2319_;
    } else {
        let mut v_val_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2321_ = leanh::lean_ctor_get(v___x_2320_, 0);
        leanh::lean_inc(v_val_2321_);
        leanh::lean_dec_ref_known(v___x_2320_, 1);
        v___x_2322_ = leanh::lean_apply_1(v_f_2318_, v_val_2321_);
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
    mut v_00_u03b1_2324_: *mut leanh::LeanObject,
    mut v_00_u03b2_2325_: *mut leanh::LeanObject,
    mut v_inst_2326_: *mut leanh::LeanObject,
    mut v_inst_2327_: *mut leanh::LeanObject,
    mut v_k_2328_: *mut leanh::LeanObject,
    mut v_f_2329_: *mut leanh::LeanObject,
    mut v_l_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ =
        l_Std_Internal_List_modifyKey___redArg(v_inst_2326_, v_k_2328_, v_f_2329_, v_l_2330_);
    return v___x_2331_;
}
pub unsafe fn l_Std_Internal_List_Const_modifyKey___redArg(
    mut v_inst_2332_: *mut leanh::LeanObject,
    mut v_k_2333_: *mut leanh::LeanObject,
    mut v_f_2334_: *mut leanh::LeanObject,
    mut v_l_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_l_2335_);
    leanh::lean_inc(v_k_2333_);
    leanh::lean_inc_ref(v_inst_2332_);
    v___x_2336_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_2332_, v_k_2333_, v_l_2335_);
    if leanh::lean_obj_tag(v___x_2336_) == 0 {
        leanh::lean_dec(v_f_2334_);
        leanh::lean_dec(v_k_2333_);
        leanh::lean_dec_ref(v_inst_2332_);
        return v_l_2335_;
    } else {
        let mut v_val_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2337_ = leanh::lean_ctor_get(v___x_2336_, 0);
        leanh::lean_inc(v_val_2337_);
        leanh::lean_dec_ref_known(v___x_2336_, 1);
        v___x_2338_ = leanh::lean_apply_1(v_f_2334_, v_val_2337_);
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
    mut v_00_u03b1_2340_: *mut leanh::LeanObject,
    mut v_00_u03b2_2341_: *mut leanh::LeanObject,
    mut v_inst_2342_: *mut leanh::LeanObject,
    mut v_k_2343_: *mut leanh::LeanObject,
    mut v_f_2344_: *mut leanh::LeanObject,
    mut v_l_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l_Std_Internal_List_Const_modifyKey___redArg(v_inst_2342_, v_k_2343_, v_f_2344_, v_l_2345_);
    return v___x_2346_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_2347_: *mut leanh::LeanObject,
    mut v_h__1_2348_: *mut leanh::LeanObject,
    mut v_h__2_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2347_) == 0 {
        let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2348_);
        v___x_2350_ = leanh::lean_box(0);
        v___x_2351_ = leanh::lean_apply_1(v_h__2_2349_, v___x_2350_);
        return v___x_2351_;
    } else {
        let mut v_val_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2349_);
        v_val_2352_ = leanh::lean_ctor_get(v_x_2347_, 0);
        leanh::lean_inc(v_val_2352_);
        leanh::lean_dec_ref_known(v_x_2347_, 1);
        v___x_2353_ = leanh::lean_apply_1(v_h__1_2348_, v_val_2352_);
        return v___x_2353_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_2354_: *mut leanh::LeanObject,
    mut v_motive_2355_: *mut leanh::LeanObject,
    mut v_x_2356_: *mut leanh::LeanObject,
    mut v_h__1_2357_: *mut leanh::LeanObject,
    mut v_h__2_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2356_) == 0 {
        let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2357_);
        v___x_2359_ = leanh::lean_box(0);
        v___x_2360_ = leanh::lean_apply_1(v_h__2_2358_, v___x_2359_);
        return v___x_2360_;
    } else {
        let mut v_val_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2358_);
        v_val_2361_ = leanh::lean_ctor_get(v_x_2356_, 0);
        leanh::lean_inc(v_val_2361_);
        leanh::lean_dec_ref_known(v_x_2356_, 1);
        v___x_2362_ = leanh::lean_apply_1(v_h__1_2357_, v_val_2361_);
        return v___x_2362_;
    }
}
pub unsafe fn l_Std_Internal_List_eraseList___redArg(
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_l_2364_: *mut leanh::LeanObject,
    mut v_toErase_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_toErase_2365_) == 0 {
                    leanh::lean_dec_ref(v_inst_2363_);
                    return v_l_2364_;
                } else {
                    v_head_2366_ = leanh::lean_ctor_get(v_toErase_2365_, 0);
                    leanh::lean_inc(v_head_2366_);
                    v_tail_2367_ = leanh::lean_ctor_get(v_toErase_2365_, 1);
                    leanh::lean_inc(v_tail_2367_);
                    leanh::lean_dec_ref_known(v_toErase_2365_, 2);
                    leanh::lean_inc_ref(v_inst_2363_);
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
    mut v_00_u03b1_2370_: *mut leanh::LeanObject,
    mut v_00_u03b2_2371_: *mut leanh::LeanObject,
    mut v_inst_2372_: *mut leanh::LeanObject,
    mut v_l_2373_: *mut leanh::LeanObject,
    mut v_toErase_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = l_Std_Internal_List_eraseList___redArg(v_inst_2372_, v_l_2373_, v_toErase_2374_);
    return v___x_2375_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(
    mut v_opt_2376_: *mut leanh::LeanObject,
    mut v_h__1_2377_: *mut leanh::LeanObject,
    mut v_h__2_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_opt_2376_) == 0 {
        let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2377_);
        v___x_2379_ = leanh::lean_box(0);
        v___x_2380_ = leanh::lean_apply_1(v_h__2_2378_, v___x_2379_);
        return v___x_2380_;
    } else {
        let mut v_val_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2378_);
        v_val_2381_ = leanh::lean_ctor_get(v_opt_2376_, 0);
        leanh::lean_inc(v_val_2381_);
        leanh::lean_dec_ref_known(v_opt_2376_, 1);
        v___x_2382_ = leanh::lean_apply_1(v_h__1_2377_, v_val_2381_);
        return v___x_2382_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(
    mut v_00_u03b1_2383_: *mut leanh::LeanObject,
    mut v_motive_2384_: *mut leanh::LeanObject,
    mut v_opt_2385_: *mut leanh::LeanObject,
    mut v_h__1_2386_: *mut leanh::LeanObject,
    mut v_h__2_2387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_opt_2385_) == 0 {
        let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2386_);
        v___x_2388_ = leanh::lean_box(0);
        v___x_2389_ = leanh::lean_apply_1(v_h__2_2387_, v___x_2388_);
        return v___x_2389_;
    } else {
        let mut v_val_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2387_);
        v_val_2390_ = leanh::lean_ctor_get(v_opt_2385_, 0);
        leanh::lean_inc(v_val_2390_);
        leanh::lean_dec_ref_known(v_opt_2385_, 1);
        v___x_2391_ = leanh::lean_apply_1(v_h__1_2386_, v_val_2390_);
        return v___x_2391_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(
    mut v_00_u03b1_2392_: *mut leanh::LeanObject,
    mut v_00_u03b2_2393_: *mut leanh::LeanObject,
    mut v_inst_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = leanh::lean_box(0);
    return v___x_2395_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(
    mut v_00_u03b1_2396_: *mut leanh::LeanObject,
    mut v_00_u03b2_2397_: *mut leanh::LeanObject,
    mut v_inst_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(
        v_00_u03b1_2396_,
        v_00_u03b2_2397_,
        v_inst_2398_,
    );
    leanh::lean_dec_ref(v_inst_2398_);
    return v_res_2399_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(
    mut v_inst_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
    mut v_b_2402_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v_fst_2403_ = leanh::lean_ctor_get(v_a_2401_, 0);
    leanh::lean_inc(v_fst_2403_);
    leanh::lean_dec_ref(v_a_2401_);
    v_fst_2404_ = leanh::lean_ctor_get(v_b_2402_, 0);
    leanh::lean_inc(v_fst_2404_);
    leanh::lean_dec_ref(v_b_2402_);
    v___x_2405_ = leanh::lean_apply_2(v_inst_2400_, v_fst_2403_, v_fst_2404_);
    v___x_2406_ = (leanh::lean_unbox(v___x_2405_) as u8);
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
    mut v_inst_2409_: *mut leanh::LeanObject,
    mut v_a_2410_: *mut leanh::LeanObject,
    mut v_b_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: u8 = 0;
    let mut v_r_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_2409_, v_a_2410_, v_b_2411_);
    v_r_2413_ = leanh::lean_box((v_res_2412_) as usize);
    return v_r_2413_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(
    mut v_00_u03b1_2414_: *mut leanh::LeanObject,
    mut v_00_u03b2_2415_: *mut leanh::LeanObject,
    mut v_inst_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
    mut v_b_2418_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2419_: u8 = 0;
    v___x_2419_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_2416_, v_a_2417_, v_b_2418_);
    return v___x_2419_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(
    mut v_00_u03b1_2420_: *mut leanh::LeanObject,
    mut v_00_u03b2_2421_: *mut leanh::LeanObject,
    mut v_inst_2422_: *mut leanh::LeanObject,
    mut v_a_2423_: *mut leanh::LeanObject,
    mut v_b_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: u8 = 0;
    let mut v_r_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_2420_, v_00_u03b2_2421_, v_inst_2422_, v_a_2423_, v_b_2424_);
    v_r_2426_ = leanh::lean_box((v_res_2425_) as usize);
    return v_r_2426_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(
    mut v_inst_2427_: *mut leanh::LeanObject,
    mut v_a_2428_: *mut leanh::LeanObject,
    mut v_b_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: u8 = 0;
    v_fst_2430_ = leanh::lean_ctor_get(v_a_2428_, 0);
    v_fst_2431_ = leanh::lean_ctor_get(v_b_2429_, 0);
    leanh::lean_inc(v_fst_2431_);
    leanh::lean_inc(v_fst_2430_);
    v___x_2432_ = leanh::lean_apply_2(v_inst_2427_, v_fst_2430_, v_fst_2431_);
    v___x_2433_ = (leanh::lean_unbox(v___x_2432_) as u8);
    if v___x_2433_ == 2 {
        leanh::lean_dec_ref(v_a_2428_);
        return v_b_2429_;
    } else {
        leanh::lean_dec_ref(v_b_2429_);
        return v_a_2428_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(
    mut v_inst_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2435_ = leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_2435_, 0, v_inst_2434_);
    return v___f_2435_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(
    mut v_00_u03b1_2436_: *mut leanh::LeanObject,
    mut v_00_u03b2_2437_: *mut leanh::LeanObject,
    mut v_inst_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2439_ = leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_2439_, 0, v_inst_2438_);
    return v___f_2439_;
}
pub unsafe fn l_Std_Internal_List_minEntry_x3f___redArg(
    mut v_inst_2440_: *mut leanh::LeanObject,
    mut v_xs_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2442_ = leanh::lean_alloc_closure(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_2442_, 0, v_inst_2440_);
    v___x_2443_ = l_List_min_x3f___redArg(v___f_2442_, v_xs_2441_);
    return v___x_2443_;
}
pub unsafe fn l_Std_Internal_List_minEntry_x3f(
    mut v_00_u03b1_2444_: *mut leanh::LeanObject,
    mut v_00_u03b2_2445_: *mut leanh::LeanObject,
    mut v_inst_2446_: *mut leanh::LeanObject,
    mut v_xs_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_2446_, v_xs_2447_);
    return v___x_2448_;
}
pub unsafe fn l_Std_Internal_List_minKey_x3f___redArg(
    mut v_inst_2449_: *mut leanh::LeanObject,
    mut v_xs_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v_fst_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2451_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_2449_, v_xs_2450_);
                if leanh::lean_obj_tag(v___x_2451_) == 0 {
                    v___x_2452_ = leanh::lean_box(0);
                    return v___x_2452_;
                } else {
                    v_val_2453_ = leanh::lean_ctor_get(v___x_2451_, 0);
                    v_isSharedCheck_2461_ = (!leanh::lean_is_exclusive(v___x_2451_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v___x_2455_ = v___x_2451_;
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2453_);
                        leanh::lean_dec(v___x_2451_);
                        v___x_2455_ = leanh::lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2457_ = leanh::lean_ctor_get(v_val_2453_, 0);
                leanh::lean_inc(v_fst_2457_);
                leanh::lean_dec(v_val_2453_);
                if v_isShared_2456_ == 0 {
                    leanh::lean_ctor_set(v___x_2455_, 0, v_fst_2457_);
                    v___x_2459_ = v___x_2455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2457_);
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
    mut v_00_u03b1_2462_: *mut leanh::LeanObject,
    mut v_00_u03b2_2463_: *mut leanh::LeanObject,
    mut v_inst_2464_: *mut leanh::LeanObject,
    mut v_xs_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2464_, v_xs_2465_);
    return v___x_2466_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(
    mut v_x_2467_: *mut leanh::LeanObject,
    mut v_h__1_2468_: *mut leanh::LeanObject,
    mut v_h__2_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2467_) == 0 {
        let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2469_);
        v___x_2470_ = leanh::lean_box(0);
        v___x_2471_ = leanh::lean_apply_1(v_h__1_2468_, v___x_2470_);
        return v___x_2471_;
    } else {
        let mut v_val_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2468_);
        v_val_2472_ = leanh::lean_ctor_get(v_x_2467_, 0);
        leanh::lean_inc(v_val_2472_);
        leanh::lean_dec_ref_known(v_x_2467_, 1);
        v___x_2473_ = leanh::lean_apply_1(v_h__2_2469_, v_val_2472_);
        return v___x_2473_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(
    mut v_00_u03b1_2474_: *mut leanh::LeanObject,
    mut v_00_u03b2_2475_: *mut leanh::LeanObject,
    mut v_motive_2476_: *mut leanh::LeanObject,
    mut v_x_2477_: *mut leanh::LeanObject,
    mut v_h__1_2478_: *mut leanh::LeanObject,
    mut v_h__2_2479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2477_) == 0 {
        let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2479_);
        v___x_2480_ = leanh::lean_box(0);
        v___x_2481_ = leanh::lean_apply_1(v_h__1_2478_, v___x_2480_);
        return v___x_2481_;
    } else {
        let mut v_val_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2478_);
        v_val_2482_ = leanh::lean_ctor_get(v_x_2477_, 0);
        leanh::lean_inc(v_val_2482_);
        leanh::lean_dec_ref_known(v_x_2477_, 1);
        v___x_2483_ = leanh::lean_apply_1(v_h__2_2479_, v_val_2482_);
        return v___x_2483_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_2484_: *mut leanh::LeanObject,
    mut v_h__1_2485_: *mut leanh::LeanObject,
    mut v_h__2_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2484_) == 0 {
        let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2486_);
        v___x_2487_ = leanh::lean_box(0);
        v___x_2488_ = leanh::lean_apply_1(v_h__1_2485_, v___x_2487_);
        return v___x_2488_;
    } else {
        let mut v_head_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2485_);
        v_head_2489_ = leanh::lean_ctor_get(v_x_2484_, 0);
        leanh::lean_inc(v_head_2489_);
        v_tail_2490_ = leanh::lean_ctor_get(v_x_2484_, 1);
        leanh::lean_inc(v_tail_2490_);
        leanh::lean_dec_ref_known(v_x_2484_, 2);
        v___x_2491_ = leanh::lean_apply_2(v_h__2_2486_, v_head_2489_, v_tail_2490_);
        return v___x_2491_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_2492_: *mut leanh::LeanObject,
    mut v_motive_2493_: *mut leanh::LeanObject,
    mut v_x_2494_: *mut leanh::LeanObject,
    mut v_h__1_2495_: *mut leanh::LeanObject,
    mut v_h__2_2496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2494_) == 0 {
        let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2496_);
        v___x_2497_ = leanh::lean_box(0);
        v___x_2498_ = leanh::lean_apply_1(v_h__1_2495_, v___x_2497_);
        return v___x_2498_;
    } else {
        let mut v_head_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2495_);
        v_head_2499_ = leanh::lean_ctor_get(v_x_2494_, 0);
        leanh::lean_inc(v_head_2499_);
        v_tail_2500_ = leanh::lean_ctor_get(v_x_2494_, 1);
        leanh::lean_inc(v_tail_2500_);
        leanh::lean_dec_ref_known(v_x_2494_, 2);
        v___x_2501_ = leanh::lean_apply_2(v_h__2_2496_, v_head_2499_, v_tail_2500_);
        return v___x_2501_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(
    mut v_x_2502_: *mut leanh::LeanObject,
    mut v_h__1_2503_: *mut leanh::LeanObject,
    mut v_h__2_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2502_) == 0 {
        let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2504_);
        v___x_2505_ = leanh::lean_box(0);
        v___x_2506_ = leanh::lean_apply_1(v_h__1_2503_, v___x_2505_);
        return v___x_2506_;
    } else {
        let mut v_val_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2503_);
        v_val_2507_ = leanh::lean_ctor_get(v_x_2502_, 0);
        leanh::lean_inc(v_val_2507_);
        leanh::lean_dec_ref_known(v_x_2502_, 1);
        v___x_2508_ = leanh::lean_apply_1(v_h__2_2504_, v_val_2507_);
        return v___x_2508_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(
    mut v_00_u03b1_2509_: *mut leanh::LeanObject,
    mut v_00_u03b2_2510_: *mut leanh::LeanObject,
    mut v_motive_2511_: *mut leanh::LeanObject,
    mut v_x_2512_: *mut leanh::LeanObject,
    mut v_h__1_2513_: *mut leanh::LeanObject,
    mut v_h__2_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2512_) == 0 {
        let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2514_);
        v___x_2515_ = leanh::lean_box(0);
        v___x_2516_ = leanh::lean_apply_1(v_h__1_2513_, v___x_2515_);
        return v___x_2516_;
    } else {
        let mut v_val_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2513_);
        v_val_2517_ = leanh::lean_ctor_get(v_x_2512_, 0);
        leanh::lean_inc(v_val_2517_);
        leanh::lean_dec_ref_known(v_x_2512_, 1);
        v___x_2518_ = leanh::lean_apply_1(v_h__2_2514_, v_val_2517_);
        return v___x_2518_;
    }
}
pub unsafe fn l_Std_Internal_List_minKey___redArg(
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_xs_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2519_, v_xs_2520_);
    v_val_2522_ = leanh::lean_ctor_get(v___x_2521_, 0);
    leanh::lean_inc(v_val_2522_);
    leanh::lean_dec(v___x_2521_);
    return v_val_2522_;
}
pub unsafe fn l_Std_Internal_List_minKey(
    mut v_00_u03b1_2523_: *mut leanh::LeanObject,
    mut v_00_u03b2_2524_: *mut leanh::LeanObject,
    mut v_inst_2525_: *mut leanh::LeanObject,
    mut v_xs_2526_: *mut leanh::LeanObject,
    mut v_h_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ = l_Std_Internal_List_minKey___redArg(v_inst_2525_, v_xs_2526_);
    return v___x_2528_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21___redArg(
    mut v_inst_2529_: *mut leanh::LeanObject,
    mut v_inst_2530_: *mut leanh::LeanObject,
    mut v_xs_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2529_, v_xs_2531_);
    if leanh::lean_obj_tag(v___x_2532_) == 0 {
        let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2533_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_2534_ = l_panic___redArg(v_inst_2530_, v___x_2533_);
        return v___x_2534_;
    } else {
        let mut v_val_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2535_ = leanh::lean_ctor_get(v___x_2532_, 0);
        leanh::lean_inc(v_val_2535_);
        leanh::lean_dec_ref_known(v___x_2532_, 1);
        return v_val_2535_;
    }
}
pub unsafe fn l_Std_Internal_List_minKey_x21___redArg___boxed(
    mut v_inst_2536_: *mut leanh::LeanObject,
    mut v_inst_2537_: *mut leanh::LeanObject,
    mut v_xs_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_2536_, v_inst_2537_, v_xs_2538_);
    leanh::lean_dec(v_inst_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21(
    mut v_00_u03b1_2540_: *mut leanh::LeanObject,
    mut v_00_u03b2_2541_: *mut leanh::LeanObject,
    mut v_inst_2542_: *mut leanh::LeanObject,
    mut v_inst_2543_: *mut leanh::LeanObject,
    mut v_xs_2544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_2542_, v_inst_2543_, v_xs_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Std_Internal_List_minKey_x21___boxed(
    mut v_00_u03b1_2546_: *mut leanh::LeanObject,
    mut v_00_u03b2_2547_: *mut leanh::LeanObject,
    mut v_inst_2548_: *mut leanh::LeanObject,
    mut v_inst_2549_: *mut leanh::LeanObject,
    mut v_xs_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_Internal_List_minKey_x21(
        v_00_u03b1_2546_,
        v_00_u03b2_2547_,
        v_inst_2548_,
        v_inst_2549_,
        v_xs_2550_,
    );
    leanh::lean_dec(v_inst_2549_);
    return v_res_2551_;
}
pub unsafe fn l_Std_Internal_List_minKeyD___redArg(
    mut v_inst_2552_: *mut leanh::LeanObject,
    mut v_xs_2553_: *mut leanh::LeanObject,
    mut v_fallback_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_2552_, v_xs_2553_);
    if leanh::lean_obj_tag(v___x_2555_) == 0 {
        leanh::lean_inc(v_fallback_2554_);
        return v_fallback_2554_;
    } else {
        let mut v_val_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2556_ = leanh::lean_ctor_get(v___x_2555_, 0);
        leanh::lean_inc(v_val_2556_);
        leanh::lean_dec_ref_known(v___x_2555_, 1);
        return v_val_2556_;
    }
}
pub unsafe fn l_Std_Internal_List_minKeyD___redArg___boxed(
    mut v_inst_2557_: *mut leanh::LeanObject,
    mut v_xs_2558_: *mut leanh::LeanObject,
    mut v_fallback_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Std_Internal_List_minKeyD___redArg(v_inst_2557_, v_xs_2558_, v_fallback_2559_);
    leanh::lean_dec(v_fallback_2559_);
    return v_res_2560_;
}
pub unsafe fn l_Std_Internal_List_minKeyD(
    mut v_00_u03b1_2561_: *mut leanh::LeanObject,
    mut v_00_u03b2_2562_: *mut leanh::LeanObject,
    mut v_inst_2563_: *mut leanh::LeanObject,
    mut v_xs_2564_: *mut leanh::LeanObject,
    mut v_fallback_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Std_Internal_List_minKeyD___redArg(v_inst_2563_, v_xs_2564_, v_fallback_2565_);
    return v___x_2566_;
}
pub unsafe fn l_Std_Internal_List_minKeyD___boxed(
    mut v_00_u03b1_2567_: *mut leanh::LeanObject,
    mut v_00_u03b2_2568_: *mut leanh::LeanObject,
    mut v_inst_2569_: *mut leanh::LeanObject,
    mut v_xs_2570_: *mut leanh::LeanObject,
    mut v_fallback_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_Internal_List_minKeyD(
        v_00_u03b1_2567_,
        v_00_u03b2_2568_,
        v_inst_2569_,
        v_xs_2570_,
        v_fallback_2571_,
    );
    leanh::lean_dec(v_fallback_2571_);
    return v_res_2572_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x3f___redArg(
    mut v_inst_2573_: *mut leanh::LeanObject,
    mut v_xs_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2575_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2575_, 0, v_inst_2573_);
    v___x_2576_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2575_, v_xs_2574_);
    return v___x_2576_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x3f(
    mut v_00_u03b1_2577_: *mut leanh::LeanObject,
    mut v_00_u03b2_2578_: *mut leanh::LeanObject,
    mut v_inst_2579_: *mut leanh::LeanObject,
    mut v_xs_2580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2581_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2581_, 0, v_inst_2579_);
    v___x_2582_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2581_, v_xs_2580_);
    return v___x_2582_;
}
pub unsafe fn l_Std_Internal_List_maxKey___redArg(
    mut v_inst_2583_: *mut leanh::LeanObject,
    mut v_xs_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2585_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2585_, 0, v_inst_2583_);
    v___x_2586_ = l_Std_Internal_List_minKey___redArg(v___f_2585_, v_xs_2584_);
    return v___x_2586_;
}
pub unsafe fn l_Std_Internal_List_maxKey(
    mut v_00_u03b1_2587_: *mut leanh::LeanObject,
    mut v_00_u03b2_2588_: *mut leanh::LeanObject,
    mut v_inst_2589_: *mut leanh::LeanObject,
    mut v_xs_2590_: *mut leanh::LeanObject,
    mut v_h_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2592_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2592_, 0, v_inst_2589_);
    v___x_2593_ = l_Std_Internal_List_minKey___redArg(v___f_2592_, v_xs_2590_);
    return v___x_2593_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___redArg(
    mut v_inst_2594_: *mut leanh::LeanObject,
    mut v_inst_2595_: *mut leanh::LeanObject,
    mut v_xs_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2597_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2597_, 0, v_inst_2594_);
    v___x_2598_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_2597_, v_xs_2596_);
    if leanh::lean_obj_tag(v___x_2598_) == 0 {
        let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2599_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once),
            _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3,
        );
        v___x_2600_ = l_panic___redArg(v_inst_2595_, v___x_2599_);
        return v___x_2600_;
    } else {
        let mut v_val_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2601_ = leanh::lean_ctor_get(v___x_2598_, 0);
        leanh::lean_inc(v_val_2601_);
        leanh::lean_dec_ref_known(v___x_2598_, 1);
        return v_val_2601_;
    }
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___redArg___boxed(
    mut v_inst_2602_: *mut leanh::LeanObject,
    mut v_inst_2603_: *mut leanh::LeanObject,
    mut v_xs_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2605_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_2602_, v_inst_2603_, v_xs_2604_);
    leanh::lean_dec(v_inst_2603_);
    return v_res_2605_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21(
    mut v_00_u03b1_2606_: *mut leanh::LeanObject,
    mut v_00_u03b2_2607_: *mut leanh::LeanObject,
    mut v_inst_2608_: *mut leanh::LeanObject,
    mut v_inst_2609_: *mut leanh::LeanObject,
    mut v_xs_2610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_2608_, v_inst_2609_, v_xs_2610_);
    return v___x_2611_;
}
pub unsafe fn l_Std_Internal_List_maxKey_x21___boxed(
    mut v_00_u03b1_2612_: *mut leanh::LeanObject,
    mut v_00_u03b2_2613_: *mut leanh::LeanObject,
    mut v_inst_2614_: *mut leanh::LeanObject,
    mut v_inst_2615_: *mut leanh::LeanObject,
    mut v_xs_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Std_Internal_List_maxKey_x21(
        v_00_u03b1_2612_,
        v_00_u03b2_2613_,
        v_inst_2614_,
        v_inst_2615_,
        v_xs_2616_,
    );
    leanh::lean_dec(v_inst_2615_);
    return v_res_2617_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___redArg(
    mut v_inst_2618_: *mut leanh::LeanObject,
    mut v_xs_2619_: *mut leanh::LeanObject,
    mut v_fallback_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2621_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2621_, 0, v_inst_2618_);
    v___x_2622_ = l_Std_Internal_List_minKeyD___redArg(v___f_2621_, v_xs_2619_, v_fallback_2620_);
    return v___x_2622_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___redArg___boxed(
    mut v_inst_2623_: *mut leanh::LeanObject,
    mut v_xs_2624_: *mut leanh::LeanObject,
    mut v_fallback_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2626_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_2623_, v_xs_2624_, v_fallback_2625_);
    leanh::lean_dec(v_fallback_2625_);
    return v_res_2626_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD(
    mut v_00_u03b1_2627_: *mut leanh::LeanObject,
    mut v_00_u03b2_2628_: *mut leanh::LeanObject,
    mut v_inst_2629_: *mut leanh::LeanObject,
    mut v_xs_2630_: *mut leanh::LeanObject,
    mut v_fallback_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2632_ = leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2632_, 0, v_inst_2629_);
    v___x_2633_ = l_Std_Internal_List_minKeyD___redArg(v___f_2632_, v_xs_2630_, v_fallback_2631_);
    return v___x_2633_;
}
pub unsafe fn l_Std_Internal_List_maxKeyD___boxed(
    mut v_00_u03b1_2634_: *mut leanh::LeanObject,
    mut v_00_u03b2_2635_: *mut leanh::LeanObject,
    mut v_inst_2636_: *mut leanh::LeanObject,
    mut v_xs_2637_: *mut leanh::LeanObject,
    mut v_fallback_2638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Std_Internal_List_maxKeyD(
        v_00_u03b1_2634_,
        v_00_u03b2_2635_,
        v_inst_2636_,
        v_xs_2637_,
        v_fallback_2638_,
    );
    leanh::lean_dec(v_fallback_2638_);
    return v_res_2639_;
}
pub unsafe fn l_Std_Internal_List_interSmallerFn___redArg(
    mut v_inst_2640_: *mut leanh::LeanObject,
    mut v_l_2641_: *mut leanh::LeanObject,
    mut v_sofar_2642_: *mut leanh::LeanObject,
    mut v_k_2643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2640_);
    v___x_2644_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_2640_, v_k_2643_, v_l_2641_);
    if leanh::lean_obj_tag(v___x_2644_) == 0 {
        leanh::lean_dec_ref(v_inst_2640_);
        return v_sofar_2642_;
    } else {
        let mut v_val_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2645_ = leanh::lean_ctor_get(v___x_2644_, 0);
        leanh::lean_inc(v_val_2645_);
        leanh::lean_dec_ref_known(v___x_2644_, 1);
        v_fst_2646_ = leanh::lean_ctor_get(v_val_2645_, 0);
        leanh::lean_inc(v_fst_2646_);
        v_snd_2647_ = leanh::lean_ctor_get(v_val_2645_, 1);
        leanh::lean_inc(v_snd_2647_);
        leanh::lean_dec(v_val_2645_);
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
    mut v_00_u03b1_2649_: *mut leanh::LeanObject,
    mut v_00_u03b2_2650_: *mut leanh::LeanObject,
    mut v_inst_2651_: *mut leanh::LeanObject,
    mut v_l_2652_: *mut leanh::LeanObject,
    mut v_sofar_2653_: *mut leanh::LeanObject,
    mut v_k_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Std_Internal_List_interSmallerFn___redArg(
        v_inst_2651_,
        v_l_2652_,
        v_sofar_2653_,
        v_k_2654_,
    );
    return v___x_2655_;
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(
    mut v_x_2656_: *mut leanh::LeanObject,
    mut v_h__1_2657_: *mut leanh::LeanObject,
    mut v_h__2_2658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2656_) == 0 {
        let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2657_);
        v___x_2659_ = leanh::lean_box(0);
        v___x_2660_ = leanh::lean_apply_1(v_h__2_2658_, v___x_2659_);
        return v___x_2660_;
    } else {
        let mut v_val_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2658_);
        v_val_2661_ = leanh::lean_ctor_get(v_x_2656_, 0);
        leanh::lean_inc(v_val_2661_);
        leanh::lean_dec_ref_known(v_x_2656_, 1);
        v___x_2662_ = leanh::lean_apply_1(v_h__1_2657_, v_val_2661_);
        return v___x_2662_;
    }
}
pub unsafe fn l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_2663_: *mut leanh::LeanObject,
    mut v_00_u03b2_2664_: *mut leanh::LeanObject,
    mut v_motive_2665_: *mut leanh::LeanObject,
    mut v_x_2666_: *mut leanh::LeanObject,
    mut v_h__1_2667_: *mut leanh::LeanObject,
    mut v_h__2_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2666_) == 0 {
        let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2667_);
        v___x_2669_ = leanh::lean_box(0);
        v___x_2670_ = leanh::lean_apply_1(v_h__2_2668_, v___x_2669_);
        return v___x_2670_;
    } else {
        let mut v_val_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2668_);
        v_val_2671_ = leanh::lean_ctor_get(v_x_2666_, 0);
        leanh::lean_inc(v_val_2671_);
        leanh::lean_dec_ref_known(v_x_2666_, 1);
        v___x_2672_ = leanh::lean_apply_1(v_h__1_2667_, v_val_2671_);
        return v___x_2672_;
    }
}
pub unsafe fn l_Std_Internal_List_interSmaller___redArg___lam__0(
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_l_u2081_2674_: *mut leanh::LeanObject,
    mut v_sofar_2675_: *mut leanh::LeanObject,
    mut v_kv_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2677_ = leanh::lean_ctor_get(v_kv_2676_, 0);
    leanh::lean_inc(v_fst_2677_);
    leanh::lean_dec_ref(v_kv_2676_);
    v___x_2678_ = l_Std_Internal_List_interSmallerFn___redArg(
        v_inst_2673_,
        v_l_u2081_2674_,
        v_sofar_2675_,
        v_fst_2677_,
    );
    return v___x_2678_;
}
pub unsafe fn l_Std_Internal_List_interSmaller___redArg(
    mut v_inst_2679_: *mut leanh::LeanObject,
    mut v_l_u2081_2680_: *mut leanh::LeanObject,
    mut v_l_u2082_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2682_ = leanh::lean_alloc_closure(
        l_Std_Internal_List_interSmaller___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2682_, 0, v_inst_2679_);
    leanh::lean_closure_set(v___f_2682_, 1, v_l_u2081_2680_);
    v___x_2683_ = leanh::lean_box(0);
    v___x_2684_ = l_List_foldl___redArg(v___f_2682_, v___x_2683_, v_l_u2082_2681_);
    return v___x_2684_;
}
pub unsafe fn l_Std_Internal_List_interSmaller(
    mut v_00_u03b1_2685_: *mut leanh::LeanObject,
    mut v_00_u03b2_2686_: *mut leanh::LeanObject,
    mut v_inst_2687_: *mut leanh::LeanObject,
    mut v_l_u2081_2688_: *mut leanh::LeanObject,
    mut v_l_u2082_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ =
        l_Std_Internal_List_interSmaller___redArg(v_inst_2687_, v_l_u2081_2688_, v_l_u2082_2689_);
    return v___x_2690_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Internal_List_Associative(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_LemmasExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Internal_List_Associative(
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
pub unsafe fn initialize_Std_Data_Internal_List_Associative(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_LemmasExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Internal_List_Associative(builtin);
}