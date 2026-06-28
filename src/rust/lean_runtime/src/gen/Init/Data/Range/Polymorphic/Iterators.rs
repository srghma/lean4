// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Iterators
// Imports: Init.Data.Range.Polymorphic.RangeIterator Init.Data.Range.Polymorphic.Basic Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Basic::{
    initialize_Init_Data_Range_Polymorphic_Basic,
    runtime_initialize_Init_Data_Range_Polymorphic_Basic,
};
use crate::r#gen::Init::Data::Range::Polymorphic::RangeIterator::{
    initialize_Init_Data_Range_Polymorphic_RangeIterator,
    runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator,
};
use crate::r#gen::Init::WFExtrinsicFix::{
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    l_WellFounded_opaqueFix_u2083___redArg,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
};
pub static l_Std_Rcc_toList___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Rcc_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Rcc_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Rcc_Internal_iter___redArg(
    mut v_r_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1273_ = crate::leanh::lean_ctor_get(v_r_1272_, 0);
                v_upper_1274_ = crate::leanh::lean_ctor_get(v_r_1272_, 1);
                v_isSharedCheck_1282_ = (!crate::leanh::lean_is_exclusive(v_r_1272_)) as u8;
                if v_isSharedCheck_1282_ == 0 {
                    v___x_1276_ = v_r_1272_;
                    v_isShared_1277_ = v_isSharedCheck_1282_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1274_);
                    crate::leanh::lean_inc(v_lower_1273_);
                    crate::leanh::lean_dec(v_r_1272_);
                    v___x_1276_ = crate::leanh::lean_box(0);
                    v_isShared_1277_ = v_isSharedCheck_1282_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1278_, 0, v_lower_1273_);
                if v_isShared_1277_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1278_);
                    v___x_1280_ = v___x_1276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_upper_1274_);
                    v___x_1280_ = v_reuseFailAlloc_1281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_Internal_iter(
    mut v_00_u03b1_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
    mut v_r_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1286_ = crate::leanh::lean_ctor_get(v_r_1285_, 0);
                v_upper_1287_ = crate::leanh::lean_ctor_get(v_r_1285_, 1);
                v_isSharedCheck_1295_ = (!crate::leanh::lean_is_exclusive(v_r_1285_)) as u8;
                if v_isSharedCheck_1295_ == 0 {
                    v___x_1289_ = v_r_1285_;
                    v_isShared_1290_ = v_isSharedCheck_1295_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1287_);
                    crate::leanh::lean_inc(v_lower_1286_);
                    crate::leanh::lean_dec(v_r_1285_);
                    v___x_1289_ = crate::leanh::lean_box(0);
                    v_isShared_1290_ = v_isSharedCheck_1295_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1291_, 0, v_lower_1286_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1291_);
                    v___x_1293_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_upper_1287_);
                    v___x_1293_ = v_reuseFailAlloc_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_Internal_iter___boxed(
    mut v_00_u03b1_1296_: *mut crate::leanh::LeanObject,
    mut v_inst_1297_: *mut crate::leanh::LeanObject,
    mut v_r_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Std_Rcc_Internal_iter(v_00_u03b1_1296_, v_inst_1297_, v_r_1298_);
    crate::leanh::lean_dec_ref(v_inst_1297_);
    return v_res_1299_;
}
pub unsafe fn l_Std_Rcc_toList___redArg___lam__0(
    mut v_inst_1300_: *mut crate::leanh::LeanObject,
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
    mut v_it_1302_: *mut crate::leanh::LeanObject,
    mut v_acc_1303_: *mut crate::leanh::LeanObject,
    mut v_recur_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_next_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v_val_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v_succ_x3f_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_unused_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1305_ = crate::leanh::lean_ctor_get(v_it_1302_, 0);
                crate::leanh::lean_inc(v_next_1305_);
                if crate::leanh::lean_obj_tag(v_next_1305_) == 0 {
                    crate::leanh::lean_dec_ref(v_recur_1304_);
                    crate::leanh::lean_dec_ref(v_it_1302_);
                    crate::leanh::lean_dec_ref(v_inst_1301_);
                    crate::leanh::lean_dec_ref(v_inst_1300_);
                    return v_acc_1303_;
                } else {
                    v_upperBound_1306_ = crate::leanh::lean_ctor_get(v_it_1302_, 1);
                    v_isSharedCheck_1320_ = (!crate::leanh::lean_is_exclusive(v_it_1302_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v_unused_1321_ = crate::leanh::lean_ctor_get(v_it_1302_, 0);
                        crate::leanh::lean_dec(v_unused_1321_);
                        v___x_1308_ = v_it_1302_;
                        v_isShared_1309_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upperBound_1306_);
                        crate::leanh::lean_dec(v_it_1302_);
                        v___x_1308_ = crate::leanh::lean_box(0);
                        v_isShared_1309_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1310_ = crate::leanh::lean_ctor_get(v_next_1305_, 0);
                crate::leanh::lean_inc_n(v_val_1310_, 2);
                crate::leanh::lean_dec_ref_known(v_next_1305_, 1);
                crate::leanh::lean_inc(v_upperBound_1306_);
                v___x_1311_ =
                    crate::leanh::lean_apply_2(v_inst_1300_, v_val_1310_, v_upperBound_1306_);
                v___x_1312_ = (crate::leanh::lean_unbox(v___x_1311_) as u8);
                if v___x_1312_ == 0 {
                    crate::leanh::lean_dec(v_val_1310_);
                    crate::leanh::lean_del_object(v___x_1308_);
                    crate::leanh::lean_dec(v_upperBound_1306_);
                    crate::leanh::lean_dec_ref(v_recur_1304_);
                    crate::leanh::lean_dec_ref(v_inst_1301_);
                    return v_acc_1303_;
                } else {
                    v_succ_x3f_1313_ = crate::leanh::lean_ctor_get(v_inst_1301_, 0);
                    crate::leanh::lean_inc_ref(v_succ_x3f_1313_);
                    crate::leanh::lean_dec_ref(v_inst_1301_);
                    crate::leanh::lean_inc(v_val_1310_);
                    v___x_1314_ = crate::leanh::lean_apply_1(v_succ_x3f_1313_, v_val_1310_);
                    if v_isShared_1309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1314_);
                        v___x_1316_ = v___x_1308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1314_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_upperBound_1306_);
                        v___x_1316_ = v_reuseFailAlloc_1319_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1317_ = lean_array_push(v_acc_1303_, v_val_1310_);
                v___x_1318_ = crate::leanh::lean_apply_3(
                    v_recur_1304_,
                    v___x_1316_,
                    v___x_1317_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_toList___redArg(
    mut v_inst_1324_: *mut crate::leanh::LeanObject,
    mut v_inst_1325_: *mut crate::leanh::LeanObject,
    mut v_r_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1327_ = crate::leanh::lean_ctor_get(v_r_1326_, 0);
                v_upper_1328_ = crate::leanh::lean_ctor_get(v_r_1326_, 1);
                v_isSharedCheck_1340_ = (!crate::leanh::lean_is_exclusive(v_r_1326_)) as u8;
                if v_isSharedCheck_1340_ == 0 {
                    v___x_1330_ = v_r_1326_;
                    v_isShared_1331_ = v_isSharedCheck_1340_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1328_);
                    crate::leanh::lean_inc(v_lower_1327_);
                    crate::leanh::lean_dec(v_r_1326_);
                    v___x_1330_ = crate::leanh::lean_box(0);
                    v_isShared_1331_ = v_isSharedCheck_1340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1332_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1332_, 0, v_inst_1324_);
                crate::leanh::lean_closure_set(v___f_1332_, 1, v_inst_1325_);
                v___x_1333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1333_, 0, v_lower_1327_);
                if v_isShared_1331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_upper_1328_);
                    v___x_1335_ = v_reuseFailAlloc_1339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1336_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1337_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1332_,
                        v___x_1335_,
                        v___x_1336_,
                    );
                v___x_1338_ = lean_array_to_list(v___x_1337_);
                return v___x_1338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_toList(
    mut v_00_u03b1_1341_: *mut crate::leanh::LeanObject,
    mut v_inst_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_inst_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_r_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___f_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1348_ = crate::leanh::lean_ctor_get(v_r_1347_, 0);
                v_upper_1349_ = crate::leanh::lean_ctor_get(v_r_1347_, 1);
                v_isSharedCheck_1361_ = (!crate::leanh::lean_is_exclusive(v_r_1347_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v___x_1351_ = v_r_1347_;
                    v_isShared_1352_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1349_);
                    crate::leanh::lean_inc(v_lower_1348_);
                    crate::leanh::lean_dec(v_r_1347_);
                    v___x_1351_ = crate::leanh::lean_box(0);
                    v_isShared_1352_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1353_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1353_, 0, v_inst_1343_);
                crate::leanh::lean_closure_set(v___f_1353_, 1, v_inst_1344_);
                v___x_1354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1354_, 0, v_lower_1348_);
                if v_isShared_1352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1354_);
                    v___x_1356_ = v___x_1351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_upper_1349_);
                    v___x_1356_ = v_reuseFailAlloc_1360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1357_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1358_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1353_,
                        v___x_1356_,
                        v___x_1357_,
                    );
                v___x_1359_ = lean_array_to_list(v___x_1358_);
                return v___x_1359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_toArray___redArg(
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
    mut v_inst_1363_: *mut crate::leanh::LeanObject,
    mut v_r_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___f_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1365_ = crate::leanh::lean_ctor_get(v_r_1364_, 0);
                v_upper_1366_ = crate::leanh::lean_ctor_get(v_r_1364_, 1);
                v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v_r_1364_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1368_ = v_r_1364_;
                    v_isShared_1369_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1366_);
                    crate::leanh::lean_inc(v_lower_1365_);
                    crate::leanh::lean_dec(v_r_1364_);
                    v___x_1368_ = crate::leanh::lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1370_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1370_, 0, v_inst_1362_);
                crate::leanh::lean_closure_set(v___f_1370_, 1, v_inst_1363_);
                v___x_1371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1371_, 0, v_lower_1365_);
                if v_isShared_1369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1371_);
                    v___x_1373_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_upper_1366_);
                    v___x_1373_ = v_reuseFailAlloc_1376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1374_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1375_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1370_,
                        v___x_1373_,
                        v___x_1374_,
                    );
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_toArray(
    mut v_00_u03b1_1378_: *mut crate::leanh::LeanObject,
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_inst_1381_: *mut crate::leanh::LeanObject,
    mut v_inst_1382_: *mut crate::leanh::LeanObject,
    mut v_inst_1383_: *mut crate::leanh::LeanObject,
    mut v_r_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___f_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1385_ = crate::leanh::lean_ctor_get(v_r_1384_, 0);
                v_upper_1386_ = crate::leanh::lean_ctor_get(v_r_1384_, 1);
                v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v_r_1384_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1388_ = v_r_1384_;
                    v_isShared_1389_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1386_);
                    crate::leanh::lean_inc(v_lower_1385_);
                    crate::leanh::lean_dec(v_r_1384_);
                    v___x_1388_ = crate::leanh::lean_box(0);
                    v_isShared_1389_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1390_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1390_, 0, v_inst_1380_);
                crate::leanh::lean_closure_set(v___f_1390_, 1, v_inst_1381_);
                v___x_1391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1391_, 0, v_lower_1385_);
                if v_isShared_1389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1388_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_upper_1386_);
                    v___x_1393_ = v_reuseFailAlloc_1396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1394_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1395_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1390_,
                        v___x_1393_,
                        v___x_1394_,
                    );
                return v___x_1395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_size___redArg(
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_r_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_1400_ = crate::leanh::lean_ctor_get(v_r_1399_, 0);
    crate::leanh::lean_inc(v_lower_1400_);
    v_upper_1401_ = crate::leanh::lean_ctor_get(v_r_1399_, 1);
    crate::leanh::lean_inc(v_upper_1401_);
    crate::leanh::lean_dec_ref(v_r_1399_);
    v___x_1402_ = crate::leanh::lean_apply_2(v_inst_1398_, v_lower_1400_, v_upper_1401_);
    return v___x_1402_;
}
pub unsafe fn l_Std_Rcc_size(
    mut v_00_u03b1_1403_: *mut crate::leanh::LeanObject,
    mut v_inst_1404_: *mut crate::leanh::LeanObject,
    mut v_r_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_1406_ = crate::leanh::lean_ctor_get(v_r_1405_, 0);
    crate::leanh::lean_inc(v_lower_1406_);
    v_upper_1407_ = crate::leanh::lean_ctor_get(v_r_1405_, 1);
    crate::leanh::lean_inc(v_upper_1407_);
    crate::leanh::lean_dec_ref(v_r_1405_);
    v___x_1408_ = crate::leanh::lean_apply_2(v_inst_1404_, v_lower_1406_, v_upper_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_toPure_1409_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = crate::leanh::lean_apply_2(
        v_toPure_1409_,
        crate::leanh::lean_box(0),
        v_____do__lift_1410_,
    );
    return v___x_1411_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1(
    mut v_toPure_1412_: *mut crate::leanh::LeanObject,
    mut v_inst_1413_: *mut crate::leanh::LeanObject,
    mut v_next_1414_: *mut crate::leanh::LeanObject,
    mut v_G_1415_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1416_) == 0 {
        let mut v_a_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_1415_);
        crate::leanh::lean_dec(v_next_1414_);
        crate::leanh::lean_dec_ref(v_inst_1413_);
        v_a_1417_ = crate::leanh::lean_ctor_get(v_____do__lift_1416_, 0);
        crate::leanh::lean_inc(v_a_1417_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1416_, 1);
        v___x_1418_ =
            crate::leanh::lean_apply_2(v_toPure_1412_, crate::leanh::lean_box(0), v_a_1417_);
        return v___x_1418_;
    } else {
        let mut v_a_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1419_ = crate::leanh::lean_ctor_get(v_____do__lift_1416_, 0);
        crate::leanh::lean_inc(v_a_1419_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1416_, 1);
        v_succ_x3f_1420_ = crate::leanh::lean_ctor_get(v_inst_1413_, 0);
        crate::leanh::lean_inc_ref(v_succ_x3f_1420_);
        crate::leanh::lean_dec_ref(v_inst_1413_);
        v___x_1421_ = crate::leanh::lean_apply_1(v_succ_x3f_1420_, v_next_1414_);
        if crate::leanh::lean_obj_tag(v___x_1421_) == 0 {
            let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_G_1415_);
            v___x_1422_ =
                crate::leanh::lean_apply_2(v_toPure_1412_, crate::leanh::lean_box(0), v_a_1419_);
            return v___x_1422_;
        } else {
            let mut v_val_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_1412_);
            v_val_1423_ = crate::leanh::lean_ctor_get(v___x_1421_, 0);
            crate::leanh::lean_inc(v_val_1423_);
            crate::leanh::lean_dec_ref_known(v___x_1421_, 1);
            v___x_1424_ = crate::leanh::lean_apply_4(
                v_G_1415_,
                v_val_1423_,
                v_a_1419_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1424_;
        }
    }
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_1425_: *mut crate::leanh::LeanObject,
    mut v_upper_1426_: *mut crate::leanh::LeanObject,
    mut v_toPure_1427_: *mut crate::leanh::LeanObject,
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_f_1429_: *mut crate::leanh::LeanObject,
    mut v_toBind_1430_: *mut crate::leanh::LeanObject,
    mut v___f_1431_: *mut crate::leanh::LeanObject,
    mut v_next_1432_: *mut crate::leanh::LeanObject,
    mut v_acc_1433_: *mut crate::leanh::LeanObject,
    mut v_h_1434_: *mut crate::leanh::LeanObject,
    mut v_G_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    crate::leanh::lean_inc(v_next_1432_);
    v___x_1436_ = crate::leanh::lean_apply_2(v_inst_1425_, v_next_1432_, v_upper_1426_);
    v___x_1437_ = (crate::leanh::lean_unbox(v___x_1436_) as u8);
    if v___x_1437_ == 0 {
        let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_1435_);
        crate::leanh::lean_dec(v_next_1432_);
        crate::leanh::lean_dec(v___f_1431_);
        crate::leanh::lean_dec(v_toBind_1430_);
        crate::leanh::lean_dec(v_f_1429_);
        crate::leanh::lean_dec_ref(v_inst_1428_);
        v___x_1438_ =
            crate::leanh::lean_apply_2(v_toPure_1427_, crate::leanh::lean_box(0), v_acc_1433_);
        return v___x_1438_;
    } else {
        let mut v___f_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_next_1432_);
        v___f_1439_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_1439_, 0, v_toPure_1427_);
        crate::leanh::lean_closure_set(v___f_1439_, 1, v_inst_1428_);
        crate::leanh::lean_closure_set(v___f_1439_, 2, v_next_1432_);
        crate::leanh::lean_closure_set(v___f_1439_, 3, v_G_1435_);
        v___x_1440_ = crate::leanh::lean_apply_3(
            v_f_1429_,
            v_next_1432_,
            crate::leanh::lean_box(0),
            v_acc_1433_,
        );
        crate::leanh::lean_inc(v_toBind_1430_);
        v___x_1441_ = crate::leanh::lean_apply_4(
            v_toBind_1430_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1440_,
            v___f_1431_,
        );
        v___x_1442_ = crate::leanh::lean_apply_4(
            v_toBind_1430_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1441_,
            v___f_1439_,
        );
        return v___x_1442_;
    }
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1446_: *mut crate::leanh::LeanObject,
    mut v_r_1447_: *mut crate::leanh::LeanObject,
    mut v_init_1448_: *mut crate::leanh::LeanObject,
    mut v_f_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1450_ = crate::leanh::lean_ctor_get(v_inst_1443_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1450_);
    v_lower_1451_ = crate::leanh::lean_ctor_get(v_r_1447_, 0);
    crate::leanh::lean_inc(v_lower_1451_);
    v_upper_1452_ = crate::leanh::lean_ctor_get(v_r_1447_, 1);
    crate::leanh::lean_inc(v_upper_1452_);
    crate::leanh::lean_dec_ref(v_r_1447_);
    v_toBind_1453_ = crate::leanh::lean_ctor_get(v_inst_1443_, 1);
    crate::leanh::lean_inc(v_toBind_1453_);
    crate::leanh::lean_dec_ref(v_inst_1443_);
    v_toPure_1454_ = crate::leanh::lean_ctor_get(v_toApplicative_1450_, 1);
    crate::leanh::lean_inc_n(v_toPure_1454_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1450_);
    v___f_1455_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1455_, 0, v_toPure_1454_);
    v___f_1456_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
    crate::leanh::lean_closure_set(v___f_1456_, 0, v_inst_1444_);
    crate::leanh::lean_closure_set(v___f_1456_, 1, v_upper_1452_);
    crate::leanh::lean_closure_set(v___f_1456_, 2, v_toPure_1454_);
    crate::leanh::lean_closure_set(v___f_1456_, 3, v_inst_1445_);
    crate::leanh::lean_closure_set(v___f_1456_, 4, v_f_1449_);
    crate::leanh::lean_closure_set(v___f_1456_, 5, v_toBind_1453_);
    crate::leanh::lean_closure_set(v___f_1456_, 6, v___f_1455_);
    v___x_1457_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1456_,
        v_lower_1451_,
        v_init_1448_,
        crate::leanh::lean_box(0),
    );
    return v___x_1457_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1458_: *mut crate::leanh::LeanObject,
    mut v_inst_1459_: *mut crate::leanh::LeanObject,
    mut v_inst_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1461_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1461_, 0, v_inst_1460_);
    crate::leanh::lean_closure_set(v___f_1461_, 1, v_inst_1459_);
    crate::leanh::lean_closure_set(v___f_1461_, 2, v_inst_1458_);
    return v___f_1461_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1462_: *mut crate::leanh::LeanObject,
    mut v_m_1463_: *mut crate::leanh::LeanObject,
    mut v_inst_1464_: *mut crate::leanh::LeanObject,
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v_inst_1467_: *mut crate::leanh::LeanObject,
    mut v_inst_1468_: *mut crate::leanh::LeanObject,
    mut v_inst_1469_: *mut crate::leanh::LeanObject,
    mut v_inst_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1471_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1471_, 0, v_inst_1469_);
    crate::leanh::lean_closure_set(v___f_1471_, 1, v_inst_1466_);
    crate::leanh::lean_closure_set(v___f_1471_, 2, v_inst_1464_);
    return v___f_1471_;
}
pub unsafe fn l_Std_Rco_Internal_iter___redArg(
    mut v_r_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1473_ = crate::leanh::lean_ctor_get(v_r_1472_, 0);
                v_upper_1474_ = crate::leanh::lean_ctor_get(v_r_1472_, 1);
                v_isSharedCheck_1482_ = (!crate::leanh::lean_is_exclusive(v_r_1472_)) as u8;
                if v_isSharedCheck_1482_ == 0 {
                    v___x_1476_ = v_r_1472_;
                    v_isShared_1477_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1474_);
                    crate::leanh::lean_inc(v_lower_1473_);
                    crate::leanh::lean_dec(v_r_1472_);
                    v___x_1476_ = crate::leanh::lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1478_, 0, v_lower_1473_);
                if v_isShared_1477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1476_, 0, v___x_1478_);
                    v___x_1480_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_upper_1474_);
                    v___x_1480_ = v_reuseFailAlloc_1481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_Internal_iter(
    mut v_00_u03b1_1483_: *mut crate::leanh::LeanObject,
    mut v_inst_1484_: *mut crate::leanh::LeanObject,
    mut v_r_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1486_ = crate::leanh::lean_ctor_get(v_r_1485_, 0);
                v_upper_1487_ = crate::leanh::lean_ctor_get(v_r_1485_, 1);
                v_isSharedCheck_1495_ = (!crate::leanh::lean_is_exclusive(v_r_1485_)) as u8;
                if v_isSharedCheck_1495_ == 0 {
                    v___x_1489_ = v_r_1485_;
                    v_isShared_1490_ = v_isSharedCheck_1495_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1487_);
                    crate::leanh::lean_inc(v_lower_1486_);
                    crate::leanh::lean_dec(v_r_1485_);
                    v___x_1489_ = crate::leanh::lean_box(0);
                    v_isShared_1490_ = v_isSharedCheck_1495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1491_, 0, v_lower_1486_);
                if v_isShared_1490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1489_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_upper_1487_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_Internal_iter___boxed(
    mut v_00_u03b1_1496_: *mut crate::leanh::LeanObject,
    mut v_inst_1497_: *mut crate::leanh::LeanObject,
    mut v_r_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Std_Rco_Internal_iter(v_00_u03b1_1496_, v_inst_1497_, v_r_1498_);
    crate::leanh::lean_dec_ref(v_inst_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Std_Rco_toList___redArg___lam__0(
    mut v_inst_1500_: *mut crate::leanh::LeanObject,
    mut v_inst_1501_: *mut crate::leanh::LeanObject,
    mut v_it_1502_: *mut crate::leanh::LeanObject,
    mut v_acc_1503_: *mut crate::leanh::LeanObject,
    mut v_recur_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_next_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_val_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v_succ_x3f_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_unused_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1505_ = crate::leanh::lean_ctor_get(v_it_1502_, 0);
                crate::leanh::lean_inc(v_next_1505_);
                if crate::leanh::lean_obj_tag(v_next_1505_) == 0 {
                    crate::leanh::lean_dec_ref(v_recur_1504_);
                    crate::leanh::lean_dec_ref(v_it_1502_);
                    crate::leanh::lean_dec_ref(v_inst_1501_);
                    crate::leanh::lean_dec_ref(v_inst_1500_);
                    return v_acc_1503_;
                } else {
                    v_upperBound_1506_ = crate::leanh::lean_ctor_get(v_it_1502_, 1);
                    v_isSharedCheck_1520_ = (!crate::leanh::lean_is_exclusive(v_it_1502_)) as u8;
                    if v_isSharedCheck_1520_ == 0 {
                        v_unused_1521_ = crate::leanh::lean_ctor_get(v_it_1502_, 0);
                        crate::leanh::lean_dec(v_unused_1521_);
                        v___x_1508_ = v_it_1502_;
                        v_isShared_1509_ = v_isSharedCheck_1520_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upperBound_1506_);
                        crate::leanh::lean_dec(v_it_1502_);
                        v___x_1508_ = crate::leanh::lean_box(0);
                        v_isShared_1509_ = v_isSharedCheck_1520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1510_ = crate::leanh::lean_ctor_get(v_next_1505_, 0);
                crate::leanh::lean_inc_n(v_val_1510_, 2);
                crate::leanh::lean_dec_ref_known(v_next_1505_, 1);
                crate::leanh::lean_inc(v_upperBound_1506_);
                v___x_1511_ =
                    crate::leanh::lean_apply_2(v_inst_1500_, v_val_1510_, v_upperBound_1506_);
                v___x_1512_ = (crate::leanh::lean_unbox(v___x_1511_) as u8);
                if v___x_1512_ == 0 {
                    crate::leanh::lean_dec(v_val_1510_);
                    crate::leanh::lean_del_object(v___x_1508_);
                    crate::leanh::lean_dec(v_upperBound_1506_);
                    crate::leanh::lean_dec_ref(v_recur_1504_);
                    crate::leanh::lean_dec_ref(v_inst_1501_);
                    return v_acc_1503_;
                } else {
                    v_succ_x3f_1513_ = crate::leanh::lean_ctor_get(v_inst_1501_, 0);
                    crate::leanh::lean_inc_ref(v_succ_x3f_1513_);
                    crate::leanh::lean_dec_ref(v_inst_1501_);
                    crate::leanh::lean_inc(v_val_1510_);
                    v___x_1514_ = crate::leanh::lean_apply_1(v_succ_x3f_1513_, v_val_1510_);
                    if v_isShared_1509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1514_);
                        v___x_1516_ = v___x_1508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_upperBound_1506_);
                        v___x_1516_ = v_reuseFailAlloc_1519_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1517_ = lean_array_push(v_acc_1503_, v_val_1510_);
                v___x_1518_ = crate::leanh::lean_apply_3(
                    v_recur_1504_,
                    v___x_1516_,
                    v___x_1517_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_toList___redArg(
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
    mut v_r_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___f_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1525_ = crate::leanh::lean_ctor_get(v_r_1524_, 0);
                v_upper_1526_ = crate::leanh::lean_ctor_get(v_r_1524_, 1);
                v_isSharedCheck_1538_ = (!crate::leanh::lean_is_exclusive(v_r_1524_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1528_ = v_r_1524_;
                    v_isShared_1529_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1526_);
                    crate::leanh::lean_inc(v_lower_1525_);
                    crate::leanh::lean_dec(v_r_1524_);
                    v___x_1528_ = crate::leanh::lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1530_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1530_, 0, v_inst_1522_);
                crate::leanh::lean_closure_set(v___f_1530_, 1, v_inst_1523_);
                v___x_1531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1531_, 0, v_lower_1525_);
                if v_isShared_1529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1531_);
                    v___x_1533_ = v___x_1528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_upper_1526_);
                    v___x_1533_ = v_reuseFailAlloc_1537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1534_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1535_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1530_,
                        v___x_1533_,
                        v___x_1534_,
                    );
                v___x_1536_ = lean_array_to_list(v___x_1535_);
                return v___x_1536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_toList(
    mut v_00_u03b1_1539_: *mut crate::leanh::LeanObject,
    mut v_inst_1540_: *mut crate::leanh::LeanObject,
    mut v_inst_1541_: *mut crate::leanh::LeanObject,
    mut v_inst_1542_: *mut crate::leanh::LeanObject,
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_r_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___f_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1546_ = crate::leanh::lean_ctor_get(v_r_1545_, 0);
                v_upper_1547_ = crate::leanh::lean_ctor_get(v_r_1545_, 1);
                v_isSharedCheck_1559_ = (!crate::leanh::lean_is_exclusive(v_r_1545_)) as u8;
                if v_isSharedCheck_1559_ == 0 {
                    v___x_1549_ = v_r_1545_;
                    v_isShared_1550_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1547_);
                    crate::leanh::lean_inc(v_lower_1546_);
                    crate::leanh::lean_dec(v_r_1545_);
                    v___x_1549_ = crate::leanh::lean_box(0);
                    v_isShared_1550_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1551_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1551_, 0, v_inst_1541_);
                crate::leanh::lean_closure_set(v___f_1551_, 1, v_inst_1542_);
                v___x_1552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1552_, 0, v_lower_1546_);
                if v_isShared_1550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1549_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_upper_1547_);
                    v___x_1554_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1555_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1556_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1551_,
                        v___x_1554_,
                        v___x_1555_,
                    );
                v___x_1557_ = lean_array_to_list(v___x_1556_);
                return v___x_1557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_toArray___redArg(
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
    mut v_inst_1561_: *mut crate::leanh::LeanObject,
    mut v_r_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___f_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1563_ = crate::leanh::lean_ctor_get(v_r_1562_, 0);
                v_upper_1564_ = crate::leanh::lean_ctor_get(v_r_1562_, 1);
                v_isSharedCheck_1575_ = (!crate::leanh::lean_is_exclusive(v_r_1562_)) as u8;
                if v_isSharedCheck_1575_ == 0 {
                    v___x_1566_ = v_r_1562_;
                    v_isShared_1567_ = v_isSharedCheck_1575_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1564_);
                    crate::leanh::lean_inc(v_lower_1563_);
                    crate::leanh::lean_dec(v_r_1562_);
                    v___x_1566_ = crate::leanh::lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1568_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1568_, 0, v_inst_1560_);
                crate::leanh::lean_closure_set(v___f_1568_, 1, v_inst_1561_);
                v___x_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1569_, 0, v_lower_1563_);
                if v_isShared_1567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1566_, 0, v___x_1569_);
                    v___x_1571_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1574_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_upper_1564_);
                    v___x_1571_ = v_reuseFailAlloc_1574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1572_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1573_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1568_,
                        v___x_1571_,
                        v___x_1572_,
                    );
                return v___x_1573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_toArray(
    mut v_00_u03b1_1576_: *mut crate::leanh::LeanObject,
    mut v_inst_1577_: *mut crate::leanh::LeanObject,
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_inst_1579_: *mut crate::leanh::LeanObject,
    mut v_inst_1580_: *mut crate::leanh::LeanObject,
    mut v_inst_1581_: *mut crate::leanh::LeanObject,
    mut v_r_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___f_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1583_ = crate::leanh::lean_ctor_get(v_r_1582_, 0);
                v_upper_1584_ = crate::leanh::lean_ctor_get(v_r_1582_, 1);
                v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v_r_1582_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1586_ = v_r_1582_;
                    v_isShared_1587_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1584_);
                    crate::leanh::lean_inc(v_lower_1583_);
                    crate::leanh::lean_dec(v_r_1582_);
                    v___x_1586_ = crate::leanh::lean_box(0);
                    v_isShared_1587_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1588_ = crate::leanh::lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1588_, 0, v_inst_1578_);
                crate::leanh::lean_closure_set(v___f_1588_, 1, v_inst_1579_);
                v___x_1589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1589_, 0, v_lower_1583_);
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1589_);
                    v___x_1591_ = v___x_1586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_upper_1584_);
                    v___x_1591_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1592_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1593_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1588_,
                        v___x_1591_,
                        v___x_1592_,
                    );
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_size___redArg(
    mut v_inst_1596_: *mut crate::leanh::LeanObject,
    mut v_r_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_1598_ = crate::leanh::lean_ctor_get(v_r_1597_, 0);
    crate::leanh::lean_inc(v_lower_1598_);
    v_upper_1599_ = crate::leanh::lean_ctor_get(v_r_1597_, 1);
    crate::leanh::lean_inc(v_upper_1599_);
    crate::leanh::lean_dec_ref(v_r_1597_);
    v___x_1600_ = crate::leanh::lean_apply_2(v_inst_1596_, v_lower_1598_, v_upper_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Std_Rco_size(
    mut v_00_u03b1_1601_: *mut crate::leanh::LeanObject,
    mut v_inst_1602_: *mut crate::leanh::LeanObject,
    mut v_r_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_1604_ = crate::leanh::lean_ctor_get(v_r_1603_, 0);
    crate::leanh::lean_inc(v_lower_1604_);
    v_upper_1605_ = crate::leanh::lean_ctor_get(v_r_1603_, 1);
    crate::leanh::lean_inc(v_upper_1605_);
    crate::leanh::lean_dec_ref(v_r_1603_);
    v___x_1606_ = crate::leanh::lean_apply_2(v_inst_1602_, v_lower_1604_, v_upper_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
    mut v_inst_1608_: *mut crate::leanh::LeanObject,
    mut v_inst_1609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1610_: *mut crate::leanh::LeanObject,
    mut v_r_1611_: *mut crate::leanh::LeanObject,
    mut v_init_1612_: *mut crate::leanh::LeanObject,
    mut v_f_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1614_ = crate::leanh::lean_ctor_get(v_inst_1607_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1614_);
    v_lower_1615_ = crate::leanh::lean_ctor_get(v_r_1611_, 0);
    crate::leanh::lean_inc(v_lower_1615_);
    v_upper_1616_ = crate::leanh::lean_ctor_get(v_r_1611_, 1);
    crate::leanh::lean_inc(v_upper_1616_);
    crate::leanh::lean_dec_ref(v_r_1611_);
    v_toBind_1617_ = crate::leanh::lean_ctor_get(v_inst_1607_, 1);
    crate::leanh::lean_inc(v_toBind_1617_);
    crate::leanh::lean_dec_ref(v_inst_1607_);
    v_toPure_1618_ = crate::leanh::lean_ctor_get(v_toApplicative_1614_, 1);
    crate::leanh::lean_inc_n(v_toPure_1618_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1614_);
    v___f_1619_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1619_, 0, v_toPure_1618_);
    v___f_1620_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
    crate::leanh::lean_closure_set(v___f_1620_, 0, v_inst_1608_);
    crate::leanh::lean_closure_set(v___f_1620_, 1, v_upper_1616_);
    crate::leanh::lean_closure_set(v___f_1620_, 2, v_toPure_1618_);
    crate::leanh::lean_closure_set(v___f_1620_, 3, v_inst_1609_);
    crate::leanh::lean_closure_set(v___f_1620_, 4, v_f_1613_);
    crate::leanh::lean_closure_set(v___f_1620_, 5, v_toBind_1617_);
    crate::leanh::lean_closure_set(v___f_1620_, 6, v___f_1619_);
    v___x_1621_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1620_,
        v_lower_1615_,
        v_init_1612_,
        crate::leanh::lean_box(0),
    );
    return v___x_1621_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v_inst_1623_: *mut crate::leanh::LeanObject,
    mut v_inst_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1625_ = crate::leanh::lean_alloc_closure(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1625_, 0, v_inst_1624_);
    crate::leanh::lean_closure_set(v___f_1625_, 1, v_inst_1623_);
    crate::leanh::lean_closure_set(v___f_1625_, 2, v_inst_1622_);
    return v___f_1625_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1626_: *mut crate::leanh::LeanObject,
    mut v_m_1627_: *mut crate::leanh::LeanObject,
    mut v_inst_1628_: *mut crate::leanh::LeanObject,
    mut v_inst_1629_: *mut crate::leanh::LeanObject,
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_inst_1631_: *mut crate::leanh::LeanObject,
    mut v_inst_1632_: *mut crate::leanh::LeanObject,
    mut v_inst_1633_: *mut crate::leanh::LeanObject,
    mut v_inst_1634_: *mut crate::leanh::LeanObject,
    mut v_inst_1635_: *mut crate::leanh::LeanObject,
    mut v_inst_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1637_ = crate::leanh::lean_alloc_closure(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1637_, 0, v_inst_1635_);
    crate::leanh::lean_closure_set(v___f_1637_, 1, v_inst_1631_);
    crate::leanh::lean_closure_set(v___f_1637_, 2, v_inst_1628_);
    return v___f_1637_;
}
pub unsafe fn l_Std_Rci_Internal_iter___redArg(
    mut v_r_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1639_, 0, v_r_1638_);
    return v___x_1639_;
}
pub unsafe fn l_Std_Rci_Internal_iter(
    mut v_00_u03b1_1640_: *mut crate::leanh::LeanObject,
    mut v_inst_1641_: *mut crate::leanh::LeanObject,
    mut v_r_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1643_, 0, v_r_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Std_Rci_Internal_iter___boxed(
    mut v_00_u03b1_1644_: *mut crate::leanh::LeanObject,
    mut v_inst_1645_: *mut crate::leanh::LeanObject,
    mut v_r_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Std_Rci_Internal_iter(v_00_u03b1_1644_, v_inst_1645_, v_r_1646_);
    crate::leanh::lean_dec_ref(v_inst_1645_);
    return v_res_1647_;
}
pub unsafe fn l_Std_Rci_toList___redArg___lam__0(
    mut v_inst_1648_: *mut crate::leanh::LeanObject,
    mut v_it_1649_: *mut crate::leanh::LeanObject,
    mut v_acc_1650_: *mut crate::leanh::LeanObject,
    mut v_recur_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_1649_) == 0 {
        crate::leanh::lean_dec_ref(v_recur_1651_);
        crate::leanh::lean_dec_ref(v_inst_1648_);
        return v_acc_1650_;
    } else {
        let mut v_val_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1652_ = crate::leanh::lean_ctor_get(v_it_1649_, 0);
        crate::leanh::lean_inc_n(v_val_1652_, 2);
        crate::leanh::lean_dec_ref_known(v_it_1649_, 1);
        v_succ_x3f_1653_ = crate::leanh::lean_ctor_get(v_inst_1648_, 0);
        crate::leanh::lean_inc_ref(v_succ_x3f_1653_);
        crate::leanh::lean_dec_ref(v_inst_1648_);
        v___x_1654_ = crate::leanh::lean_apply_1(v_succ_x3f_1653_, v_val_1652_);
        v___x_1655_ = lean_array_push(v_acc_1650_, v_val_1652_);
        v___x_1656_ = crate::leanh::lean_apply_3(
            v_recur_1651_,
            v___x_1654_,
            v___x_1655_,
            crate::leanh::lean_box(0),
        );
        return v___x_1656_;
    }
}
pub unsafe fn l_Std_Rci_toList___redArg(
    mut v_inst_1657_: *mut crate::leanh::LeanObject,
    mut v_r_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1659_ = crate::leanh::lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1659_, 0, v_inst_1657_);
    v___x_1660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1660_, 0, v_r_1658_);
    v___x_1661_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1662_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1659_,
        v___x_1660_,
        v___x_1661_,
    );
    v___x_1663_ = lean_array_to_list(v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Std_Rci_toList(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
    mut v_inst_1666_: *mut crate::leanh::LeanObject,
    mut v_inst_1667_: *mut crate::leanh::LeanObject,
    mut v_r_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1669_ = crate::leanh::lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1669_, 0, v_inst_1665_);
    v___x_1670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1670_, 0, v_r_1668_);
    v___x_1671_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1672_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1669_,
        v___x_1670_,
        v___x_1671_,
    );
    v___x_1673_ = lean_array_to_list(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn l_Std_Rci_toArray___redArg(
    mut v_inst_1674_: *mut crate::leanh::LeanObject,
    mut v_r_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1676_ = crate::leanh::lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1676_, 0, v_inst_1674_);
    v___x_1677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1677_, 0, v_r_1675_);
    v___x_1678_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1679_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1676_,
        v___x_1677_,
        v___x_1678_,
    );
    return v___x_1679_;
}
pub unsafe fn l_Std_Rci_toArray(
    mut v_00_u03b1_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_inst_1682_: *mut crate::leanh::LeanObject,
    mut v_inst_1683_: *mut crate::leanh::LeanObject,
    mut v_r_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1685_ = crate::leanh::lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1685_, 0, v_inst_1681_);
    v___x_1686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1686_, 0, v_r_1684_);
    v___x_1687_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1688_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1685_,
        v___x_1686_,
        v___x_1687_,
    );
    return v___x_1688_;
}
pub unsafe fn l_Std_Rci_size___redArg(
    mut v_inst_1689_: *mut crate::leanh::LeanObject,
    mut v_r_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = crate::leanh::lean_apply_1(v_inst_1689_, v_r_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Std_Rci_size(
    mut v_00_u03b1_1692_: *mut crate::leanh::LeanObject,
    mut v_inst_1693_: *mut crate::leanh::LeanObject,
    mut v_r_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = crate::leanh::lean_apply_1(v_inst_1693_, v_r_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_toPure_1696_: *mut crate::leanh::LeanObject,
    mut v_inst_1697_: *mut crate::leanh::LeanObject,
    mut v_f_1698_: *mut crate::leanh::LeanObject,
    mut v_toBind_1699_: *mut crate::leanh::LeanObject,
    mut v___f_1700_: *mut crate::leanh::LeanObject,
    mut v_next_1701_: *mut crate::leanh::LeanObject,
    mut v_acc_1702_: *mut crate::leanh::LeanObject,
    mut v_h_1703_: *mut crate::leanh::LeanObject,
    mut v_G_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_next_1701_);
    v___f_1705_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_1705_, 0, v_toPure_1696_);
    crate::leanh::lean_closure_set(v___f_1705_, 1, v_inst_1697_);
    crate::leanh::lean_closure_set(v___f_1705_, 2, v_next_1701_);
    crate::leanh::lean_closure_set(v___f_1705_, 3, v_G_1704_);
    v___x_1706_ = crate::leanh::lean_apply_3(
        v_f_1698_,
        v_next_1701_,
        crate::leanh::lean_box(0),
        v_acc_1702_,
    );
    crate::leanh::lean_inc(v_toBind_1699_);
    v___x_1707_ = crate::leanh::lean_apply_4(
        v_toBind_1699_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1706_,
        v___f_1700_,
    );
    v___x_1708_ = crate::leanh::lean_apply_4(
        v_toBind_1699_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1707_,
        v___f_1705_,
    );
    return v___x_1708_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_1709_: *mut crate::leanh::LeanObject,
    mut v_inst_1710_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1711_: *mut crate::leanh::LeanObject,
    mut v_r_1712_: *mut crate::leanh::LeanObject,
    mut v_init_1713_: *mut crate::leanh::LeanObject,
    mut v_f_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1715_ = crate::leanh::lean_ctor_get(v_inst_1709_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1715_);
    v_toBind_1716_ = crate::leanh::lean_ctor_get(v_inst_1709_, 1);
    crate::leanh::lean_inc(v_toBind_1716_);
    crate::leanh::lean_dec_ref(v_inst_1709_);
    v_toPure_1717_ = crate::leanh::lean_ctor_get(v_toApplicative_1715_, 1);
    crate::leanh::lean_inc_n(v_toPure_1717_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1715_);
    v___f_1718_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1718_, 0, v_toPure_1717_);
    v___f_1719_ = crate::leanh::lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
    crate::leanh::lean_closure_set(v___f_1719_, 0, v_toPure_1717_);
    crate::leanh::lean_closure_set(v___f_1719_, 1, v_inst_1710_);
    crate::leanh::lean_closure_set(v___f_1719_, 2, v_f_1714_);
    crate::leanh::lean_closure_set(v___f_1719_, 3, v_toBind_1716_);
    crate::leanh::lean_closure_set(v___f_1719_, 4, v___f_1718_);
    v___x_1720_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1719_,
        v_r_1712_,
        v_init_1713_,
        crate::leanh::lean_box(0),
    );
    return v___x_1720_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1723_ = crate::leanh::lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_1723_, 0, v_inst_1722_);
    crate::leanh::lean_closure_set(v___f_1723_, 1, v_inst_1721_);
    return v___f_1723_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1724_: *mut crate::leanh::LeanObject,
    mut v_m_1725_: *mut crate::leanh::LeanObject,
    mut v_inst_1726_: *mut crate::leanh::LeanObject,
    mut v_inst_1727_: *mut crate::leanh::LeanObject,
    mut v_inst_1728_: *mut crate::leanh::LeanObject,
    mut v_inst_1729_: *mut crate::leanh::LeanObject,
    mut v_inst_1730_: *mut crate::leanh::LeanObject,
    mut v_inst_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1732_ = crate::leanh::lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_1732_, 0, v_inst_1730_);
    crate::leanh::lean_closure_set(v___f_1732_, 1, v_inst_1726_);
    return v___f_1732_;
}
pub unsafe fn l_Std_Roc_Internal_iter___redArg(
    mut v_inst_1733_: *mut crate::leanh::LeanObject,
    mut v_r_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1735_ = crate::leanh::lean_ctor_get(v_inst_1733_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1735_);
                crate::leanh::lean_dec_ref(v_inst_1733_);
                v_lower_1736_ = crate::leanh::lean_ctor_get(v_r_1734_, 0);
                v_upper_1737_ = crate::leanh::lean_ctor_get(v_r_1734_, 1);
                v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v_r_1734_)) as u8;
                if v_isSharedCheck_1745_ == 0 {
                    v___x_1739_ = v_r_1734_;
                    v_isShared_1740_ = v_isSharedCheck_1745_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1737_);
                    crate::leanh::lean_inc(v_lower_1736_);
                    crate::leanh::lean_dec(v_r_1734_);
                    v___x_1739_ = crate::leanh::lean_box(0);
                    v_isShared_1740_ = v_isSharedCheck_1745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1741_ = crate::leanh::lean_apply_1(v_succ_x3f_1735_, v_lower_1736_);
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1741_);
                    v___x_1743_ = v___x_1739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_upper_1737_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_Internal_iter(
    mut v_00_u03b1_1746_: *mut crate::leanh::LeanObject,
    mut v_inst_1747_: *mut crate::leanh::LeanObject,
    mut v_r_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1749_ = crate::leanh::lean_ctor_get(v_inst_1747_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1749_);
                crate::leanh::lean_dec_ref(v_inst_1747_);
                v_lower_1750_ = crate::leanh::lean_ctor_get(v_r_1748_, 0);
                v_upper_1751_ = crate::leanh::lean_ctor_get(v_r_1748_, 1);
                v_isSharedCheck_1759_ = (!crate::leanh::lean_is_exclusive(v_r_1748_)) as u8;
                if v_isSharedCheck_1759_ == 0 {
                    v___x_1753_ = v_r_1748_;
                    v_isShared_1754_ = v_isSharedCheck_1759_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1751_);
                    crate::leanh::lean_inc(v_lower_1750_);
                    crate::leanh::lean_dec(v_r_1748_);
                    v___x_1753_ = crate::leanh::lean_box(0);
                    v_isShared_1754_ = v_isSharedCheck_1759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1755_ = crate::leanh::lean_apply_1(v_succ_x3f_1749_, v_lower_1750_);
                if v_isShared_1754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_upper_1751_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toList___redArg___lam__0(
    mut v_inst_1760_: *mut crate::leanh::LeanObject,
    mut v_succ_x3f_1761_: *mut crate::leanh::LeanObject,
    mut v_it_1762_: *mut crate::leanh::LeanObject,
    mut v_acc_1763_: *mut crate::leanh::LeanObject,
    mut v_recur_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_next_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v_val_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut v_unused_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1765_ = crate::leanh::lean_ctor_get(v_it_1762_, 0);
                crate::leanh::lean_inc(v_next_1765_);
                if crate::leanh::lean_obj_tag(v_next_1765_) == 0 {
                    crate::leanh::lean_dec_ref(v_recur_1764_);
                    crate::leanh::lean_dec_ref(v_it_1762_);
                    crate::leanh::lean_dec_ref(v_succ_x3f_1761_);
                    crate::leanh::lean_dec_ref(v_inst_1760_);
                    return v_acc_1763_;
                } else {
                    v_upperBound_1766_ = crate::leanh::lean_ctor_get(v_it_1762_, 1);
                    v_isSharedCheck_1779_ = (!crate::leanh::lean_is_exclusive(v_it_1762_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v_unused_1780_ = crate::leanh::lean_ctor_get(v_it_1762_, 0);
                        crate::leanh::lean_dec(v_unused_1780_);
                        v___x_1768_ = v_it_1762_;
                        v_isShared_1769_ = v_isSharedCheck_1779_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upperBound_1766_);
                        crate::leanh::lean_dec(v_it_1762_);
                        v___x_1768_ = crate::leanh::lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1770_ = crate::leanh::lean_ctor_get(v_next_1765_, 0);
                crate::leanh::lean_inc_n(v_val_1770_, 2);
                crate::leanh::lean_dec_ref_known(v_next_1765_, 1);
                crate::leanh::lean_inc(v_upperBound_1766_);
                v___x_1771_ =
                    crate::leanh::lean_apply_2(v_inst_1760_, v_val_1770_, v_upperBound_1766_);
                v___x_1772_ = (crate::leanh::lean_unbox(v___x_1771_) as u8);
                if v___x_1772_ == 0 {
                    crate::leanh::lean_dec(v_val_1770_);
                    crate::leanh::lean_del_object(v___x_1768_);
                    crate::leanh::lean_dec(v_upperBound_1766_);
                    crate::leanh::lean_dec_ref(v_recur_1764_);
                    crate::leanh::lean_dec_ref(v_succ_x3f_1761_);
                    return v_acc_1763_;
                } else {
                    crate::leanh::lean_inc(v_val_1770_);
                    v___x_1773_ = crate::leanh::lean_apply_1(v_succ_x3f_1761_, v_val_1770_);
                    if v_isShared_1769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1773_);
                        v___x_1775_ = v___x_1768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1773_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_upperBound_1766_);
                        v___x_1775_ = v_reuseFailAlloc_1778_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1776_ = lean_array_push(v_acc_1763_, v_val_1770_);
                v___x_1777_ = crate::leanh::lean_apply_3(
                    v_recur_1764_,
                    v___x_1775_,
                    v___x_1776_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toList___redArg(
    mut v_inst_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_r_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___f_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1784_ = crate::leanh::lean_ctor_get(v_inst_1782_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1784_);
                crate::leanh::lean_dec_ref(v_inst_1782_);
                v_lower_1785_ = crate::leanh::lean_ctor_get(v_r_1783_, 0);
                v_upper_1786_ = crate::leanh::lean_ctor_get(v_r_1783_, 1);
                v_isSharedCheck_1798_ = (!crate::leanh::lean_is_exclusive(v_r_1783_)) as u8;
                if v_isSharedCheck_1798_ == 0 {
                    v___x_1788_ = v_r_1783_;
                    v_isShared_1789_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1786_);
                    crate::leanh::lean_inc(v_lower_1785_);
                    crate::leanh::lean_dec(v_r_1783_);
                    v___x_1788_ = crate::leanh::lean_box(0);
                    v_isShared_1789_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_1784_);
                v___f_1790_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1790_, 0, v_inst_1781_);
                crate::leanh::lean_closure_set(v___f_1790_, 1, v_succ_x3f_1784_);
                v___x_1791_ = crate::leanh::lean_apply_1(v_succ_x3f_1784_, v_lower_1785_);
                if v_isShared_1789_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1791_);
                    v___x_1793_ = v___x_1788_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_upper_1786_);
                    v___x_1793_ = v_reuseFailAlloc_1797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1794_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1795_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1790_,
                        v___x_1793_,
                        v___x_1794_,
                    );
                v___x_1796_ = lean_array_to_list(v___x_1795_);
                return v___x_1796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toList(
    mut v_00_u03b1_1799_: *mut crate::leanh::LeanObject,
    mut v_inst_1800_: *mut crate::leanh::LeanObject,
    mut v_inst_1801_: *mut crate::leanh::LeanObject,
    mut v_inst_1802_: *mut crate::leanh::LeanObject,
    mut v_inst_1803_: *mut crate::leanh::LeanObject,
    mut v_inst_1804_: *mut crate::leanh::LeanObject,
    mut v_r_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___f_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1806_ = crate::leanh::lean_ctor_get(v_inst_1802_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1806_);
                crate::leanh::lean_dec_ref(v_inst_1802_);
                v_lower_1807_ = crate::leanh::lean_ctor_get(v_r_1805_, 0);
                v_upper_1808_ = crate::leanh::lean_ctor_get(v_r_1805_, 1);
                v_isSharedCheck_1820_ = (!crate::leanh::lean_is_exclusive(v_r_1805_)) as u8;
                if v_isSharedCheck_1820_ == 0 {
                    v___x_1810_ = v_r_1805_;
                    v_isShared_1811_ = v_isSharedCheck_1820_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1808_);
                    crate::leanh::lean_inc(v_lower_1807_);
                    crate::leanh::lean_dec(v_r_1805_);
                    v___x_1810_ = crate::leanh::lean_box(0);
                    v_isShared_1811_ = v_isSharedCheck_1820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_1806_);
                v___f_1812_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1812_, 0, v_inst_1801_);
                crate::leanh::lean_closure_set(v___f_1812_, 1, v_succ_x3f_1806_);
                v___x_1813_ = crate::leanh::lean_apply_1(v_succ_x3f_1806_, v_lower_1807_);
                if v_isShared_1811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1810_, 0, v___x_1813_);
                    v___x_1815_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_upper_1808_);
                    v___x_1815_ = v_reuseFailAlloc_1819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1816_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1817_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1812_,
                        v___x_1815_,
                        v___x_1816_,
                    );
                v___x_1818_ = lean_array_to_list(v___x_1817_);
                return v___x_1818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toArray___redArg(
    mut v_inst_1821_: *mut crate::leanh::LeanObject,
    mut v_inst_1822_: *mut crate::leanh::LeanObject,
    mut v_r_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1829_: u8 = 0;
    let mut v___f_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1824_ = crate::leanh::lean_ctor_get(v_inst_1822_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1824_);
                crate::leanh::lean_dec_ref(v_inst_1822_);
                v_lower_1825_ = crate::leanh::lean_ctor_get(v_r_1823_, 0);
                v_upper_1826_ = crate::leanh::lean_ctor_get(v_r_1823_, 1);
                v_isSharedCheck_1837_ = (!crate::leanh::lean_is_exclusive(v_r_1823_)) as u8;
                if v_isSharedCheck_1837_ == 0 {
                    v___x_1828_ = v_r_1823_;
                    v_isShared_1829_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1826_);
                    crate::leanh::lean_inc(v_lower_1825_);
                    crate::leanh::lean_dec(v_r_1823_);
                    v___x_1828_ = crate::leanh::lean_box(0);
                    v_isShared_1829_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_1824_);
                v___f_1830_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1830_, 0, v_inst_1821_);
                crate::leanh::lean_closure_set(v___f_1830_, 1, v_succ_x3f_1824_);
                v___x_1831_ = crate::leanh::lean_apply_1(v_succ_x3f_1824_, v_lower_1825_);
                if v_isShared_1829_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1828_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_upper_1826_);
                    v___x_1833_ = v_reuseFailAlloc_1836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1834_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1835_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1830_,
                        v___x_1833_,
                        v___x_1834_,
                    );
                return v___x_1835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toArray(
    mut v_00_u03b1_1838_: *mut crate::leanh::LeanObject,
    mut v_inst_1839_: *mut crate::leanh::LeanObject,
    mut v_inst_1840_: *mut crate::leanh::LeanObject,
    mut v_inst_1841_: *mut crate::leanh::LeanObject,
    mut v_inst_1842_: *mut crate::leanh::LeanObject,
    mut v_inst_1843_: *mut crate::leanh::LeanObject,
    mut v_r_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___f_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1845_ = crate::leanh::lean_ctor_get(v_inst_1841_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1845_);
                crate::leanh::lean_dec_ref(v_inst_1841_);
                v_lower_1846_ = crate::leanh::lean_ctor_get(v_r_1844_, 0);
                v_upper_1847_ = crate::leanh::lean_ctor_get(v_r_1844_, 1);
                v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v_r_1844_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1849_ = v_r_1844_;
                    v_isShared_1850_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1847_);
                    crate::leanh::lean_inc(v_lower_1846_);
                    crate::leanh::lean_dec(v_r_1844_);
                    v___x_1849_ = crate::leanh::lean_box(0);
                    v_isShared_1850_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_1845_);
                v___f_1851_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1851_, 0, v_inst_1840_);
                crate::leanh::lean_closure_set(v___f_1851_, 1, v_succ_x3f_1845_);
                v___x_1852_ = crate::leanh::lean_apply_1(v_succ_x3f_1845_, v_lower_1846_);
                if v_isShared_1850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1852_);
                    v___x_1854_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_upper_1847_);
                    v___x_1854_ = v_reuseFailAlloc_1857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1855_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_1856_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1851_,
                        v___x_1854_,
                        v___x_1855_,
                    );
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_size___redArg(
    mut v_inst_1859_: *mut crate::leanh::LeanObject,
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_r_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_1862_ = crate::leanh::lean_ctor_get(v_inst_1860_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_1862_);
    crate::leanh::lean_dec_ref(v_inst_1860_);
    v_lower_1863_ = crate::leanh::lean_ctor_get(v_r_1861_, 0);
    crate::leanh::lean_inc(v_lower_1863_);
    v_upper_1864_ = crate::leanh::lean_ctor_get(v_r_1861_, 1);
    crate::leanh::lean_inc(v_upper_1864_);
    crate::leanh::lean_dec_ref(v_r_1861_);
    v___x_1865_ = crate::leanh::lean_apply_1(v_succ_x3f_1862_, v_lower_1863_);
    if crate::leanh::lean_obj_tag(v___x_1865_) == 0 {
        let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_upper_1864_);
        crate::leanh::lean_dec_ref(v_inst_1859_);
        v___x_1866_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1866_;
    } else {
        let mut v_val_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1867_ = crate::leanh::lean_ctor_get(v___x_1865_, 0);
        crate::leanh::lean_inc(v_val_1867_);
        crate::leanh::lean_dec_ref_known(v___x_1865_, 1);
        v___x_1868_ = crate::leanh::lean_apply_2(v_inst_1859_, v_val_1867_, v_upper_1864_);
        return v___x_1868_;
    }
}
pub unsafe fn l_Std_Roc_size(
    mut v_00_u03b1_1869_: *mut crate::leanh::LeanObject,
    mut v_inst_1870_: *mut crate::leanh::LeanObject,
    mut v_inst_1871_: *mut crate::leanh::LeanObject,
    mut v_r_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_1873_ = crate::leanh::lean_ctor_get(v_inst_1871_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_1873_);
    crate::leanh::lean_dec_ref(v_inst_1871_);
    v_lower_1874_ = crate::leanh::lean_ctor_get(v_r_1872_, 0);
    crate::leanh::lean_inc(v_lower_1874_);
    v_upper_1875_ = crate::leanh::lean_ctor_get(v_r_1872_, 1);
    crate::leanh::lean_inc(v_upper_1875_);
    crate::leanh::lean_dec_ref(v_r_1872_);
    v___x_1876_ = crate::leanh::lean_apply_1(v_succ_x3f_1873_, v_lower_1874_);
    if crate::leanh::lean_obj_tag(v___x_1876_) == 0 {
        let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_upper_1875_);
        crate::leanh::lean_dec_ref(v_inst_1870_);
        v___x_1877_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1877_;
    } else {
        let mut v_val_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1878_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
        crate::leanh::lean_inc(v_val_1878_);
        crate::leanh::lean_dec_ref_known(v___x_1876_, 1);
        v___x_1879_ = crate::leanh::lean_apply_2(v_inst_1870_, v_val_1878_, v_upper_1875_);
        return v___x_1879_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1(
    mut v_toPure_1880_: *mut crate::leanh::LeanObject,
    mut v_succ_x3f_1881_: *mut crate::leanh::LeanObject,
    mut v_next_1882_: *mut crate::leanh::LeanObject,
    mut v_G_1883_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1884_) == 0 {
        let mut v_a_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_1883_);
        crate::leanh::lean_dec(v_next_1882_);
        crate::leanh::lean_dec_ref(v_succ_x3f_1881_);
        v_a_1885_ = crate::leanh::lean_ctor_get(v_____do__lift_1884_, 0);
        crate::leanh::lean_inc(v_a_1885_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1884_, 1);
        v___x_1886_ =
            crate::leanh::lean_apply_2(v_toPure_1880_, crate::leanh::lean_box(0), v_a_1885_);
        return v___x_1886_;
    } else {
        let mut v_a_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1887_ = crate::leanh::lean_ctor_get(v_____do__lift_1884_, 0);
        crate::leanh::lean_inc(v_a_1887_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1884_, 1);
        v___x_1888_ = crate::leanh::lean_apply_1(v_succ_x3f_1881_, v_next_1882_);
        if crate::leanh::lean_obj_tag(v___x_1888_) == 0 {
            let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_G_1883_);
            v___x_1889_ =
                crate::leanh::lean_apply_2(v_toPure_1880_, crate::leanh::lean_box(0), v_a_1887_);
            return v___x_1889_;
        } else {
            let mut v_val_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_1880_);
            v_val_1890_ = crate::leanh::lean_ctor_get(v___x_1888_, 0);
            crate::leanh::lean_inc(v_val_1890_);
            crate::leanh::lean_dec_ref_known(v___x_1888_, 1);
            v___x_1891_ = crate::leanh::lean_apply_4(
                v_G_1883_,
                v_val_1890_,
                v_a_1887_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1891_;
        }
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_1892_: *mut crate::leanh::LeanObject,
    mut v_upper_1893_: *mut crate::leanh::LeanObject,
    mut v_toPure_1894_: *mut crate::leanh::LeanObject,
    mut v_succ_x3f_1895_: *mut crate::leanh::LeanObject,
    mut v_f_1896_: *mut crate::leanh::LeanObject,
    mut v_toBind_1897_: *mut crate::leanh::LeanObject,
    mut v___f_1898_: *mut crate::leanh::LeanObject,
    mut v_next_1899_: *mut crate::leanh::LeanObject,
    mut v_acc_1900_: *mut crate::leanh::LeanObject,
    mut v_h_1901_: *mut crate::leanh::LeanObject,
    mut v_G_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    crate::leanh::lean_inc(v_next_1899_);
    v___x_1903_ = crate::leanh::lean_apply_2(v_inst_1892_, v_next_1899_, v_upper_1893_);
    v___x_1904_ = (crate::leanh::lean_unbox(v___x_1903_) as u8);
    if v___x_1904_ == 0 {
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_1902_);
        crate::leanh::lean_dec(v_next_1899_);
        crate::leanh::lean_dec(v___f_1898_);
        crate::leanh::lean_dec(v_toBind_1897_);
        crate::leanh::lean_dec(v_f_1896_);
        crate::leanh::lean_dec_ref(v_succ_x3f_1895_);
        v___x_1905_ =
            crate::leanh::lean_apply_2(v_toPure_1894_, crate::leanh::lean_box(0), v_acc_1900_);
        return v___x_1905_;
    } else {
        let mut v___f_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_next_1899_);
        v___f_1906_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_1906_, 0, v_toPure_1894_);
        crate::leanh::lean_closure_set(v___f_1906_, 1, v_succ_x3f_1895_);
        crate::leanh::lean_closure_set(v___f_1906_, 2, v_next_1899_);
        crate::leanh::lean_closure_set(v___f_1906_, 3, v_G_1902_);
        v___x_1907_ = crate::leanh::lean_apply_3(
            v_f_1896_,
            v_next_1899_,
            crate::leanh::lean_box(0),
            v_acc_1900_,
        );
        crate::leanh::lean_inc(v_toBind_1897_);
        v___x_1908_ = crate::leanh::lean_apply_4(
            v_toBind_1897_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1907_,
            v___f_1898_,
        );
        v___x_1909_ = crate::leanh::lean_apply_4(
            v_toBind_1897_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1908_,
            v___f_1906_,
        );
        return v___x_1909_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_1910_: *mut crate::leanh::LeanObject,
    mut v_inst_1911_: *mut crate::leanh::LeanObject,
    mut v_inst_1912_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1913_: *mut crate::leanh::LeanObject,
    mut v_r_1914_: *mut crate::leanh::LeanObject,
    mut v_init_1915_: *mut crate::leanh::LeanObject,
    mut v_f_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1917_ = crate::leanh::lean_ctor_get(v_inst_1911_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1917_);
    v_succ_x3f_1918_ = crate::leanh::lean_ctor_get(v_inst_1910_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_1918_, 2);
    crate::leanh::lean_dec_ref(v_inst_1910_);
    v_lower_1919_ = crate::leanh::lean_ctor_get(v_r_1914_, 0);
    crate::leanh::lean_inc(v_lower_1919_);
    v_upper_1920_ = crate::leanh::lean_ctor_get(v_r_1914_, 1);
    crate::leanh::lean_inc(v_upper_1920_);
    crate::leanh::lean_dec_ref(v_r_1914_);
    v_toBind_1921_ = crate::leanh::lean_ctor_get(v_inst_1911_, 1);
    crate::leanh::lean_inc(v_toBind_1921_);
    crate::leanh::lean_dec_ref(v_inst_1911_);
    v_toPure_1922_ = crate::leanh::lean_ctor_get(v_toApplicative_1917_, 1);
    crate::leanh::lean_inc(v_toPure_1922_);
    crate::leanh::lean_dec_ref(v_toApplicative_1917_);
    v___x_1923_ = crate::leanh::lean_apply_1(v_succ_x3f_1918_, v_lower_1919_);
    if crate::leanh::lean_obj_tag(v___x_1923_) == 0 {
        let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_1921_);
        crate::leanh::lean_dec(v_upper_1920_);
        crate::leanh::lean_dec_ref(v_succ_x3f_1918_);
        crate::leanh::lean_dec(v_f_1916_);
        crate::leanh::lean_dec_ref(v_inst_1912_);
        v___x_1924_ =
            crate::leanh::lean_apply_2(v_toPure_1922_, crate::leanh::lean_box(0), v_init_1915_);
        return v___x_1924_;
    } else {
        let mut v_val_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1925_ = crate::leanh::lean_ctor_get(v___x_1923_, 0);
        crate::leanh::lean_inc(v_val_1925_);
        crate::leanh::lean_dec_ref_known(v___x_1923_, 1);
        crate::leanh::lean_inc(v_toPure_1922_);
        v___f_1926_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_1926_, 0, v_toPure_1922_);
        v___f_1927_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 11, 7);
        crate::leanh::lean_closure_set(v___f_1927_, 0, v_inst_1912_);
        crate::leanh::lean_closure_set(v___f_1927_, 1, v_upper_1920_);
        crate::leanh::lean_closure_set(v___f_1927_, 2, v_toPure_1922_);
        crate::leanh::lean_closure_set(v___f_1927_, 3, v_succ_x3f_1918_);
        crate::leanh::lean_closure_set(v___f_1927_, 4, v_f_1916_);
        crate::leanh::lean_closure_set(v___f_1927_, 5, v_toBind_1921_);
        crate::leanh::lean_closure_set(v___f_1927_, 6, v___f_1926_);
        v___x_1928_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1927_,
            v_val_1925_,
            v_init_1915_,
            crate::leanh::lean_box(0),
        );
        return v___x_1928_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1929_: *mut crate::leanh::LeanObject,
    mut v_inst_1930_: *mut crate::leanh::LeanObject,
    mut v_inst_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1932_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1932_, 0, v_inst_1929_);
    crate::leanh::lean_closure_set(v___f_1932_, 1, v_inst_1931_);
    crate::leanh::lean_closure_set(v___f_1932_, 2, v_inst_1930_);
    return v___f_1932_;
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1933_: *mut crate::leanh::LeanObject,
    mut v_m_1934_: *mut crate::leanh::LeanObject,
    mut v_inst_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
    mut v_inst_1939_: *mut crate::leanh::LeanObject,
    mut v_inst_1940_: *mut crate::leanh::LeanObject,
    mut v_inst_1941_: *mut crate::leanh::LeanObject,
    mut v_inst_1942_: *mut crate::leanh::LeanObject,
    mut v_inst_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1944_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_1944_, 0, v_inst_1935_);
    crate::leanh::lean_closure_set(v___f_1944_, 1, v_inst_1942_);
    crate::leanh::lean_closure_set(v___f_1944_, 2, v_inst_1937_);
    return v___f_1944_;
}
pub unsafe fn l_Std_Roo_Internal_iter___redArg(
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_r_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1947_ = crate::leanh::lean_ctor_get(v_inst_1945_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1947_);
                crate::leanh::lean_dec_ref(v_inst_1945_);
                v_lower_1948_ = crate::leanh::lean_ctor_get(v_r_1946_, 0);
                v_upper_1949_ = crate::leanh::lean_ctor_get(v_r_1946_, 1);
                v_isSharedCheck_1957_ = (!crate::leanh::lean_is_exclusive(v_r_1946_)) as u8;
                if v_isSharedCheck_1957_ == 0 {
                    v___x_1951_ = v_r_1946_;
                    v_isShared_1952_ = v_isSharedCheck_1957_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1949_);
                    crate::leanh::lean_inc(v_lower_1948_);
                    crate::leanh::lean_dec(v_r_1946_);
                    v___x_1951_ = crate::leanh::lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1957_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1953_ = crate::leanh::lean_apply_1(v_succ_x3f_1947_, v_lower_1948_);
                if v_isShared_1952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_upper_1949_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_Internal_iter(
    mut v_00_u03b1_1958_: *mut crate::leanh::LeanObject,
    mut v_inst_1959_: *mut crate::leanh::LeanObject,
    mut v_r_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1961_ = crate::leanh::lean_ctor_get(v_inst_1959_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1961_);
                crate::leanh::lean_dec_ref(v_inst_1959_);
                v_lower_1962_ = crate::leanh::lean_ctor_get(v_r_1960_, 0);
                v_upper_1963_ = crate::leanh::lean_ctor_get(v_r_1960_, 1);
                v_isSharedCheck_1971_ = (!crate::leanh::lean_is_exclusive(v_r_1960_)) as u8;
                if v_isSharedCheck_1971_ == 0 {
                    v___x_1965_ = v_r_1960_;
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1963_);
                    crate::leanh::lean_inc(v_lower_1962_);
                    crate::leanh::lean_dec(v_r_1960_);
                    v___x_1965_ = crate::leanh::lean_box(0);
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1967_ = crate::leanh::lean_apply_1(v_succ_x3f_1961_, v_lower_1962_);
                if v_isShared_1966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1967_);
                    v___x_1969_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_upper_1963_);
                    v___x_1969_ = v_reuseFailAlloc_1970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toList___redArg___lam__0(
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_succ_x3f_1973_: *mut crate::leanh::LeanObject,
    mut v_it_1974_: *mut crate::leanh::LeanObject,
    mut v_acc_1975_: *mut crate::leanh::LeanObject,
    mut v_recur_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_next_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v_val_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1977_ = crate::leanh::lean_ctor_get(v_it_1974_, 0);
                crate::leanh::lean_inc(v_next_1977_);
                if crate::leanh::lean_obj_tag(v_next_1977_) == 0 {
                    crate::leanh::lean_dec_ref(v_recur_1976_);
                    crate::leanh::lean_dec_ref(v_it_1974_);
                    crate::leanh::lean_dec_ref(v_succ_x3f_1973_);
                    crate::leanh::lean_dec_ref(v_inst_1972_);
                    return v_acc_1975_;
                } else {
                    v_upperBound_1978_ = crate::leanh::lean_ctor_get(v_it_1974_, 1);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v_it_1974_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v_unused_1992_ = crate::leanh::lean_ctor_get(v_it_1974_, 0);
                        crate::leanh::lean_dec(v_unused_1992_);
                        v___x_1980_ = v_it_1974_;
                        v_isShared_1981_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upperBound_1978_);
                        crate::leanh::lean_dec(v_it_1974_);
                        v___x_1980_ = crate::leanh::lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1982_ = crate::leanh::lean_ctor_get(v_next_1977_, 0);
                crate::leanh::lean_inc_n(v_val_1982_, 2);
                crate::leanh::lean_dec_ref_known(v_next_1977_, 1);
                crate::leanh::lean_inc(v_upperBound_1978_);
                v___x_1983_ =
                    crate::leanh::lean_apply_2(v_inst_1972_, v_val_1982_, v_upperBound_1978_);
                v___x_1984_ = (crate::leanh::lean_unbox(v___x_1983_) as u8);
                if v___x_1984_ == 0 {
                    crate::leanh::lean_dec(v_val_1982_);
                    crate::leanh::lean_del_object(v___x_1980_);
                    crate::leanh::lean_dec(v_upperBound_1978_);
                    crate::leanh::lean_dec_ref(v_recur_1976_);
                    crate::leanh::lean_dec_ref(v_succ_x3f_1973_);
                    return v_acc_1975_;
                } else {
                    crate::leanh::lean_inc(v_val_1982_);
                    v___x_1985_ = crate::leanh::lean_apply_1(v_succ_x3f_1973_, v_val_1982_);
                    if v_isShared_1981_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_1985_);
                        v___x_1987_ = v___x_1980_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1985_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_upperBound_1978_);
                        v___x_1987_ = v_reuseFailAlloc_1990_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1988_ = lean_array_push(v_acc_1975_, v_val_1982_);
                v___x_1989_ = crate::leanh::lean_apply_3(
                    v_recur_1976_,
                    v___x_1987_,
                    v___x_1988_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toList___redArg(
    mut v_inst_1993_: *mut crate::leanh::LeanObject,
    mut v_inst_1994_: *mut crate::leanh::LeanObject,
    mut v_r_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___f_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1996_ = crate::leanh::lean_ctor_get(v_inst_1994_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_1996_);
                crate::leanh::lean_dec_ref(v_inst_1994_);
                v_lower_1997_ = crate::leanh::lean_ctor_get(v_r_1995_, 0);
                v_upper_1998_ = crate::leanh::lean_ctor_get(v_r_1995_, 1);
                v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v_r_1995_)) as u8;
                if v_isSharedCheck_2010_ == 0 {
                    v___x_2000_ = v_r_1995_;
                    v_isShared_2001_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_1998_);
                    crate::leanh::lean_inc(v_lower_1997_);
                    crate::leanh::lean_dec(v_r_1995_);
                    v___x_2000_ = crate::leanh::lean_box(0);
                    v_isShared_2001_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_1996_);
                v___f_2002_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2002_, 0, v_inst_1993_);
                crate::leanh::lean_closure_set(v___f_2002_, 1, v_succ_x3f_1996_);
                v___x_2003_ = crate::leanh::lean_apply_1(v_succ_x3f_1996_, v_lower_1997_);
                if v_isShared_2001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2000_, 0, v___x_2003_);
                    v___x_2005_ = v___x_2000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_upper_1998_);
                    v___x_2005_ = v_reuseFailAlloc_2009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2006_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_2007_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_2002_,
                        v___x_2005_,
                        v___x_2006_,
                    );
                v___x_2008_ = lean_array_to_list(v___x_2007_);
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toList(
    mut v_00_u03b1_2011_: *mut crate::leanh::LeanObject,
    mut v_inst_2012_: *mut crate::leanh::LeanObject,
    mut v_inst_2013_: *mut crate::leanh::LeanObject,
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_inst_2015_: *mut crate::leanh::LeanObject,
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_r_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___f_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2018_ = crate::leanh::lean_ctor_get(v_inst_2014_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_2018_);
                crate::leanh::lean_dec_ref(v_inst_2014_);
                v_lower_2019_ = crate::leanh::lean_ctor_get(v_r_2017_, 0);
                v_upper_2020_ = crate::leanh::lean_ctor_get(v_r_2017_, 1);
                v_isSharedCheck_2032_ = (!crate::leanh::lean_is_exclusive(v_r_2017_)) as u8;
                if v_isSharedCheck_2032_ == 0 {
                    v___x_2022_ = v_r_2017_;
                    v_isShared_2023_ = v_isSharedCheck_2032_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2020_);
                    crate::leanh::lean_inc(v_lower_2019_);
                    crate::leanh::lean_dec(v_r_2017_);
                    v___x_2022_ = crate::leanh::lean_box(0);
                    v_isShared_2023_ = v_isSharedCheck_2032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_2018_);
                v___f_2024_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2024_, 0, v_inst_2013_);
                crate::leanh::lean_closure_set(v___f_2024_, 1, v_succ_x3f_2018_);
                v___x_2025_ = crate::leanh::lean_apply_1(v_succ_x3f_2018_, v_lower_2019_);
                if v_isShared_2023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2025_);
                    v___x_2027_ = v___x_2022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_upper_2020_);
                    v___x_2027_ = v_reuseFailAlloc_2031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2028_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_2029_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_2024_,
                        v___x_2027_,
                        v___x_2028_,
                    );
                v___x_2030_ = lean_array_to_list(v___x_2029_);
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toArray___redArg(
    mut v_inst_2033_: *mut crate::leanh::LeanObject,
    mut v_inst_2034_: *mut crate::leanh::LeanObject,
    mut v_r_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___f_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2036_ = crate::leanh::lean_ctor_get(v_inst_2034_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_2036_);
                crate::leanh::lean_dec_ref(v_inst_2034_);
                v_lower_2037_ = crate::leanh::lean_ctor_get(v_r_2035_, 0);
                v_upper_2038_ = crate::leanh::lean_ctor_get(v_r_2035_, 1);
                v_isSharedCheck_2049_ = (!crate::leanh::lean_is_exclusive(v_r_2035_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v___x_2040_ = v_r_2035_;
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2038_);
                    crate::leanh::lean_inc(v_lower_2037_);
                    crate::leanh::lean_dec(v_r_2035_);
                    v___x_2040_ = crate::leanh::lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_2036_);
                v___f_2042_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2042_, 0, v_inst_2033_);
                crate::leanh::lean_closure_set(v___f_2042_, 1, v_succ_x3f_2036_);
                v___x_2043_ = crate::leanh::lean_apply_1(v_succ_x3f_2036_, v_lower_2037_);
                if v_isShared_2041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2040_, 0, v___x_2043_);
                    v___x_2045_ = v___x_2040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_upper_2038_);
                    v___x_2045_ = v_reuseFailAlloc_2048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2046_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_2047_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_2042_,
                        v___x_2045_,
                        v___x_2046_,
                    );
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toArray(
    mut v_00_u03b1_2050_: *mut crate::leanh::LeanObject,
    mut v_inst_2051_: *mut crate::leanh::LeanObject,
    mut v_inst_2052_: *mut crate::leanh::LeanObject,
    mut v_inst_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_inst_2055_: *mut crate::leanh::LeanObject,
    mut v_r_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___f_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2057_ = crate::leanh::lean_ctor_get(v_inst_2053_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_2057_);
                crate::leanh::lean_dec_ref(v_inst_2053_);
                v_lower_2058_ = crate::leanh::lean_ctor_get(v_r_2056_, 0);
                v_upper_2059_ = crate::leanh::lean_ctor_get(v_r_2056_, 1);
                v_isSharedCheck_2070_ = (!crate::leanh::lean_is_exclusive(v_r_2056_)) as u8;
                if v_isSharedCheck_2070_ == 0 {
                    v___x_2061_ = v_r_2056_;
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2059_);
                    crate::leanh::lean_inc(v_lower_2058_);
                    crate::leanh::lean_dec(v_r_2056_);
                    v___x_2061_ = crate::leanh::lean_box(0);
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_succ_x3f_2057_);
                v___f_2063_ = crate::leanh::lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2063_, 0, v_inst_2052_);
                crate::leanh::lean_closure_set(v___f_2063_, 1, v_succ_x3f_2057_);
                v___x_2064_ = crate::leanh::lean_apply_1(v_succ_x3f_2057_, v_lower_2058_);
                if v_isShared_2062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2061_, 0, v___x_2064_);
                    v___x_2066_ = v___x_2061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_upper_2059_);
                    v___x_2066_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2067_ = l_Std_Rcc_toList___redArg___closed__0;
                v___x_2068_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_2063_,
                        v___x_2066_,
                        v___x_2067_,
                    );
                return v___x_2068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_size___redArg(
    mut v_inst_2071_: *mut crate::leanh::LeanObject,
    mut v_inst_2072_: *mut crate::leanh::LeanObject,
    mut v_r_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2074_ = crate::leanh::lean_ctor_get(v_inst_2072_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2074_);
    crate::leanh::lean_dec_ref(v_inst_2072_);
    v_lower_2075_ = crate::leanh::lean_ctor_get(v_r_2073_, 0);
    crate::leanh::lean_inc(v_lower_2075_);
    v_upper_2076_ = crate::leanh::lean_ctor_get(v_r_2073_, 1);
    crate::leanh::lean_inc(v_upper_2076_);
    crate::leanh::lean_dec_ref(v_r_2073_);
    v___x_2077_ = crate::leanh::lean_apply_1(v_succ_x3f_2074_, v_lower_2075_);
    if crate::leanh::lean_obj_tag(v___x_2077_) == 0 {
        let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_upper_2076_);
        crate::leanh::lean_dec_ref(v_inst_2071_);
        v___x_2078_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2078_;
    } else {
        let mut v_val_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2079_ = crate::leanh::lean_ctor_get(v___x_2077_, 0);
        crate::leanh::lean_inc(v_val_2079_);
        crate::leanh::lean_dec_ref_known(v___x_2077_, 1);
        v___x_2080_ = crate::leanh::lean_apply_2(v_inst_2071_, v_val_2079_, v_upper_2076_);
        return v___x_2080_;
    }
}
pub unsafe fn l_Std_Roo_size(
    mut v_00_u03b1_2081_: *mut crate::leanh::LeanObject,
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_inst_2083_: *mut crate::leanh::LeanObject,
    mut v_r_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2085_ = crate::leanh::lean_ctor_get(v_inst_2083_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2085_);
    crate::leanh::lean_dec_ref(v_inst_2083_);
    v_lower_2086_ = crate::leanh::lean_ctor_get(v_r_2084_, 0);
    crate::leanh::lean_inc(v_lower_2086_);
    v_upper_2087_ = crate::leanh::lean_ctor_get(v_r_2084_, 1);
    crate::leanh::lean_inc(v_upper_2087_);
    crate::leanh::lean_dec_ref(v_r_2084_);
    v___x_2088_ = crate::leanh::lean_apply_1(v_succ_x3f_2085_, v_lower_2086_);
    if crate::leanh::lean_obj_tag(v___x_2088_) == 0 {
        let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_upper_2087_);
        crate::leanh::lean_dec_ref(v_inst_2082_);
        v___x_2089_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2089_;
    } else {
        let mut v_val_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2090_ = crate::leanh::lean_ctor_get(v___x_2088_, 0);
        crate::leanh::lean_inc(v_val_2090_);
        crate::leanh::lean_dec_ref_known(v___x_2088_, 1);
        v___x_2091_ = crate::leanh::lean_apply_2(v_inst_2082_, v_val_2090_, v_upper_2087_);
        return v___x_2091_;
    }
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_2092_: *mut crate::leanh::LeanObject,
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut crate::leanh::LeanObject,
    mut v_r_2096_: *mut crate::leanh::LeanObject,
    mut v_init_2097_: *mut crate::leanh::LeanObject,
    mut v_f_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2099_ = crate::leanh::lean_ctor_get(v_inst_2093_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2099_);
    v_succ_x3f_2100_ = crate::leanh::lean_ctor_get(v_inst_2092_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2100_, 2);
    crate::leanh::lean_dec_ref(v_inst_2092_);
    v_lower_2101_ = crate::leanh::lean_ctor_get(v_r_2096_, 0);
    crate::leanh::lean_inc(v_lower_2101_);
    v_upper_2102_ = crate::leanh::lean_ctor_get(v_r_2096_, 1);
    crate::leanh::lean_inc(v_upper_2102_);
    crate::leanh::lean_dec_ref(v_r_2096_);
    v_toBind_2103_ = crate::leanh::lean_ctor_get(v_inst_2093_, 1);
    crate::leanh::lean_inc(v_toBind_2103_);
    crate::leanh::lean_dec_ref(v_inst_2093_);
    v_toPure_2104_ = crate::leanh::lean_ctor_get(v_toApplicative_2099_, 1);
    crate::leanh::lean_inc(v_toPure_2104_);
    crate::leanh::lean_dec_ref(v_toApplicative_2099_);
    v___x_2105_ = crate::leanh::lean_apply_1(v_succ_x3f_2100_, v_lower_2101_);
    if crate::leanh::lean_obj_tag(v___x_2105_) == 0 {
        let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_2103_);
        crate::leanh::lean_dec(v_upper_2102_);
        crate::leanh::lean_dec_ref(v_succ_x3f_2100_);
        crate::leanh::lean_dec(v_f_2098_);
        crate::leanh::lean_dec_ref(v_inst_2094_);
        v___x_2106_ =
            crate::leanh::lean_apply_2(v_toPure_2104_, crate::leanh::lean_box(0), v_init_2097_);
        return v___x_2106_;
    } else {
        let mut v_val_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2107_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
        crate::leanh::lean_inc(v_val_2107_);
        crate::leanh::lean_dec_ref_known(v___x_2105_, 1);
        crate::leanh::lean_inc(v_toPure_2104_);
        v___f_2108_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_2108_, 0, v_toPure_2104_);
        v___f_2109_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 11, 7);
        crate::leanh::lean_closure_set(v___f_2109_, 0, v_inst_2094_);
        crate::leanh::lean_closure_set(v___f_2109_, 1, v_upper_2102_);
        crate::leanh::lean_closure_set(v___f_2109_, 2, v_toPure_2104_);
        crate::leanh::lean_closure_set(v___f_2109_, 3, v_succ_x3f_2100_);
        crate::leanh::lean_closure_set(v___f_2109_, 4, v_f_2098_);
        crate::leanh::lean_closure_set(v___f_2109_, 5, v_toBind_2103_);
        crate::leanh::lean_closure_set(v___f_2109_, 6, v___f_2108_);
        v___x_2110_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2109_,
            v_val_2107_,
            v_init_2097_,
            crate::leanh::lean_box(0),
        );
        return v___x_2110_;
    }
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2111_: *mut crate::leanh::LeanObject,
    mut v_inst_2112_: *mut crate::leanh::LeanObject,
    mut v_inst_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2114_ = crate::leanh::lean_alloc_closure(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_2114_, 0, v_inst_2111_);
    crate::leanh::lean_closure_set(v___f_2114_, 1, v_inst_2113_);
    crate::leanh::lean_closure_set(v___f_2114_, 2, v_inst_2112_);
    return v___f_2114_;
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2115_: *mut crate::leanh::LeanObject,
    mut v_m_2116_: *mut crate::leanh::LeanObject,
    mut v_inst_2117_: *mut crate::leanh::LeanObject,
    mut v_inst_2118_: *mut crate::leanh::LeanObject,
    mut v_inst_2119_: *mut crate::leanh::LeanObject,
    mut v_inst_2120_: *mut crate::leanh::LeanObject,
    mut v_inst_2121_: *mut crate::leanh::LeanObject,
    mut v_inst_2122_: *mut crate::leanh::LeanObject,
    mut v_inst_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2124_ = crate::leanh::lean_alloc_closure(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_2124_, 0, v_inst_2117_);
    crate::leanh::lean_closure_set(v___f_2124_, 1, v_inst_2122_);
    crate::leanh::lean_closure_set(v___f_2124_, 2, v_inst_2119_);
    return v___f_2124_;
}
pub unsafe fn l_Std_Roi_Internal_iter___redArg(
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v_r_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2127_ = crate::leanh::lean_ctor_get(v_inst_2125_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2127_);
    crate::leanh::lean_dec_ref(v_inst_2125_);
    v___x_2128_ = crate::leanh::lean_apply_1(v_succ_x3f_2127_, v_r_2126_);
    return v___x_2128_;
}
pub unsafe fn l_Std_Roi_Internal_iter(
    mut v_00_u03b1_2129_: *mut crate::leanh::LeanObject,
    mut v_inst_2130_: *mut crate::leanh::LeanObject,
    mut v_r_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2132_ = crate::leanh::lean_ctor_get(v_inst_2130_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2132_);
    crate::leanh::lean_dec_ref(v_inst_2130_);
    v___x_2133_ = crate::leanh::lean_apply_1(v_succ_x3f_2132_, v_r_2131_);
    return v___x_2133_;
}
pub unsafe fn l_Std_Roi_toList___redArg___lam__0(
    mut v_succ_x3f_2134_: *mut crate::leanh::LeanObject,
    mut v_it_2135_: *mut crate::leanh::LeanObject,
    mut v_acc_2136_: *mut crate::leanh::LeanObject,
    mut v_recur_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_2135_) == 0 {
        crate::leanh::lean_dec_ref(v_recur_2137_);
        crate::leanh::lean_dec_ref(v_succ_x3f_2134_);
        return v_acc_2136_;
    } else {
        let mut v_val_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2138_ = crate::leanh::lean_ctor_get(v_it_2135_, 0);
        crate::leanh::lean_inc_n(v_val_2138_, 2);
        crate::leanh::lean_dec_ref_known(v_it_2135_, 1);
        v___x_2139_ = crate::leanh::lean_apply_1(v_succ_x3f_2134_, v_val_2138_);
        v___x_2140_ = lean_array_push(v_acc_2136_, v_val_2138_);
        v___x_2141_ = crate::leanh::lean_apply_3(
            v_recur_2137_,
            v___x_2139_,
            v___x_2140_,
            crate::leanh::lean_box(0),
        );
        return v___x_2141_;
    }
}
pub unsafe fn l_Std_Roi_toList___redArg(
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_r_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2144_ = crate::leanh::lean_ctor_get(v_inst_2142_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2144_, 2);
    crate::leanh::lean_dec_ref(v_inst_2142_);
    v___f_2145_ = crate::leanh::lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2145_, 0, v_succ_x3f_2144_);
    v___x_2146_ = crate::leanh::lean_apply_1(v_succ_x3f_2144_, v_r_2143_);
    v___x_2147_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2148_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2145_,
        v___x_2146_,
        v___x_2147_,
    );
    v___x_2149_ = lean_array_to_list(v___x_2148_);
    return v___x_2149_;
}
pub unsafe fn l_Std_Roi_toList(
    mut v_00_u03b1_2150_: *mut crate::leanh::LeanObject,
    mut v_inst_2151_: *mut crate::leanh::LeanObject,
    mut v_inst_2152_: *mut crate::leanh::LeanObject,
    mut v_inst_2153_: *mut crate::leanh::LeanObject,
    mut v_r_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2155_ = crate::leanh::lean_ctor_get(v_inst_2151_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2155_, 2);
    crate::leanh::lean_dec_ref(v_inst_2151_);
    v___f_2156_ = crate::leanh::lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2156_, 0, v_succ_x3f_2155_);
    v___x_2157_ = crate::leanh::lean_apply_1(v_succ_x3f_2155_, v_r_2154_);
    v___x_2158_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2156_,
        v___x_2157_,
        v___x_2158_,
    );
    v___x_2160_ = lean_array_to_list(v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Std_Roi_toArray___redArg(
    mut v_inst_2161_: *mut crate::leanh::LeanObject,
    mut v_r_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2163_ = crate::leanh::lean_ctor_get(v_inst_2161_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2163_, 2);
    crate::leanh::lean_dec_ref(v_inst_2161_);
    v___f_2164_ = crate::leanh::lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2164_, 0, v_succ_x3f_2163_);
    v___x_2165_ = crate::leanh::lean_apply_1(v_succ_x3f_2163_, v_r_2162_);
    v___x_2166_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2167_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2164_,
        v___x_2165_,
        v___x_2166_,
    );
    return v___x_2167_;
}
pub unsafe fn l_Std_Roi_toArray(
    mut v_00_u03b1_2168_: *mut crate::leanh::LeanObject,
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
    mut v_inst_2170_: *mut crate::leanh::LeanObject,
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_r_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2173_ = crate::leanh::lean_ctor_get(v_inst_2169_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2173_, 2);
    crate::leanh::lean_dec_ref(v_inst_2169_);
    v___f_2174_ = crate::leanh::lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2174_, 0, v_succ_x3f_2173_);
    v___x_2175_ = crate::leanh::lean_apply_1(v_succ_x3f_2173_, v_r_2172_);
    v___x_2176_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2177_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2174_,
        v___x_2175_,
        v___x_2176_,
    );
    return v___x_2177_;
}
pub unsafe fn l_Std_Roi_size___redArg(
    mut v_inst_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_r_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2181_ = crate::leanh::lean_ctor_get(v_inst_2179_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2181_);
    crate::leanh::lean_dec_ref(v_inst_2179_);
    v___x_2182_ = crate::leanh::lean_apply_1(v_succ_x3f_2181_, v_r_2180_);
    if crate::leanh::lean_obj_tag(v___x_2182_) == 0 {
        let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2178_);
        v___x_2183_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2183_;
    } else {
        let mut v_val_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2184_ = crate::leanh::lean_ctor_get(v___x_2182_, 0);
        crate::leanh::lean_inc(v_val_2184_);
        crate::leanh::lean_dec_ref_known(v___x_2182_, 1);
        v___x_2185_ = crate::leanh::lean_apply_1(v_inst_2178_, v_val_2184_);
        return v___x_2185_;
    }
}
pub unsafe fn l_Std_Roi_size(
    mut v_00_u03b1_2186_: *mut crate::leanh::LeanObject,
    mut v_inst_2187_: *mut crate::leanh::LeanObject,
    mut v_inst_2188_: *mut crate::leanh::LeanObject,
    mut v_r_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_2190_ = crate::leanh::lean_ctor_get(v_inst_2188_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_2190_);
    crate::leanh::lean_dec_ref(v_inst_2188_);
    v___x_2191_ = crate::leanh::lean_apply_1(v_succ_x3f_2190_, v_r_2189_);
    if crate::leanh::lean_obj_tag(v___x_2191_) == 0 {
        let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2187_);
        v___x_2192_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2192_;
    } else {
        let mut v_val_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2193_ = crate::leanh::lean_ctor_get(v___x_2191_, 0);
        crate::leanh::lean_inc(v_val_2193_);
        crate::leanh::lean_dec_ref_known(v___x_2191_, 1);
        v___x_2194_ = crate::leanh::lean_apply_1(v_inst_2187_, v_val_2193_);
        return v___x_2194_;
    }
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_toPure_2195_: *mut crate::leanh::LeanObject,
    mut v_succ_x3f_2196_: *mut crate::leanh::LeanObject,
    mut v_f_2197_: *mut crate::leanh::LeanObject,
    mut v_toBind_2198_: *mut crate::leanh::LeanObject,
    mut v___f_2199_: *mut crate::leanh::LeanObject,
    mut v_next_2200_: *mut crate::leanh::LeanObject,
    mut v_acc_2201_: *mut crate::leanh::LeanObject,
    mut v_h_2202_: *mut crate::leanh::LeanObject,
    mut v_G_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_next_2200_);
    v___f_2204_ = crate::leanh::lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_2204_, 0, v_toPure_2195_);
    crate::leanh::lean_closure_set(v___f_2204_, 1, v_succ_x3f_2196_);
    crate::leanh::lean_closure_set(v___f_2204_, 2, v_next_2200_);
    crate::leanh::lean_closure_set(v___f_2204_, 3, v_G_2203_);
    v___x_2205_ = crate::leanh::lean_apply_3(
        v_f_2197_,
        v_next_2200_,
        crate::leanh::lean_box(0),
        v_acc_2201_,
    );
    crate::leanh::lean_inc(v_toBind_2198_);
    v___x_2206_ = crate::leanh::lean_apply_4(
        v_toBind_2198_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2205_,
        v___f_2199_,
    );
    v___x_2207_ = crate::leanh::lean_apply_4(
        v_toBind_2198_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2206_,
        v___f_2204_,
    );
    return v___x_2207_;
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_inst_2209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2210_: *mut crate::leanh::LeanObject,
    mut v_r_2211_: *mut crate::leanh::LeanObject,
    mut v_init_2212_: *mut crate::leanh::LeanObject,
    mut v_f_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2214_ = crate::leanh::lean_ctor_get(v_inst_2209_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2214_);
    v_succ_x3f_2215_ = crate::leanh::lean_ctor_get(v_inst_2208_, 0);
    crate::leanh::lean_inc_ref_n(v_succ_x3f_2215_, 2);
    crate::leanh::lean_dec_ref(v_inst_2208_);
    v_toBind_2216_ = crate::leanh::lean_ctor_get(v_inst_2209_, 1);
    crate::leanh::lean_inc(v_toBind_2216_);
    crate::leanh::lean_dec_ref(v_inst_2209_);
    v_toPure_2217_ = crate::leanh::lean_ctor_get(v_toApplicative_2214_, 1);
    crate::leanh::lean_inc(v_toPure_2217_);
    crate::leanh::lean_dec_ref(v_toApplicative_2214_);
    v_next_2218_ = crate::leanh::lean_apply_1(v_succ_x3f_2215_, v_r_2211_);
    if crate::leanh::lean_obj_tag(v_next_2218_) == 0 {
        let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_2216_);
        crate::leanh::lean_dec_ref(v_succ_x3f_2215_);
        crate::leanh::lean_dec(v_f_2213_);
        v___x_2219_ =
            crate::leanh::lean_apply_2(v_toPure_2217_, crate::leanh::lean_box(0), v_init_2212_);
        return v___x_2219_;
    } else {
        let mut v_val_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2220_ = crate::leanh::lean_ctor_get(v_next_2218_, 0);
        crate::leanh::lean_inc(v_val_2220_);
        crate::leanh::lean_dec_ref_known(v_next_2218_, 1);
        crate::leanh::lean_inc(v_toPure_2217_);
        v___f_2221_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_2221_, 0, v_toPure_2217_);
        v___f_2222_ = crate::leanh::lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
        crate::leanh::lean_closure_set(v___f_2222_, 0, v_toPure_2217_);
        crate::leanh::lean_closure_set(v___f_2222_, 1, v_succ_x3f_2215_);
        crate::leanh::lean_closure_set(v___f_2222_, 2, v_f_2213_);
        crate::leanh::lean_closure_set(v___f_2222_, 3, v_toBind_2216_);
        crate::leanh::lean_closure_set(v___f_2222_, 4, v___f_2221_);
        v___x_2223_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2222_,
            v_val_2220_,
            v_init_2212_,
            crate::leanh::lean_box(0),
        );
        return v___x_2223_;
    }
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2224_: *mut crate::leanh::LeanObject,
    mut v_inst_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2226_ = crate::leanh::lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_2226_, 0, v_inst_2224_);
    crate::leanh::lean_closure_set(v___f_2226_, 1, v_inst_2225_);
    return v___f_2226_;
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2227_: *mut crate::leanh::LeanObject,
    mut v_m_2228_: *mut crate::leanh::LeanObject,
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_inst_2230_: *mut crate::leanh::LeanObject,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
    mut v_inst_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2235_ = crate::leanh::lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_2235_, 0, v_inst_2229_);
    crate::leanh::lean_closure_set(v___f_2235_, 1, v_inst_2233_);
    return v___f_2235_;
}
pub unsafe fn l_Std_Ric_Internal_iter___redArg(
    mut v_inst_2236_: *mut crate::leanh::LeanObject,
    mut v_r_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2238_, 0, v_inst_2236_);
    crate::leanh::lean_ctor_set(v___x_2238_, 1, v_r_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Std_Ric_Internal_iter(
    mut v_00_u03b1_2239_: *mut crate::leanh::LeanObject,
    mut v_inst_2240_: *mut crate::leanh::LeanObject,
    mut v_r_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2242_, 0, v_inst_2240_);
    crate::leanh::lean_ctor_set(v___x_2242_, 1, v_r_2241_);
    return v___x_2242_;
}
pub unsafe fn l_Std_Ric_toList___redArg(
    mut v_inst_2243_: *mut crate::leanh::LeanObject,
    mut v_inst_2244_: *mut crate::leanh::LeanObject,
    mut v_inst_2245_: *mut crate::leanh::LeanObject,
    mut v_r_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2247_ = crate::leanh::lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2247_, 0, v_inst_2244_);
    crate::leanh::lean_closure_set(v___f_2247_, 1, v_inst_2245_);
    v___x_2248_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2248_, 0, v_inst_2243_);
    crate::leanh::lean_ctor_set(v___x_2248_, 1, v_r_2246_);
    v___x_2249_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2250_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2247_,
        v___x_2248_,
        v___x_2249_,
    );
    v___x_2251_ = lean_array_to_list(v___x_2250_);
    return v___x_2251_;
}
pub unsafe fn l_Std_Ric_toList(
    mut v_00_u03b1_2252_: *mut crate::leanh::LeanObject,
    mut v_inst_2253_: *mut crate::leanh::LeanObject,
    mut v_inst_2254_: *mut crate::leanh::LeanObject,
    mut v_inst_2255_: *mut crate::leanh::LeanObject,
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
    mut v_inst_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_r_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2260_ = crate::leanh::lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2260_, 0, v_inst_2255_);
    crate::leanh::lean_closure_set(v___f_2260_, 1, v_inst_2256_);
    v___x_2261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2261_, 0, v_inst_2253_);
    crate::leanh::lean_ctor_set(v___x_2261_, 1, v_r_2259_);
    v___x_2262_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2263_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2260_,
        v___x_2261_,
        v___x_2262_,
    );
    v___x_2264_ = lean_array_to_list(v___x_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Std_Ric_toArray___redArg(
    mut v_inst_2265_: *mut crate::leanh::LeanObject,
    mut v_inst_2266_: *mut crate::leanh::LeanObject,
    mut v_inst_2267_: *mut crate::leanh::LeanObject,
    mut v_r_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2269_ = crate::leanh::lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2269_, 0, v_inst_2266_);
    crate::leanh::lean_closure_set(v___f_2269_, 1, v_inst_2267_);
    v___x_2270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2270_, 0, v_inst_2265_);
    crate::leanh::lean_ctor_set(v___x_2270_, 1, v_r_2268_);
    v___x_2271_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2269_,
        v___x_2270_,
        v___x_2271_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Std_Ric_toArray(
    mut v_00_u03b1_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_inst_2275_: *mut crate::leanh::LeanObject,
    mut v_inst_2276_: *mut crate::leanh::LeanObject,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
    mut v_inst_2279_: *mut crate::leanh::LeanObject,
    mut v_r_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2281_ = crate::leanh::lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2281_, 0, v_inst_2276_);
    crate::leanh::lean_closure_set(v___f_2281_, 1, v_inst_2277_);
    v___x_2282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2282_, 0, v_inst_2274_);
    crate::leanh::lean_ctor_set(v___x_2282_, 1, v_r_2280_);
    v___x_2283_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2281_,
        v___x_2282_,
        v___x_2283_,
    );
    return v___x_2284_;
}
pub unsafe fn l_Std_Ric_size___redArg(
    mut v_inst_2285_: *mut crate::leanh::LeanObject,
    mut v_inst_2286_: *mut crate::leanh::LeanObject,
    mut v_r_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2286_) == 0 {
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_r_2287_);
        crate::leanh::lean_dec_ref(v_inst_2285_);
        v___x_2288_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2288_;
    } else {
        let mut v_val_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2289_ = crate::leanh::lean_ctor_get(v_inst_2286_, 0);
        crate::leanh::lean_inc(v_val_2289_);
        crate::leanh::lean_dec_ref_known(v_inst_2286_, 1);
        v___x_2290_ = crate::leanh::lean_apply_2(v_inst_2285_, v_val_2289_, v_r_2287_);
        return v___x_2290_;
    }
}
pub unsafe fn l_Std_Ric_size(
    mut v_00_u03b1_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_inst_2293_: *mut crate::leanh::LeanObject,
    mut v_r_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2293_) == 0 {
        let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_r_2294_);
        crate::leanh::lean_dec_ref(v_inst_2292_);
        v___x_2295_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2295_;
    } else {
        let mut v_val_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2296_ = crate::leanh::lean_ctor_get(v_inst_2293_, 0);
        crate::leanh::lean_inc(v_val_2296_);
        crate::leanh::lean_dec_ref_known(v_inst_2293_, 1);
        v___x_2297_ = crate::leanh::lean_apply_2(v_inst_2292_, v_val_2296_, v_r_2294_);
        return v___x_2297_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_2298_: *mut crate::leanh::LeanObject,
    mut v_r_2299_: *mut crate::leanh::LeanObject,
    mut v_toPure_2300_: *mut crate::leanh::LeanObject,
    mut v_inst_2301_: *mut crate::leanh::LeanObject,
    mut v_f_2302_: *mut crate::leanh::LeanObject,
    mut v_toBind_2303_: *mut crate::leanh::LeanObject,
    mut v___f_2304_: *mut crate::leanh::LeanObject,
    mut v_next_2305_: *mut crate::leanh::LeanObject,
    mut v_acc_2306_: *mut crate::leanh::LeanObject,
    mut v_h_2307_: *mut crate::leanh::LeanObject,
    mut v_G_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    crate::leanh::lean_inc(v_next_2305_);
    v___x_2309_ = crate::leanh::lean_apply_2(v_inst_2298_, v_next_2305_, v_r_2299_);
    v___x_2310_ = (crate::leanh::lean_unbox(v___x_2309_) as u8);
    if v___x_2310_ == 0 {
        let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_2308_);
        crate::leanh::lean_dec(v_next_2305_);
        crate::leanh::lean_dec(v___f_2304_);
        crate::leanh::lean_dec(v_toBind_2303_);
        crate::leanh::lean_dec(v_f_2302_);
        crate::leanh::lean_dec_ref(v_inst_2301_);
        v___x_2311_ =
            crate::leanh::lean_apply_2(v_toPure_2300_, crate::leanh::lean_box(0), v_acc_2306_);
        return v___x_2311_;
    } else {
        let mut v___f_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_next_2305_);
        v___f_2312_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_2312_, 0, v_toPure_2300_);
        crate::leanh::lean_closure_set(v___f_2312_, 1, v_inst_2301_);
        crate::leanh::lean_closure_set(v___f_2312_, 2, v_next_2305_);
        crate::leanh::lean_closure_set(v___f_2312_, 3, v_G_2308_);
        v___x_2313_ = crate::leanh::lean_apply_3(
            v_f_2302_,
            v_next_2305_,
            crate::leanh::lean_box(0),
            v_acc_2306_,
        );
        crate::leanh::lean_inc(v_toBind_2303_);
        v___x_2314_ = crate::leanh::lean_apply_4(
            v_toBind_2303_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2313_,
            v___f_2304_,
        );
        v___x_2315_ = crate::leanh::lean_apply_4(
            v_toBind_2303_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2314_,
            v___f_2312_,
        );
        return v___x_2315_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_2316_: *mut crate::leanh::LeanObject,
    mut v_inst_2317_: *mut crate::leanh::LeanObject,
    mut v_inst_2318_: *mut crate::leanh::LeanObject,
    mut v_inst_2319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2320_: *mut crate::leanh::LeanObject,
    mut v_r_2321_: *mut crate::leanh::LeanObject,
    mut v_init_2322_: *mut crate::leanh::LeanObject,
    mut v_f_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2324_ = crate::leanh::lean_ctor_get(v_inst_2316_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2324_);
    if crate::leanh::lean_obj_tag(v_inst_2317_) == 0 {
        let mut v_toPure_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_2323_);
        crate::leanh::lean_dec(v_r_2321_);
        crate::leanh::lean_dec_ref(v_inst_2319_);
        crate::leanh::lean_dec_ref(v_inst_2318_);
        crate::leanh::lean_dec_ref(v_inst_2316_);
        v_toPure_2325_ = crate::leanh::lean_ctor_get(v_toApplicative_2324_, 1);
        crate::leanh::lean_inc(v_toPure_2325_);
        crate::leanh::lean_dec_ref(v_toApplicative_2324_);
        v___x_2326_ =
            crate::leanh::lean_apply_2(v_toPure_2325_, crate::leanh::lean_box(0), v_init_2322_);
        return v___x_2326_;
    } else {
        let mut v_toBind_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2327_ = crate::leanh::lean_ctor_get(v_inst_2316_, 1);
        crate::leanh::lean_inc(v_toBind_2327_);
        crate::leanh::lean_dec_ref(v_inst_2316_);
        v_toPure_2328_ = crate::leanh::lean_ctor_get(v_toApplicative_2324_, 1);
        crate::leanh::lean_inc_n(v_toPure_2328_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_2324_);
        v_val_2329_ = crate::leanh::lean_ctor_get(v_inst_2317_, 0);
        crate::leanh::lean_inc(v_val_2329_);
        crate::leanh::lean_dec_ref_known(v_inst_2317_, 1);
        v___f_2330_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_2330_, 0, v_toPure_2328_);
        v___f_2331_ = crate::leanh::lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
        crate::leanh::lean_closure_set(v___f_2331_, 0, v_inst_2318_);
        crate::leanh::lean_closure_set(v___f_2331_, 1, v_r_2321_);
        crate::leanh::lean_closure_set(v___f_2331_, 2, v_toPure_2328_);
        crate::leanh::lean_closure_set(v___f_2331_, 3, v_inst_2319_);
        crate::leanh::lean_closure_set(v___f_2331_, 4, v_f_2323_);
        crate::leanh::lean_closure_set(v___f_2331_, 5, v_toBind_2327_);
        crate::leanh::lean_closure_set(v___f_2331_, 6, v___f_2330_);
        v___x_2332_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2331_,
            v_val_2329_,
            v_init_2322_,
            crate::leanh::lean_box(0),
        );
        return v___x_2332_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2333_: *mut crate::leanh::LeanObject,
    mut v_inst_2334_: *mut crate::leanh::LeanObject,
    mut v_inst_2335_: *mut crate::leanh::LeanObject,
    mut v_inst_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2337_ = crate::leanh::lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_2337_, 0, v_inst_2336_);
    crate::leanh::lean_closure_set(v___f_2337_, 1, v_inst_2335_);
    crate::leanh::lean_closure_set(v___f_2337_, 2, v_inst_2334_);
    crate::leanh::lean_closure_set(v___f_2337_, 3, v_inst_2333_);
    return v___f_2337_;
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2338_: *mut crate::leanh::LeanObject,
    mut v_m_2339_: *mut crate::leanh::LeanObject,
    mut v_inst_2340_: *mut crate::leanh::LeanObject,
    mut v_inst_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
    mut v_inst_2343_: *mut crate::leanh::LeanObject,
    mut v_inst_2344_: *mut crate::leanh::LeanObject,
    mut v_inst_2345_: *mut crate::leanh::LeanObject,
    mut v_inst_2346_: *mut crate::leanh::LeanObject,
    mut v_inst_2347_: *mut crate::leanh::LeanObject,
    mut v_inst_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2349_ = crate::leanh::lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_2349_, 0, v_inst_2347_);
    crate::leanh::lean_closure_set(v___f_2349_, 1, v_inst_2343_);
    crate::leanh::lean_closure_set(v___f_2349_, 2, v_inst_2342_);
    crate::leanh::lean_closure_set(v___f_2349_, 3, v_inst_2340_);
    return v___f_2349_;
}
pub unsafe fn l_Std_Rio_Internal_iter___redArg(
    mut v_inst_2350_: *mut crate::leanh::LeanObject,
    mut v_r_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2352_, 0, v_inst_2350_);
    crate::leanh::lean_ctor_set(v___x_2352_, 1, v_r_2351_);
    return v___x_2352_;
}
pub unsafe fn l_Std_Rio_Internal_iter(
    mut v_00_u03b1_2353_: *mut crate::leanh::LeanObject,
    mut v_inst_2354_: *mut crate::leanh::LeanObject,
    mut v_inst_2355_: *mut crate::leanh::LeanObject,
    mut v_r_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2357_, 0, v_inst_2355_);
    crate::leanh::lean_ctor_set(v___x_2357_, 1, v_r_2356_);
    return v___x_2357_;
}
pub unsafe fn l_Std_Rio_Internal_iter___boxed(
    mut v_00_u03b1_2358_: *mut crate::leanh::LeanObject,
    mut v_inst_2359_: *mut crate::leanh::LeanObject,
    mut v_inst_2360_: *mut crate::leanh::LeanObject,
    mut v_r_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Std_Rio_Internal_iter(v_00_u03b1_2358_, v_inst_2359_, v_inst_2360_, v_r_2361_);
    crate::leanh::lean_dec_ref(v_inst_2359_);
    return v_res_2362_;
}
pub unsafe fn l_Std_Rio_toList___redArg(
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v_inst_2364_: *mut crate::leanh::LeanObject,
    mut v_inst_2365_: *mut crate::leanh::LeanObject,
    mut v_r_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2367_ = crate::leanh::lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2367_, 0, v_inst_2364_);
    crate::leanh::lean_closure_set(v___f_2367_, 1, v_inst_2365_);
    v___x_2368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2368_, 0, v_inst_2363_);
    crate::leanh::lean_ctor_set(v___x_2368_, 1, v_r_2366_);
    v___x_2369_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2370_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2367_,
        v___x_2368_,
        v___x_2369_,
    );
    v___x_2371_ = lean_array_to_list(v___x_2370_);
    return v___x_2371_;
}
pub unsafe fn l_Std_Rio_toList(
    mut v_00_u03b1_2372_: *mut crate::leanh::LeanObject,
    mut v_inst_2373_: *mut crate::leanh::LeanObject,
    mut v_inst_2374_: *mut crate::leanh::LeanObject,
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
    mut v_inst_2376_: *mut crate::leanh::LeanObject,
    mut v_inst_2377_: *mut crate::leanh::LeanObject,
    mut v_inst_2378_: *mut crate::leanh::LeanObject,
    mut v_r_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2380_ = crate::leanh::lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2380_, 0, v_inst_2375_);
    crate::leanh::lean_closure_set(v___f_2380_, 1, v_inst_2376_);
    v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2381_, 0, v_inst_2373_);
    crate::leanh::lean_ctor_set(v___x_2381_, 1, v_r_2379_);
    v___x_2382_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2383_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2380_,
        v___x_2381_,
        v___x_2382_,
    );
    v___x_2384_ = lean_array_to_list(v___x_2383_);
    return v___x_2384_;
}
pub unsafe fn l_Std_Rio_toArray___redArg(
    mut v_inst_2385_: *mut crate::leanh::LeanObject,
    mut v_inst_2386_: *mut crate::leanh::LeanObject,
    mut v_inst_2387_: *mut crate::leanh::LeanObject,
    mut v_r_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2389_ = crate::leanh::lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2389_, 0, v_inst_2386_);
    crate::leanh::lean_closure_set(v___f_2389_, 1, v_inst_2387_);
    v___x_2390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2390_, 0, v_inst_2385_);
    crate::leanh::lean_ctor_set(v___x_2390_, 1, v_r_2388_);
    v___x_2391_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2392_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2389_,
        v___x_2390_,
        v___x_2391_,
    );
    return v___x_2392_;
}
pub unsafe fn l_Std_Rio_toArray(
    mut v_00_u03b1_2393_: *mut crate::leanh::LeanObject,
    mut v_inst_2394_: *mut crate::leanh::LeanObject,
    mut v_inst_2395_: *mut crate::leanh::LeanObject,
    mut v_inst_2396_: *mut crate::leanh::LeanObject,
    mut v_inst_2397_: *mut crate::leanh::LeanObject,
    mut v_inst_2398_: *mut crate::leanh::LeanObject,
    mut v_inst_2399_: *mut crate::leanh::LeanObject,
    mut v_r_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2401_ = crate::leanh::lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2401_, 0, v_inst_2396_);
    crate::leanh::lean_closure_set(v___f_2401_, 1, v_inst_2397_);
    v___x_2402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2402_, 0, v_inst_2394_);
    crate::leanh::lean_ctor_set(v___x_2402_, 1, v_r_2400_);
    v___x_2403_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2401_,
        v___x_2402_,
        v___x_2403_,
    );
    return v___x_2404_;
}
pub unsafe fn l_Std_Rio_size___redArg(
    mut v_inst_2405_: *mut crate::leanh::LeanObject,
    mut v_inst_2406_: *mut crate::leanh::LeanObject,
    mut v_r_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2406_) == 0 {
        let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_r_2407_);
        crate::leanh::lean_dec_ref(v_inst_2405_);
        v___x_2408_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2408_;
    } else {
        let mut v_val_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2409_ = crate::leanh::lean_ctor_get(v_inst_2406_, 0);
        crate::leanh::lean_inc(v_val_2409_);
        crate::leanh::lean_dec_ref_known(v_inst_2406_, 1);
        v___x_2410_ = crate::leanh::lean_apply_2(v_inst_2405_, v_val_2409_, v_r_2407_);
        return v___x_2410_;
    }
}
pub unsafe fn l_Std_Rio_size(
    mut v_00_u03b1_2411_: *mut crate::leanh::LeanObject,
    mut v_inst_2412_: *mut crate::leanh::LeanObject,
    mut v_inst_2413_: *mut crate::leanh::LeanObject,
    mut v_r_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2413_) == 0 {
        let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_r_2414_);
        crate::leanh::lean_dec_ref(v_inst_2412_);
        v___x_2415_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2415_;
    } else {
        let mut v_val_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2416_ = crate::leanh::lean_ctor_get(v_inst_2413_, 0);
        crate::leanh::lean_inc(v_val_2416_);
        crate::leanh::lean_dec_ref_known(v_inst_2413_, 1);
        v___x_2417_ = crate::leanh::lean_apply_2(v_inst_2412_, v_val_2416_, v_r_2414_);
        return v___x_2417_;
    }
}
pub unsafe fn l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
    mut v_inst_2420_: *mut crate::leanh::LeanObject,
    mut v_inst_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2422_ = crate::leanh::lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_2422_, 0, v_inst_2421_);
    crate::leanh::lean_closure_set(v___f_2422_, 1, v_inst_2420_);
    crate::leanh::lean_closure_set(v___f_2422_, 2, v_inst_2419_);
    crate::leanh::lean_closure_set(v___f_2422_, 3, v_inst_2418_);
    return v___f_2422_;
}
pub unsafe fn l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2423_: *mut crate::leanh::LeanObject,
    mut v_m_2424_: *mut crate::leanh::LeanObject,
    mut v_inst_2425_: *mut crate::leanh::LeanObject,
    mut v_inst_2426_: *mut crate::leanh::LeanObject,
    mut v_inst_2427_: *mut crate::leanh::LeanObject,
    mut v_inst_2428_: *mut crate::leanh::LeanObject,
    mut v_inst_2429_: *mut crate::leanh::LeanObject,
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
    mut v_inst_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2434_ = crate::leanh::lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_2434_, 0, v_inst_2432_);
    crate::leanh::lean_closure_set(v___f_2434_, 1, v_inst_2428_);
    crate::leanh::lean_closure_set(v___f_2434_, 2, v_inst_2427_);
    crate::leanh::lean_closure_set(v___f_2434_, 3, v_inst_2425_);
    return v___f_2434_;
}
pub unsafe fn l_Std_Rii_Internal_iter___redArg(
    mut v_inst_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_2435_);
    return v_inst_2435_;
}
pub unsafe fn l_Std_Rii_Internal_iter___redArg___boxed(
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Std_Rii_Internal_iter___redArg(v_inst_2436_);
    crate::leanh::lean_dec(v_inst_2436_);
    return v_res_2437_;
}
pub unsafe fn l_Std_Rii_Internal_iter(
    mut v_00_u03b1_2438_: *mut crate::leanh::LeanObject,
    mut v_inst_2439_: *mut crate::leanh::LeanObject,
    mut v_inst_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_2440_);
    return v_inst_2440_;
}
pub unsafe fn l_Std_Rii_Internal_iter___boxed(
    mut v_00_u03b1_2442_: *mut crate::leanh::LeanObject,
    mut v_inst_2443_: *mut crate::leanh::LeanObject,
    mut v_inst_2444_: *mut crate::leanh::LeanObject,
    mut v_x_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Rii_Internal_iter(v_00_u03b1_2442_, v_inst_2443_, v_inst_2444_, v_x_2445_);
    crate::leanh::lean_dec(v_inst_2444_);
    crate::leanh::lean_dec_ref(v_inst_2443_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Rii_toList___redArg___lam__0(
    mut v_inst_2447_: *mut crate::leanh::LeanObject,
    mut v_it_2448_: *mut crate::leanh::LeanObject,
    mut v_acc_2449_: *mut crate::leanh::LeanObject,
    mut v_recur_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_2451_ = crate::leanh::lean_apply_1(v_inst_2447_, v_it_2448_);
    match crate::leanh::lean_obj_tag(v_val_2451_) {
        0 => {
            let mut v_it_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_2452_ = crate::leanh::lean_ctor_get(v_val_2451_, 0);
            crate::leanh::lean_inc(v_it_2452_);
            v_out_2453_ = crate::leanh::lean_ctor_get(v_val_2451_, 1);
            crate::leanh::lean_inc(v_out_2453_);
            crate::leanh::lean_dec_ref_known(v_val_2451_, 2);
            v___x_2454_ = lean_array_push(v_acc_2449_, v_out_2453_);
            v___x_2455_ = crate::leanh::lean_apply_3(
                v_recur_2450_,
                v_it_2452_,
                v___x_2454_,
                crate::leanh::lean_box(0),
            );
            return v___x_2455_;
        }
        1 => {
            let mut v_it_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_2456_ = crate::leanh::lean_ctor_get(v_val_2451_, 0);
            crate::leanh::lean_inc(v_it_2456_);
            crate::leanh::lean_dec_ref_known(v_val_2451_, 1);
            v___x_2457_ = crate::leanh::lean_apply_3(
                v_recur_2450_,
                v_it_2456_,
                v_acc_2449_,
                crate::leanh::lean_box(0),
            );
            return v___x_2457_;
        }
        _ => {
            crate::leanh::lean_dec_ref(v_recur_2450_);
            return v_acc_2449_;
        }
    }
}
pub unsafe fn l_Std_Rii_toList___redArg(
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v_inst_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2460_ = crate::leanh::lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2460_, 0, v_inst_2459_);
    v___x_2461_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2462_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2460_,
        v_inst_2458_,
        v___x_2461_,
    );
    v___x_2463_ = lean_array_to_list(v___x_2462_);
    return v___x_2463_;
}
pub unsafe fn l_Std_Rii_toList(
    mut v_00_u03b1_2464_: *mut crate::leanh::LeanObject,
    mut v_inst_2465_: *mut crate::leanh::LeanObject,
    mut v_inst_2466_: *mut crate::leanh::LeanObject,
    mut v_r_2467_: *mut crate::leanh::LeanObject,
    mut v_inst_2468_: *mut crate::leanh::LeanObject,
    mut v_inst_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2470_ = crate::leanh::lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2470_, 0, v_inst_2468_);
    v___x_2471_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2470_,
        v_inst_2466_,
        v___x_2471_,
    );
    v___x_2473_ = lean_array_to_list(v___x_2472_);
    return v___x_2473_;
}
pub unsafe fn l_Std_Rii_toList___boxed(
    mut v_00_u03b1_2474_: *mut crate::leanh::LeanObject,
    mut v_inst_2475_: *mut crate::leanh::LeanObject,
    mut v_inst_2476_: *mut crate::leanh::LeanObject,
    mut v_r_2477_: *mut crate::leanh::LeanObject,
    mut v_inst_2478_: *mut crate::leanh::LeanObject,
    mut v_inst_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Std_Rii_toList(
        v_00_u03b1_2474_,
        v_inst_2475_,
        v_inst_2476_,
        v_r_2477_,
        v_inst_2478_,
        v_inst_2479_,
    );
    crate::leanh::lean_dec_ref(v_inst_2475_);
    return v_res_2480_;
}
pub unsafe fn l_Std_Rii_toArray___redArg(
    mut v_inst_2481_: *mut crate::leanh::LeanObject,
    mut v_inst_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2483_ = crate::leanh::lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2483_, 0, v_inst_2482_);
    v___x_2484_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2483_,
        v_inst_2481_,
        v___x_2484_,
    );
    return v___x_2485_;
}
pub unsafe fn l_Std_Rii_toArray(
    mut v_00_u03b1_2486_: *mut crate::leanh::LeanObject,
    mut v_inst_2487_: *mut crate::leanh::LeanObject,
    mut v_inst_2488_: *mut crate::leanh::LeanObject,
    mut v_r_2489_: *mut crate::leanh::LeanObject,
    mut v_inst_2490_: *mut crate::leanh::LeanObject,
    mut v_inst_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2492_ = crate::leanh::lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2492_, 0, v_inst_2490_);
    v___x_2493_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2494_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2492_,
        v_inst_2488_,
        v___x_2493_,
    );
    return v___x_2494_;
}
pub unsafe fn l_Std_Rii_toArray___boxed(
    mut v_00_u03b1_2495_: *mut crate::leanh::LeanObject,
    mut v_inst_2496_: *mut crate::leanh::LeanObject,
    mut v_inst_2497_: *mut crate::leanh::LeanObject,
    mut v_r_2498_: *mut crate::leanh::LeanObject,
    mut v_inst_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Std_Rii_toArray(
        v_00_u03b1_2495_,
        v_inst_2496_,
        v_inst_2497_,
        v_r_2498_,
        v_inst_2499_,
        v_inst_2500_,
    );
    crate::leanh::lean_dec_ref(v_inst_2496_);
    return v_res_2501_;
}
pub unsafe fn l_Std_Rii_size___redArg(
    mut v_inst_2502_: *mut crate::leanh::LeanObject,
    mut v_inst_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2502_) == 0 {
        let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2503_);
        v___x_2504_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2504_;
    } else {
        let mut v_val_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2505_ = crate::leanh::lean_ctor_get(v_inst_2502_, 0);
        crate::leanh::lean_inc(v_val_2505_);
        crate::leanh::lean_dec_ref_known(v_inst_2502_, 1);
        v___x_2506_ = crate::leanh::lean_apply_1(v_inst_2503_, v_val_2505_);
        return v___x_2506_;
    }
}
pub unsafe fn l_Std_Rii_size(
    mut v_00_u03b1_2507_: *mut crate::leanh::LeanObject,
    mut v_x_2508_: *mut crate::leanh::LeanObject,
    mut v_inst_2509_: *mut crate::leanh::LeanObject,
    mut v_inst_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_inst_2509_) == 0 {
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2510_);
        v___x_2511_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2511_;
    } else {
        let mut v_val_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2512_ = crate::leanh::lean_ctor_get(v_inst_2509_, 0);
        crate::leanh::lean_inc(v_val_2512_);
        crate::leanh::lean_dec_ref_known(v_inst_2509_, 1);
        v___x_2513_ = crate::leanh::lean_apply_1(v_inst_2510_, v_val_2512_);
        return v___x_2513_;
    }
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_2514_: *mut crate::leanh::LeanObject,
    mut v_inst_2515_: *mut crate::leanh::LeanObject,
    mut v_inst_2516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2517_: *mut crate::leanh::LeanObject,
    mut v_r_2518_: *mut crate::leanh::LeanObject,
    mut v_init_2519_: *mut crate::leanh::LeanObject,
    mut v_f_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2521_ = crate::leanh::lean_ctor_get(v_inst_2514_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2521_);
    if crate::leanh::lean_obj_tag(v_inst_2515_) == 0 {
        let mut v_toPure_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_2520_);
        crate::leanh::lean_dec_ref(v_inst_2516_);
        crate::leanh::lean_dec_ref(v_inst_2514_);
        v_toPure_2522_ = crate::leanh::lean_ctor_get(v_toApplicative_2521_, 1);
        crate::leanh::lean_inc(v_toPure_2522_);
        crate::leanh::lean_dec_ref(v_toApplicative_2521_);
        v___x_2523_ =
            crate::leanh::lean_apply_2(v_toPure_2522_, crate::leanh::lean_box(0), v_init_2519_);
        return v___x_2523_;
    } else {
        let mut v_toBind_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2524_ = crate::leanh::lean_ctor_get(v_inst_2514_, 1);
        crate::leanh::lean_inc(v_toBind_2524_);
        crate::leanh::lean_dec_ref(v_inst_2514_);
        v_toPure_2525_ = crate::leanh::lean_ctor_get(v_toApplicative_2521_, 1);
        crate::leanh::lean_inc_n(v_toPure_2525_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_2521_);
        v_val_2526_ = crate::leanh::lean_ctor_get(v_inst_2515_, 0);
        crate::leanh::lean_inc(v_val_2526_);
        crate::leanh::lean_dec_ref_known(v_inst_2515_, 1);
        v___f_2527_ = crate::leanh::lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_2527_, 0, v_toPure_2525_);
        v___f_2528_ = crate::leanh::lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
        crate::leanh::lean_closure_set(v___f_2528_, 0, v_toPure_2525_);
        crate::leanh::lean_closure_set(v___f_2528_, 1, v_inst_2516_);
        crate::leanh::lean_closure_set(v___f_2528_, 2, v_f_2520_);
        crate::leanh::lean_closure_set(v___f_2528_, 3, v_toBind_2524_);
        crate::leanh::lean_closure_set(v___f_2528_, 4, v___f_2527_);
        v___x_2529_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2528_,
            v_val_2526_,
            v_init_2519_,
            crate::leanh::lean_box(0),
        );
        return v___x_2529_;
    }
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2530_: *mut crate::leanh::LeanObject,
    mut v_inst_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2533_ = crate::leanh::lean_alloc_closure(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_2533_, 0, v_inst_2532_);
    crate::leanh::lean_closure_set(v___f_2533_, 1, v_inst_2531_);
    crate::leanh::lean_closure_set(v___f_2533_, 2, v_inst_2530_);
    return v___f_2533_;
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2534_: *mut crate::leanh::LeanObject,
    mut v_m_2535_: *mut crate::leanh::LeanObject,
    mut v_inst_2536_: *mut crate::leanh::LeanObject,
    mut v_inst_2537_: *mut crate::leanh::LeanObject,
    mut v_inst_2538_: *mut crate::leanh::LeanObject,
    mut v_inst_2539_: *mut crate::leanh::LeanObject,
    mut v_inst_2540_: *mut crate::leanh::LeanObject,
    mut v_inst_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2542_ = crate::leanh::lean_alloc_closure(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_2542_, 0, v_inst_2540_);
    crate::leanh::lean_closure_set(v___f_2542_, 1, v_inst_2537_);
    crate::leanh::lean_closure_set(v___f_2542_, 2, v_inst_2536_);
    return v___f_2542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Iterators(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Iterators(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Iterators(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
}
